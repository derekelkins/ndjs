import { bind, wire } from "hyperhtml/esm";
import { runEffects, tap, merge } from "@most/core";
import { click, domEvent, mouseleave, change, hashchange } from "@most/dom-event";
import { newDefaultScheduler } from "@most/scheduler";
import { Set, ValueObject, hash } from "immutable";
import { cse, expandCse } from "./json-with-sharing";
import { compressToEncodedURIComponent, decompressFromEncodedURIComponent } from "lz-string";

type Json = any;

function nullMap<A, B>(xs: Array<A>, f: (x: A) => B | null): Array<B> | null {
    const len = xs.length;
    const result = new Array<B>(len);
    for(let i = 0; i < len; ++i) {
        const y = f(xs[i]);
        if(y === null) return null;
        result[i] = y;
    }
    return result;
}

interface Equals<T> {
    equals(other: T): boolean;
}

interface Freshen<V> {
    freshen(variableContext: Set<V>): V;
}

interface ToJson {
    toJson(): Json;
}

interface Display {
    toDisplayString(topLevel: boolean): string;
}

interface LaTeX {
    toLaTeX(topLevel: boolean): string;
}

interface FreeVariables<V, T> {
    freeVariables(): Set<V>;
}

interface Substitute<V, T> extends FreeVariables<V, T> {
    // TODO: Probably want to do something to avoid recalculating free variables.
    alphaRename(oldVar: V, newVar: V): this;
    substitute(oldVar: V, term: T): this;
}

// Just for convenience
interface IVariable<V> extends Equals<V>, ToJson, Freshen<V>, Display, LaTeX {}
interface IGeneric<V extends IVariable<V>, O> extends ToJson, Substitute<V, GenericTerm<V, O>>, Display, LaTeX  {}

/* Terms ************************************************************************************************************************************************************/

const BOT_SYMBOL = '⊥';
const TOP_SYMBOL = '⊤';
const NOT_SYMBOL = '¬';
const AND_SYMBOL = '∧';
const OR_SYMBOL = '∨';
const IMP_SYMBOL = '→';
const FORALL_SYMBOL = '∀';
const EXISTS_SYMBOL = '∃';

const connectiveToLaTeX: {[conn: string]: string} = {
    [BOT_SYMBOL]: '\\bot{}',
    [TOP_SYMBOL]: '\\top{}',
    [NOT_SYMBOL]: '\\neg{}',
    [AND_SYMBOL]: '\\land{}',
    [OR_SYMBOL]: '\\lor{}',
    [IMP_SYMBOL]: '\\to{}',
    [FORALL_SYMBOL]: '\\forall{}',
    [EXISTS_SYMBOL]: '\\exists{}'
};

interface GenericTerm<V extends IVariable<V>, O> extends IGeneric<V, O>, Equals<GenericTerm<V, O>> {
    match<A>(variableCase: (v: V) => A,
             operatorCase: (operator: O, ...terms: Array<GenericTerm<V, O>>) => A): A;
    equals(other: GenericTerm<V, O>): boolean;
}

class Variable<V extends IVariable<V>, O> implements GenericTerm<V, O> {
    constructor(readonly variable: V) {}

    match<A>(variableCase: (v: V) => A, opCase: (o: O, ...ts: Array<GenericTerm<V, O>>) => A): A {
        return variableCase(this.variable);
    }

    toJson(): Json {
        return this.variable.toJson();
    }

    toDisplayString(topLevel: boolean): string { return this.variable.toDisplayString(true); }

    toLaTeX(topLevel: boolean): string { return this.variable.toLaTeX(true); }

    freeVariables(): Set<V> {
        return Set.of(this.variable);
    }

    alphaRename(oldVar: V, newVar: V): this {
        if(this.variable.equals(oldVar)) return new Variable(newVar) as this;
        return this;
    }

    substitute(oldVar: V, term: GenericTerm<V, O>): this {
        if(!this.variable.equals(oldVar)) return this;
        return term as this;
    }

    equals(other: GenericTerm<V, O>): boolean {
        return other.match(
                    v => this.variable.equals(v),
                    _ => false);
    }
}

class Operator<V extends IVariable<V>, O> implements GenericTerm<V, O> {
    readonly terms: Array<GenericTerm<V, O>>;

    constructor(readonly operator: O, ...ts: Array<GenericTerm<V, O>>) { this.terms = ts; }

    match<A>(variableCase: (v: V) => A, opCase: (o: O, ...ts: Array<GenericTerm<V, O>>) => A): A {
        return opCase(this.operator, ...this.terms);
    }

    toJson(): Json {
        return [this.operator].concat(this.terms.map(t => t.toJson()));
    }

    toDisplayString(topLevel: boolean): string { return this.operator+'('+this.terms.map(t => t.toDisplayString(true)).join(', ')+')'; }

    toLaTeX(topLevel: boolean): string { return '\\mathsf{'+this.operator+'}('+this.terms.map(t => t.toLaTeX(true)).join(', ')+')'; }

    freeVariables(): Set<V> {
        return Set.union(this.terms.map(t => t.freeVariables()));
    }

    alphaRename(oldVar: V, newVar: V): this {
        if(!this.freeVariables().has(oldVar)) return this;
        return new Operator(this.operator, ...this.terms.map(t => t.alphaRename(oldVar, newVar))) as this;
    }

    substitute(oldVar: V, term: GenericTerm<V, O>): this {
        if(!this.freeVariables().has(oldVar)) return this;
        return new Operator(this.operator, ...this.terms.map(t => t.substitute(oldVar, term))) as this;
    }

    equals(other: GenericTerm<V, O>): boolean {
        return other.match(
                    v => false,
                    (o, ...ts) => o === this.operator
                               && this.terms.length === ts.length
                               && ts.every((t, i) => t.equals(this.terms[i])));
    }
}

function varFromJson(json: Json): Var | null {
    if(typeof json !== 'string') return null;
    const components = json.split('.');
    if(components.length !== 1 && components.length !== 2) return null;
    try {
        return new Var(components[0], components[1] === void(0) ? -1 : parseInt(components[1], 10));
    } catch(SyntaxError) {
        return null;
    }
}

function termFromJson(json: Json): SimpleTerm | null {
    if(typeof json === 'string') { // Variable case
        const v = varFromJson(json);
        if(v === null) return null;
        return new Variable(v);
    }
    if(typeof json !== 'object' || json === null || !(json instanceof Array) || json.length < 1) return null;
    const terms = nullMap(json.slice(1), termFromJson);
    if(terms === null) return null;
    return new Operator(json[0], ...terms);
}

/* Formulas *********************************************************************************************************************************************************/

interface GenericFormula<V extends IVariable<V>, P, C, Q, O, T extends GenericTerm<V, O>> extends IGeneric<V, O> {
    match<A>(predicateCase: (predicate: P, ...terms: Array<T>) => A,
             nullaryCase: (connective: C) => A,
             unaryCase: (connective: C, formula: GenericFormula<V, P, C, Q, O, T>) => A,
             binaryCase: (leftFormula: GenericFormula<V, P, C, Q, O, T>, connective: C, rightFormula: GenericFormula<V, P, C, Q, O, T>) => A,
             quantifierCase: (quantifier: Q, v: V, formula: GenericFormula<V, P, C, Q, O, T>) => A): A;

    matches(predicate: P, terms: Array<T>): boolean;
}

class Predicate<V extends IVariable<V>, P, C, Q, O, T extends GenericTerm<V, O>> implements GenericFormula<V, P, C, Q, O, T> {
    readonly terms: Array<T>;

    constructor(readonly predicate: P, ...ts: Array<T>) { this.terms = ts; }

    match<A>(predicateCase: (predicate: P, ...terms: Array<T>) => A,
             nullaryCase: (connective: C) => A,
             unaryCase: (connective: C, formula: GenericFormula<V, P, C, Q, O, T>) => A,
             binaryCase: (leftFormula: GenericFormula<V, P, C, Q, O, T>, connective: C, rightFormula: GenericFormula<V, P, C, Q, O, T>) => A,
             quantifierCase: (quantifier: Q, v: V, formula: GenericFormula<V, P, C, Q, O, T>) => A): A {
        return predicateCase(this.predicate, ...this.terms);
    }

    toJson(): Json {
        return [this.predicate].concat(this.terms.map(t => t.toJson()));
    }

    toDisplayString(topLevel: boolean): string {
        return this.terms.length === 0 ? ''+this.predicate : this.predicate+'('+this.terms.map(t => t.toDisplayString(true)).join(', ')+')';
    }

    toLaTeX(topLevel: boolean): string {
        return this.terms.length === 0 ? '\\mathrm{'+this.predicate+'}' : '\\mathrm{'+this.predicate+'}('+this.terms.map(t => t.toLaTeX(true)).join(', ')+')';
    }

    freeVariables(): Set<V> {
        return Set.union(this.terms.map(t => t.freeVariables()));
    }

    alphaRename(oldVar: V, newVar: V): this {
        if(!this.freeVariables().has(oldVar)) return this;
        return new Predicate(this.predicate, ...this.terms.map(t => t.alphaRename(oldVar, newVar))) as this;
    }

    substitute(oldVar: V, term: GenericTerm<V, O>): this {
        if(!this.freeVariables().has(oldVar)) return this;
        return new Predicate(this.predicate, ...this.terms.map(t => t.substitute(oldVar, term))) as this;
    }

    matches(predicate: P, terms: Array<T>): boolean {
        return this.predicate === predicate
            && this.terms.length === terms.length
            && terms.every((t, i) => t.equals(this.terms[i]));
    }
}

class NullaryConnective<V extends IVariable<V>, P, C, Q, O, T extends GenericTerm<V, O>> implements GenericFormula<V, P, C, Q, O, T> {
    constructor(readonly connective: C) { }

    match<A>(predicateCase: (predicate: P, ...terms: Array<T>) => A,
             nullaryCase: (connective: C) => A,
             unaryCase: (connective: C, formula: GenericFormula<V, P, C, Q, O, T>) => A,
             binaryCase: (leftFormula: GenericFormula<V, P, C, Q, O, T>, connective: C, rightFormula: GenericFormula<V, P, C, Q, O, T>) => A,
             quantifierCase: (quantifier: Q, v: V, formula: GenericFormula<V, P, C, Q, O, T>) => A): A {
        return nullaryCase(this.connective);
    }

    toJson(): Json {
        return this.connective;
    }

    toDisplayString(topLevel: boolean): string { return ''+this.connective; }

    toLaTeX(topLevel: boolean): string { return connectiveToLaTeX[''+this.connective]; }

    freeVariables(): Set<V> {
        return Set();
    }

    alphaRename(oldVar: V, newVar: V): this {
        return this;
    }

    substitute(oldVar: V, term: GenericTerm<V, O>): this { return this; }

    matches(predicate: P, terms: Array<T>): boolean { return false; }
}

class UnaryConnective<V extends IVariable<V>, P, C, Q, O, T extends GenericTerm<V, O>> implements GenericFormula<V, P, C, Q, O, T> {
    constructor(readonly connective: C, readonly formula: GenericFormula<V, P, C, Q , O, T>) { }

    match<A>(predicateCase: (predicate: P, ...terms: Array<T>) => A,
             nullaryCase: (connective: C) => A,
             unaryCase: (connective: C, formula: GenericFormula<V, P, C, Q, O, T>) => A,
             binaryCase: (leftFormula: GenericFormula<V, P, C, Q, O, T>, connective: C, rightFormula: GenericFormula<V, P, C, Q, O, T>) => A,
             quantifierCase: (quantifier: Q, v: V, formula: GenericFormula<V, P, C, Q, O, T>) => A): A {
        return unaryCase(this.connective, this.formula);
    }

    toJson(): Json {
        return {c: this.connective, r: this.formula.toJson()};
    }

    toDisplayString(topLevel: boolean): string {
        if(topLevel) {
            return this.connective + this.formula.toDisplayString(false);
        } else {
            return '(' + this.connective + this.formula.toDisplayString(false) + ')';
        }
    }

    toLaTeX(topLevel: boolean): string {
        if(topLevel) {
            return connectiveToLaTeX[''+this.connective] + this.formula.toLaTeX(false);
        } else {
            return '(' + connectiveToLaTeX[''+this.connective] + this.formula.toLaTeX(false) + ')';
        }
    }

    freeVariables(): Set<V> {
        return this.formula.freeVariables();
    }

    alphaRename(oldVar: V, newVar: V): this {
        if(!this.freeVariables().has(oldVar)) return this;
        return new UnaryConnective(this.connective, this.formula.alphaRename(oldVar, newVar)) as this;
    }

    substitute(oldVar: V, term: GenericTerm<V, O>): this {
        if(!this.freeVariables().has(oldVar)) return this;
        return new UnaryConnective(this.connective, this.formula.substitute(oldVar, term)) as this;
    }

    matches(predicate: P, terms: Array<T>): boolean { return false; }
}

class BinaryConnective<V extends IVariable<V>, P, C, Q, O, T extends GenericTerm<V, O>> implements GenericFormula<V, P, C, Q, O, T> {
    constructor(readonly leftFormula: GenericFormula<V, P, C, Q, O, T>, readonly connective: C, readonly rightFormula: GenericFormula<V, P, C, Q, O, T>) { }

    match<A>(predicateCase: (predicate: P, ...terms: Array<T>) => A,
             nullaryCase: (connective: C) => A,
             unaryCase: (connective: C, formula: GenericFormula<V, P, C, Q, O, T>) => A,
             binaryCase: (leftFormula: GenericFormula<V, P, C, Q, O, T>, connective: C, rightFormula: GenericFormula<V, P, C, Q, O, T>) => A,
             quantifierCase: (quantifier: Q, v: V, formula: GenericFormula<V, P, C, Q, O, T>) => A): A {
        return binaryCase(this.leftFormula, this.connective, this.rightFormula);
    }

    toJson(): Json {
        return {c: this.connective, l: this.leftFormula.toJson(), r: this.rightFormula.toJson()};
    }

    toDisplayString(topLevel: boolean): string {
        if(topLevel) {
            return this.leftFormula.toDisplayString(false) + this.connective + this.rightFormula.toDisplayString(false);
        } else {
            return '(' + this.leftFormula.toDisplayString(false) + this.connective + this.rightFormula.toDisplayString(false) + ')';
        }
    }

    toLaTeX(topLevel: boolean): string {
        if(topLevel) {
            return this.leftFormula.toLaTeX(false) + connectiveToLaTeX[''+this.connective] + this.rightFormula.toLaTeX(false);
        } else {
            return '(' + this.leftFormula.toLaTeX(false) + connectiveToLaTeX[''+this.connective] + this.rightFormula.toLaTeX(false) + ')';
        }
    }

    freeVariables(): Set<V> {
        return this.leftFormula.freeVariables().union(this.rightFormula.freeVariables());
    }

    alphaRename(oldVar: V, newVar: V): this {
        if(!this.freeVariables().has(oldVar)) return this;
        return new BinaryConnective(this.leftFormula.alphaRename(oldVar, newVar), this.connective, this.rightFormula.alphaRename(oldVar, newVar)) as this;
    }

    substitute(oldVar: V, term: GenericTerm<V, O>): this {
        if(!this.freeVariables().has(oldVar)) return this;
        return new BinaryConnective(this.leftFormula.substitute(oldVar, term), this.connective, this.rightFormula.substitute(oldVar, term)) as this;
    }

    matches(predicate: P, terms: Array<T>): boolean { return false; }
}

class Quantifier<V extends IVariable<V>, P, C, Q, O, T extends GenericTerm<V, O>> implements GenericFormula<V, P, C, Q, O, T> {
    constructor(readonly quantifier: Q, readonly variable: V, readonly formula: GenericFormula<V, P, C, Q, O, T>) {}

    match<A>(predicateCase: (predicate: P, ...terms: Array<T>) => A,
             nullaryCase: (connective: C) => A,
             unaryCase: (connective: C, formula: GenericFormula<V, P, C, Q, O, T>) => A,
             binaryCase: (leftFormula: GenericFormula<V, P, C, Q, O, T>, connective: C, rightFormula: GenericFormula<V, P, C, Q, O, T>) => A,
             quantifierCase: (quantifier: Q, v: V, formula: GenericFormula<V, P, C, Q, O, T>) => A): A {
        return quantifierCase(this.quantifier, this.variable, this.formula);
    }

    toJson(): Json {
        return {q: this.quantifier, v: this.variable.toJson(), f: this.formula.toJson()};
    }

    toDisplayString(topLevel: boolean): string {
        if(topLevel) {
            return this.quantifier + this.variable.toDisplayString(false) + '.' + this.formula.toDisplayString(false);
        } else {
            return '(' + this.quantifier + this.variable.toDisplayString(false) + '.' + this.formula.toDisplayString(true) + ')';
        }
    }

    toLaTeX(topLevel: boolean): string {
        if(topLevel) {
            return connectiveToLaTeX[''+this.quantifier] + this.variable.toLaTeX(false) + '.' + this.formula.toLaTeX(false);
        } else {
            return '(' + connectiveToLaTeX[''+this.quantifier] + this.variable.toLaTeX(false) + '.' + this.formula.toLaTeX(true) + ')';
        }
    }

    freeVariables(): Set<V> {
        return this.formula.freeVariables().delete(this.variable);
    }

    alphaRename(oldVar: V, newVar: V): this {
        if(!this.freeVariables().has(oldVar)) return this;
        return new Quantifier(this.quantifier, this.variable, this.formula.alphaRename(oldVar, newVar)) as this;
    }

    substitute(oldVar: V, term: GenericTerm<V, O>): this {
        if(!this.freeVariables().has(oldVar)) return this;
        const variableContext = term.freeVariables();
        if(variableContext.has(this.variable)) {
            const fresh = this.variable.freshen(variableContext);
            return new Quantifier(this.quantifier, fresh, this.formula.alphaRename(this.variable, fresh).substitute(oldVar, term)) as this;
        } else {
            return new Quantifier(this.quantifier, this.variable, this.formula.substitute(oldVar, term)) as this;
        }
    }

    matches(predicate: P, terms: Array<T>): boolean { return false; }
}

function formulaFromJson(json: Json): SimpleFormula | null {
    if(typeof json === 'string') return new NullaryConnective(json);
    if(typeof json !== 'object' || json === null) return null;
    if(json instanceof Array) { // Predicate case
        if(json.length < 1) return null;
        const terms = nullMap(json.slice(1), termFromJson);
        if(terms === null) return null;
        return new Predicate(json[0], ...terms);
    }
    if('q' in json) { // Quantifier case
        const q = json.q;
        if(typeof q !== 'string') return null;
        const v = varFromJson(json.v);
        if(v === null) return null;
        const f = formulaFromJson(json.f);
        if(f === null) return null;
        return new Quantifier(q, v, f);
    } else if('l' in json) { // Binary connective case
        const c = json.c;
        if(typeof c !== 'string') return null;
        const r = formulaFromJson(json.r);
        if(r === null) return null;
        const l = formulaFromJson(json.l);
        if(l === null) return null;
        return new BinaryConnective(l, c, r);
    } else { // Unary Connective case
        const c = json.c;
        if(typeof c !== 'string') return null;
        const r = formulaFromJson(json.r);
        if(r === null) return null;
        return new UnaryConnective(c, r);
    }
}

/* Goals ************************************************************************************************************************************************************/

interface GenericGoal<V extends IVariable<V>, O, F extends ToJson & Display & LaTeX & FreeVariables<V, GenericTerm<V, O>>> extends ToJson, Display, LaTeX, FreeVariables<V, GenericTerm<V, O>> {
    match<A>(f: (premises: Array<F>, consequences: Array<F>) => A): A;
    readonly premises: Array<F>;
    readonly consequences: Array<F>;
}

class Goal<V extends IVariable<V>, O, F extends ToJson & Display & LaTeX & FreeVariables<V, GenericTerm<V, O>>> implements GenericGoal<V, O, F> {
    constructor(readonly premises: Array<F>, readonly consequences: Array<F>) {}

    match<A>(f: (premises: Array<F>, consequences: Array<F>) => A): A {
        return f(this.premises, this.consequences);
    }

    freeVariables(): Set<V> {
        return Set.union(this.premises.map(p => p.freeVariables()).concat(this.consequences.map(c => c.freeVariables())));
    }

    toDisplayString(topLevel: boolean): string {
        return this.premises.map(p => p.toDisplayString(true)).join(', ') + ' ⊢ ' + this.consequences.map(c => c.toDisplayString(true)).join(', ');
    }

    toLaTeX(topLevel: boolean): string {
        return this.premises.map(p => p.toLaTeX(true)).join(', ') + '\\vdash ' + this.consequences.map(c => c.toLaTeX(true)).join(', ');
    }

    toJson(): Json {
        return [this.premises.map(p => p.toJson()), this.consequences.map(c => c.toJson())];
    }
}

function goalFromJson(json: Json): SimpleGoal | null {
    if(typeof json !== 'object' || json === null || !(json instanceof Array) || json.length !== 2) return null;
    if(!(json[0] instanceof Array && json[1] instanceof Array)) return null;
    const premises = nullMap(json[0], formulaFromJson);
    if(premises === null) return null;
    const consequences = nullMap(json[1], formulaFromJson);
    if(consequences === null) return null;
    return new Goal(premises, consequences);
}

/* Lexer ************************************************************************************************************************************************************/

type TokenType = 'NAME' | 'LPAREN' | 'RPAREN' | 'COMMA' | 'PERIOD' | 'TURNSTILE' | 'BOTTOM' | 'TOP' | 'NOT' | 'AND' | 'OR' | 'IMPLIES' | 'FORALL' | 'EXISTS';
type Token = [TokenType, string];

export class Lexer {
    static readonly NAME_TOKEN = 'NAME';
    static readonly LPAREN_TOKEN = 'LPAREN';
    static readonly RPAREN_TOKEN = 'RPAREN';
    static readonly COMMA_TOKEN = 'COMMA';
    static readonly PERIOD_TOKEN = 'PERIOD';
    static readonly TURNSTILE_TOKEN = 'TURNSTILE';
    static readonly BOT_TOKEN = 'BOTTOM';
    static readonly TOP_TOKEN = 'TOP';
    static readonly NOT_TOKEN = 'NOT';
    static readonly AND_TOKEN = 'AND';
    static readonly OR_TOKEN = 'OR';
    static readonly IMP_TOKEN = 'IMPLIES';
    static readonly FORALL_TOKEN = 'FORALL';
    static readonly EXISTS_TOKEN = 'EXISTS';

    private static readonly lexTable = {
        [Lexer.NAME_TOKEN]: /^\s*([a-zA-Z][a-zA-Z0-9]*(_[0-9]+)?)/giu,
        [Lexer.LPAREN_TOKEN]: /^\s*(\()/giu,
        [Lexer.RPAREN_TOKEN]: /^\s*(\))/giu,
        [Lexer.COMMA_TOKEN]: /^\s*(,)/giu,
        [Lexer.PERIOD_TOKEN]: /^\s*(\.)/giu,
        [Lexer.TURNSTILE_TOKEN]: /^\s*(\|-|⊢)/giu,
        [Lexer.BOT_TOKEN]: /^\s*(false|_\|_|⊥)/giu,
        [Lexer.TOP_TOKEN]: /^\s*(true|⊤)/giu, // TODO: ASCII version?
        [Lexer.NOT_TOKEN]: /^\s*(~|¬)/giu,
        [Lexer.AND_TOKEN]: /^\s*(\/\\|∧)/giu,
        [Lexer.OR_TOKEN]: /^\s*(\\\/|∨)/giu,
        [Lexer.IMP_TOKEN]: /^\s*(->|=>|⇒|→)/giu,
        [Lexer.FORALL_TOKEN]: /^\s*(forall|∀)/giu,
        [Lexer.EXISTS_TOKEN]: /^\s*(exists|∃)/giu
    };

    private static readonly spaceRegExp = /^\s*$/gu;

    private position: number = 0;
    private buffer: Token | null = null;

    peek(): Token | null {
        return this.buffer;
    }

    next(): Token | 'done' | 'error' {
        const result = this.innerNext();
        this.buffer = result === 'done' || result === 'error' ? null : result;
        return result;
    }

    private innerNext(): Token | 'done' | 'error' {
        const nameRE = Lexer.lexTable[Lexer.NAME_TOKEN];
        const input = this.inputString.slice(this.position);
        nameRE.lastIndex = 0;
        const nameResult = nameRE.exec(input);
        if(nameResult !== null) {
            this.position += nameRE.lastIndex;
            const s = nameResult[1];
            if(/^forall$/i.test(s)) return [Lexer.FORALL_TOKEN, s];
            if(/^exists$/i.test(s)) return [Lexer.EXISTS_TOKEN, s];
            if(/^true/i.test(s)) return [Lexer.TOP_TOKEN, s];
            if(/^false/i.test(s)) return [Lexer.BOT_TOKEN, s];
            return [Lexer.NAME_TOKEN, s];
        } else {
            for(const reName in Lexer.lexTable) {
                if(reName === Lexer.NAME_TOKEN) continue;
                const re = Lexer.lexTable[reName as TokenType];
                re.lastIndex = 0;
                const result = re.exec(input);
                if(result === null) continue;
                this.position += re.lastIndex;
                return [reName as TokenType, result[1]];
            }
            Lexer.spaceRegExp.lastIndex = 0;
            return Lexer.spaceRegExp.test(input) ? 'done' : 'error';
        }
    }

    constructor(private readonly inputString: string) { this.next(); }
}

/* Parser ***********************************************************************************************************************************************************/

// TODO: Improve parser to handle conventional precedence rules.
// TODO: Improve error messages.

function parseVariable(v: string): Var | null {
    const components = v.split('_');
    if(components.length !== 1 && components.length !== 2) return null;
    try {
        return new Var(components[0], components[1] === void(0) ? -1 : parseInt(components[1], 10));
    } catch(SyntaxError) {
        return null;
    }
}

/*
   Term ::= NAME (LPAREN TermList RPAREN)?
   TermList ::= Term (COMMA Term)*
 */
function parseTerm(lexer: Lexer): SimpleTerm | null {
    const nameToken = lexer.peek();
    if(nameToken === null || nameToken[0] !== Lexer.NAME_TOKEN) return null;
    const lparenToken = lexer.next();
    if(lparenToken === 'error') return null;
    if(lparenToken === 'done' || lparenToken[0] !== Lexer.LPAREN_TOKEN) {
        const v = parseVariable(nameToken[1]);
        if(v === null) return null;
        return new Variable(v);
    }
    lexer.next();
    const terms = parseTermList(lexer);
    if(terms === null) return null;
    const rparenToken = lexer.peek();
    if(rparenToken === null || rparenToken[0] !== Lexer.RPAREN_TOKEN) return null;
    lexer.next();
    return new Operator(nameToken[1], ...terms);
}

function parseTermList(lexer: Lexer): Array<SimpleTerm> | null {
    const firstTerm = parseTerm(lexer);
    if(firstTerm === null) return [];
    const terms = [firstTerm];
    while(true) {
        const commaToken = lexer.peek();
        if(commaToken === null || commaToken[0] !== Lexer.COMMA_TOKEN) return terms;
        lexer.next();
        const nextTerm = parseTerm(lexer);
        if(nextTerm === null) return null;
        terms.push(nextTerm);
    }
}

function termFromString(s: string): SimpleTerm | null {
    const lexer = new Lexer(s);
    const term = parseTerm(lexer);
    if(lexer.peek() !== null) return null; // we aren't at the end of the string
    return term;
}

/*
   NullaryConnective ::= TOP | BOTTOM
   UnaryConnective ::= NOT
   BinaryConnective ::= AND | OR | IMP
   Quantifier ::= FORALL | EXISTS
   AtomicFormula ::= NAME (LPAREN TermList RPAREN)?
   | NullaryConnective
   | LPAREN Formula RPAREN
   Formula ::= AtamicFormula FormulaTail
   | UnaryConnective AtomicFormula
   | Quantifier NAME PERIOD AtomicFormula
   FormulaTail ::= BinaryConnective AtomicFormula
   | EMPTY
 */
const nullaryConnectives: {[token: string]: string | undefined} = {
    [Lexer.TOP_TOKEN]: TOP_SYMBOL,
    [Lexer.BOT_TOKEN]: BOT_SYMBOL
};
const unaryConnectives: {[token: string]: string | undefined} = {
    [Lexer.NOT_TOKEN]: NOT_SYMBOL
};
const binaryConnectives: {[token: string]: string | undefined} = {
    [Lexer.AND_TOKEN]: AND_SYMBOL,
    [Lexer.OR_TOKEN]: OR_SYMBOL,
    [Lexer.IMP_TOKEN]: IMP_SYMBOL
};
const quantifiers: {[token: string]: string | undefined} = {
    [Lexer.FORALL_TOKEN]: FORALL_SYMBOL,
    [Lexer.EXISTS_TOKEN]: EXISTS_SYMBOL
};


function parseFormula(lexer: Lexer): SimpleFormula | null {
    const leadToken = lexer.peek();
    if(leadToken === null) return null;
    const tokenType = leadToken[0];
    if(unaryConnectives[tokenType] !== void(0)) {
        lexer.next();
        const f = parseAtomicFormula(lexer);
        if(f === null) return null;
        return new UnaryConnective(unaryConnectives[tokenType] as string, f);
    } else if(quantifiers[tokenType] !== void(0)) {
        const nameToken = lexer.next();
        if(nameToken === 'done' || nameToken === 'error' || nameToken[0] !== Lexer.NAME_TOKEN) return null;
        const periodToken = lexer.next();
        if(periodToken === 'done' || periodToken === 'error' || periodToken[0] !== Lexer.PERIOD_TOKEN) return null;
        lexer.next();
        const formula = parseAtomicFormula(lexer);
        if(formula === null) return null;
        const v = parseVariable(nameToken[1]);
        if(v === null) return null;
        return new Quantifier(quantifiers[tokenType] as string, v, formula);
    } else {
        const lf = parseAtomicFormula(lexer);
        if(lf === null) return null;
        const rf = parseFormulaTail(lexer);
        if(rf === null) return lf;
        const conn = binaryConnectives[rf[0]];
        if(conn === void(0)) return null;
        return new BinaryConnective(lf, conn, rf[1]);
    }
}

function parseAtomicFormula(lexer: Lexer): SimpleFormula | null {
    const leadToken = lexer.peek();
    if(leadToken === null) return null;
    const tokenType = leadToken[0];
    if(nullaryConnectives[tokenType] !== void(0)) {
        lexer.next();
        return new NullaryConnective(nullaryConnectives[tokenType] as string);
    } else {
        switch(tokenType) {
            case Lexer.NAME_TOKEN:
                const lparenToken = lexer.next();
                if(lparenToken === 'error') return null;
                if(lparenToken === 'done' || lparenToken[0] !== Lexer.LPAREN_TOKEN) return new Predicate(leadToken[1]);
                lexer.next();
                const terms = parseTermList(lexer);
                if(terms === null) return null;
                const rparenToken = lexer.peek();
                if(rparenToken === null || rparenToken[0] !== Lexer.RPAREN_TOKEN) return null;
                lexer.next();
                return new Predicate(leadToken[1], ...terms);
            case Lexer.LPAREN_TOKEN:
                lexer.next();
                const formula = parseFormula(lexer);
                if(formula === null) return null;
                const rparenToken2 = lexer.peek();
                if(rparenToken2 === null || rparenToken2[0] !== Lexer.RPAREN_TOKEN) return null;
                lexer.next();
                return formula;
            default:
                return null;
        }
    }
}

function parseFormulaTail(lexer: Lexer): [string, SimpleFormula] | null {
    const bc = lexer.peek();
    if(bc === null || (bc[0] !== Lexer.AND_TOKEN && bc[0] !== Lexer.OR_TOKEN && bc[0] !== Lexer.IMP_TOKEN)) return null;
    lexer.next();
    const rf = parseAtomicFormula(lexer);
    if(rf === null) return null;
    return [bc[0], rf];
}

function formulaFromString(s: string): SimpleFormula | null {
    const lexer = new Lexer(s);
    const formula = parseFormula(lexer);
    if(lexer.peek() !== null) return null; // we aren't at the end of the string
    return formula;
}

/*
   Goal ::= FormulaList TURNSTILE FormulaList
   FormulaList ::= Formula (COMMA Formula)*
 */
function parseGoal(lexer: Lexer, lax: boolean = true): SimpleGoal | null {
    const premises = parseFormulaList(lexer);
    if(premises === null) return null;
    const turnstileToken = lexer.peek();
    if(turnstileToken === null || turnstileToken[0] !== Lexer.TURNSTILE_TOKEN) {
        if(lax && premises.length === 1) { // A single formula which we'll treat as the conclusion to prove.
            return new Goal([], premises);
        } else {
            return null;
        }
    }
    lexer.next();
    const consequences = parseFormulaList(lexer);
    if(consequences === null) return null;
    return new Goal(premises, consequences);
}

function parseFormulaList(lexer: Lexer): Array<SimpleFormula> | null {
    const firstFormula = parseFormula(lexer);
    if(firstFormula === null) return [];
    const formulas = [firstFormula];
    while(true) {
        const commaToken = lexer.peek();
        if(commaToken === null || commaToken[0] !== Lexer.COMMA_TOKEN) return formulas;
        lexer.next();
        const nextFormula = parseFormula(lexer);
        if(nextFormula === null) return null;
        formulas.push(nextFormula);
    }
}

function goalFromString(s: string, lax: boolean = true): SimpleGoal | null {
    const lexer = new Lexer(s);
    const goal = parseGoal(lexer, lax);
    if(lexer.peek() !== null) return null; // we aren't at the end of the string
    return goal;
}

/* Derivations ******************************************************************************************************************************************************/

interface GenericDerivation<G extends ToJson & LaTeX> extends ToJson, LaTeX {
    match<A>(openCase: (conclusion: G) => A, inferenceCase: (name: string, premises: Array<GenericDerivation<G>>, conclusion: G) => A): A;
    conclusion: G;
    isCompleted(): boolean;
}

class OpenDerivation<G extends ToJson & LaTeX> implements GenericDerivation<G> {
    constructor(readonly conclusion:  G) {}

    match<A>(openCase: (conclusion: G) => A, inferenceCase: (name: string, premises: Array<GenericDerivation<G>>, conclusion: G) => A): A {
        return openCase(this.conclusion);
    }

    toJson(): Json {
        return {c: this.conclusion.toJson()};
    }

    toLaTeX(topLevel: boolean): string {
        return this.conclusion.toLaTeX(true);
    }

    isCompleted(): boolean { return false; }
}

class Inference<G extends ToJson & LaTeX> implements GenericDerivation<G> {
    constructor(readonly name: string, readonly premises: Array<GenericDerivation<G>>, readonly conclusion: G) {}

    match<A>(openCase: (conclusion: G) => A, inferenceCase: (name: string, premises: Array<GenericDerivation<G>>, conclusion: G) => A): A {
        return inferenceCase(this.name, this.premises, this.conclusion);
    }

    toJson(): Json {
        return {n: this.name, c: this.conclusion.toJson(), p: this.premises.map(p => p.toJson())};                     
    }

    toLaTeX(topLevel: boolean): string {
        return '\\dfrac{'+this.premises.map(p => p.toLaTeX(true)).join('\\qquad ')+'}{'+this.conclusion.toLaTeX(true)+'}\\rlap{('+this.name+')}';
    }

    isCompleted(): boolean { return this.premises.every(p => p.isCompleted()); }
}

function derivationFromJson(json: Json): SimpleDerivation | null {
    if(typeof json !== 'object' || json === null || !('c' in json)) return null;
    const conclusion = goalFromJson(json.c);
    if(conclusion === null) return null;
    if('n' in json) { // Inference case
        const name = json.n;
        if(typeof name !== 'string') return null;
        const p = json.p;
        if(typeof p !== 'object' || p === null || !(p instanceof Array)) return null;
        const premises = nullMap(p, derivationFromJson);
        if(premises === null) return null;
        return new Inference(name, premises, conclusion);
    } else { // Open case
        return new OpenDerivation(conclusion);
    }
}

/* Path *************************************************************************************************************************************************************/

interface Path {
    extend(branch: number): Path;
    toString(): string;
}

class StartPath implements Path {
    private readonly start: string;
    constructor(s: string) { this.start = ':'+s; }
    extend(branch: number): Path {
        return new ExtendPath(branch, this);
    }
    toString(branches: Array<number> = []): string { return this.start + branches.map(b => b.toString()).join('.'); }
}

class ExtendPath implements Path {
    constructor(private readonly branch: number, private readonly prev: StartPath | ExtendPath) {}
    extend(branch: number): Path {
        return new ExtendPath(branch, this);
    }
    toString(branches: Array<number> = []): string {
        branches.push(this.branch);
        return this.prev.toString(branches);
    }
}

/* DerivationExtender ***********************************************************************************************************************************************/

interface DerivationExtender {
    extend(name: string, premises: Array<SimpleDerivation>): SimpleDerivation;
    open(): SimpleDerivation;
    goal: SimpleGoal;
}

class GoalExtender implements DerivationExtender {
    constructor(readonly goal: SimpleGoal) {}

    extend(name: string, premises: Array<SimpleDerivation>): SimpleDerivation { return new Inference(name, premises, this.goal); }

    open(): SimpleDerivation { return new OpenDerivation(this.goal); }
}

class InferenceExtender implements DerivationExtender {
    constructor(
        private readonly name: string,
        private readonly left: Array<SimpleDerivation>,
        readonly goal: SimpleGoal,
        private readonly right: Array<SimpleDerivation>,
        private readonly extender: DerivationExtender) {}

    extend(name: string, premises: Array<SimpleDerivation>): SimpleDerivation {
        return this.extender.extend(this.name, this.left.concat(new Inference(name, premises, this.goal), this.right));
    }

    open(): SimpleDerivation {
        return this.extender.extend(this.name, this.left.concat(new OpenDerivation(this.goal), this.right));
    }
}

/* Rendering ********************************************************************************************************************************************************/

class Var implements ValueObject, IVariable<Var> {
    constructor(readonly name: string, readonly subscript: number = -1) {}

    equals(other: Var): boolean {
        return this.name === other.name && this.subscript === other.subscript;
    }

    toJson(): Json {
        return this.subscript === -1 ? this.name : this.name+'.'+this.subscript;
    }

    toDisplayString(): string { return this.subscript === -1 ? this.name : this.name + '_' + this.subscript; }

    toLaTeX(): string { return this.subscript === -1 ? this.name : this.name + '_{' + this.subscript + '}'; }

    hashCode(): number {
        return (hash(this.name) + hash(this.subscript)) | 0;
    }

    freshen(variableContext: Set<Var>): Var {
        // TODO: Could probably be smarter than this...
        let sub = this.subscript + 1;
        let v = new Var(this.name, sub);
        while(variableContext.has(v)) {
            v = new Var(this.name, ++sub);
        }
        return v;
    }
}

type SimpleTerm = GenericTerm<Var, string>;
type SimpleFormula = GenericFormula<Var, string, string, string, string, SimpleTerm>;
type SimpleGoal = GenericGoal<Var, string, SimpleFormula>;
type SimpleDerivation = GenericDerivation<SimpleGoal>;

function renderTerm(t: SimpleTerm): Element {
    return t.match(
            v => wire()`<span class="occurrence">${v.name}${v.subscript !== -1 ? [wire()`<sub>${v.subscript}</sub>`] : []}</span>`,
            (o, ...ts) => wire()`<span class="operator">${o}</span>(${
                ts.flatMap((t, i) => i+1 === ts.length ? [renderTerm(t)] : [renderTerm(t), wire()`, `])
                })`);
}

// TODO: Add precedence system.
function renderFormula(f: SimpleFormula, path: Path, inPremises: boolean, extraClasses: string, extender?: DerivationExtender): Element {
    const id = path.toString();
    if(extender !== void(0)) {
        const extraData = {extender: extender, formula: f, inPremises: inPremises};
        return f.match(
                (p, ...ts) => wire(f, id)`<div id="${id}" data=${extraData} class="${'formula active '+extraClasses}"><!--
                --><span class="predicate"><span class="predicateSymbol">${p}</span>${ts.length === 0 ? '' : '('}${
                    ts.flatMap((t, i) => i+1 === ts.length ? [renderTerm(t)]
                                                           : [renderTerm(t), wire()`, `])
                }${ts.length === 0 ? '' : ')'}</span></div>`,
                c => wire(f, id)`<div id="${id}" data=${extraData} class="${'formula active '+extraClasses}"><span class="connective nullary">${c}</span></div>`,
                (c, f) => wire(f, id)`<div id="${id}" data=${extraData} class="${'formula active '+extraClasses}"><!--
                --><span class="connective unary">${c}</span>${
                    renderFormula(f, path.extend(1), inPremises, '')
                }</div>`,
                (lf, c, rf) => wire(f, id)`<div id="${id}" data=${extraData} class="${'formula active '+extraClasses}">${
                    renderFormula(lf, path.extend(1), inPremises, 'left')
                }<span class="connective binary">${c}</span>${
                    renderFormula(rf, path.extend(2), inPremises, 'right')
                }</div>`,
                (q, v, f) => wire(f, id)`<div id="${id}" data=${extraData} class="${'formula active quantifier '+extraClasses}"><!--
                --><span class="connective quantifier">${q}</span><!--
                --><span class="boundVariable">${v.name}${v.subscript !== -1 ? [wire()`<sub>${v.subscript}</sub>`] : []}</span><!--
                --><span class="quantifierSeparator">.</span>${
                    renderFormula(f, path.extend(1), inPremises, '')
                }</div>`);
    } else {
        return f.match(
                (p, ...ts) => wire(f, id)`<div id="${id}" class="${'formula '+extraClasses}"><!--
                --><span class="predicate"><span class="predicateSymbol">${p}</span>${ts.length === 0 ? '' : '('}${
                    ts.flatMap((t, i) => i+1 === ts.length ? [renderTerm(t)]
                                                           : [renderTerm(t), wire()`, `])
                }${ts.length === 0 ? '' : ')'}</span></div>`,
                c => wire(f, id)`<div id="${id}" class="${'formula '+extraClasses}"><span class="connective nullary">${c}</span></div>`,
                (c, f) => wire(f, id)`<div id="${id}" class="${'formula '+extraClasses}">(<!--
                    --><span class="connective unary">${c}</span>${
                        renderFormula(f, path.extend(1), inPremises, '')
                    })</div>`,
                (lf, c, rf) => wire(f, id)`<div id="${id}" class="${'formula '+extraClasses}">(${
                        renderFormula(lf, path.extend(1), inPremises, '')
                    }<span class="connective binary">${c}</span>${
                        renderFormula(rf, path.extend(2), inPremises, '')
                    })</div>`,
                (q, v, f) => wire(f, id)`<div id="${id}" class="${'formula quantifier '+extraClasses}">(<!--
                    --><span class="connective quantifier">${q}</span><!--
                    --><span class="boundVariable">${v.name}${v.subscript !== -1 ? [wire()`<sub>${v.subscript}</sub>`] : []}</span><!--
                    --><span class="quantifierSeparator">.</span>${
                        renderFormula(f, path.extend(1), inPremises, '')
                    })</div>`);
    }
}

function renderGoal(g: SimpleGoal, path: Path, extender: DerivationExtender): Element {
    const id = path.toString();
    return g.match((ps, cs) => {
            const psLen = ps.length;
            const psLenm1 = psLen - 1;
            const csLenm1 = cs.length - 1;
            return wire(g, id)`<div id="${id}" class="goal">${
            wire(ps, id)`<div id="${id+"premises"}" class="premises context">${
                ps.flatMap((p, i) => i === psLenm1 ? [renderFormula(p, path.extend(i), true, 'topLevel', extender)]
                                                   : [renderFormula(p, path.extend(i), true, 'topLevel', extender), wire()`, `])
            }</div>`
            }<span class="turnstile" title="reset" data=${{extender: extender}}>⊢</span>${ // TODO: Only show title text for active elements.
            wire(cs, id)`<div id="${id+"consequences"}" class="consequences context">${
                cs.flatMap((c, i) => i === csLenm1 ? [renderFormula(c, path.extend(i+psLen), false, 'topLevel', extender)]
                                                   : [renderFormula(c, path.extend(i+psLen), false, 'topLevel', extender), wire()`, `])
            }</div>`
            }</div>`
            });
}

function renderDerivation(d: SimpleDerivation, path: Path, extender: DerivationExtender, first: boolean = true, root: boolean = false): Element {
    const id = path.toString();
    const classes = (first ? 'derivation first' : 'derivation') + (root && d.isCompleted() ? ' completed' : '');
    return d.match(
            c => wire(d, id)`<div id="${id}" class="${classes + ' open'}">${renderGoal(c, path/*TODO:extend(0)*/, extender)}</div>`,
            (n, ps, c) =>
            wire(d, id)`<div id="${id}" class="${classes + ' closed'}"><!--
            --><div class="row rulePremise">${
                ps.map((p, i) => {
                    const newExtender = new InferenceExtender(
                        n,
                        ps.slice(0, i),
                        p.conclusion,
                        ps.slice(i+1),
                        extender);
                    return renderDerivation(p, path.extend(i), newExtender, i === 0);
                })
            }</div><!--
            --><div class="tag" title="${renderTagTitle(n)}">${n}</div><!--
            --><div class="row ruleConclusion">${
                renderGoal(c, path.extend(ps.length), extender)
            }</div></div>`);
}

const tagNameToDescription: {[name: string]: string} = {
    "Ax": "axiom",
    "⊤L": "top left",
    "⊤R": "top right",
    "⊥L": "bottom left (ex falso quodlibet, principle of explosion)",
    "⊥R": "bottom right",
    "¬L": "left negation (resolution)",
    "¬R": "right negation (negation introduction)",
    "∧L": "left conjuction",
    "∧R": "right conjuction",
    "∨L": "left disjunction",
    "∨R": "right disjunction",
    "⇒L": "left implication (material implication)",
    "⇒R": "right implication (detachment)",
    "∀L": "left univers (universal instantiation)",
    "∀R": "right universal (universal generalization)",
    "∃L": "left existential",
    "∃R": "right existential (existential instantiation)",
    "CL": "left contraction",
    "CR": "right contraction"
};

function renderTagTitle(name: string): string {
    return tagNameToDescription[name] || '';
}

/* Helpers **********************************************************************************************************************************************************/

const bot: SimpleFormula = new NullaryConnective<Var, string, string, string, string, SimpleTerm>(BOT_SYMBOL);
const top: SimpleFormula = new NullaryConnective<Var, string, string, string, string, SimpleTerm>(TOP_SYMBOL);

function variable(v: Var): SimpleTerm {
    return new Variable<Var, string>(v);
}

function predicate(p: string, ...ts: Array<SimpleTerm>): SimpleFormula {
    return new Predicate<Var, string, string, string, string, SimpleTerm>(p, ...ts);
}

function not(f: SimpleFormula): SimpleFormula {
    return new UnaryConnective<Var, string, string, string, string, SimpleTerm>(NOT_SYMBOL, f);
}

function and(lf: SimpleFormula, rf: SimpleFormula): SimpleFormula {
    return new BinaryConnective<Var, string, string, string, string, SimpleTerm>(lf, AND_SYMBOL, rf);
}

function or(lf: SimpleFormula, rf: SimpleFormula): SimpleFormula {
    return new BinaryConnective<Var, string, string, string, string, SimpleTerm>(lf, OR_SYMBOL, rf);
}

function implies(lf: SimpleFormula, rf: SimpleFormula): SimpleFormula {
    return new BinaryConnective<Var, string, string, string, string, SimpleTerm>(lf, IMP_SYMBOL, rf);
}

function forall(v: Var, f: SimpleFormula): SimpleFormula {
    return new Quantifier<Var, string, string, string, string, SimpleTerm>(FORALL_SYMBOL, v, f);
}

function exists(v: Var, f: SimpleFormula): SimpleFormula {
    return new Quantifier<Var, string, string, string, string, SimpleTerm>(EXISTS_SYMBOL, v, f);
}

function open(conclusion: SimpleGoal): SimpleDerivation { return new OpenDerivation<SimpleGoal>(conclusion); }

function entails(premises: Array<SimpleFormula>, consequences: Array<SimpleFormula>): Goal<Var, string, SimpleFormula> {
    return new Goal<Var, string, SimpleFormula>(premises, consequences);
}

function infers(name: string, premises: Array<SimpleDerivation>, conclusion: SimpleGoal): Inference<SimpleGoal> {
    return new Inference<SimpleGoal>(name, premises, conclusion);
}

/* Events ***********************************************************************************************************************************************************/

interface InputEvent {
    match<A>(applyTacticCase: (goal: SimpleGoal, formula: SimpleFormula, inPremises: boolean, leftRight?: boolean) => A,
             contractCase: (goal: SimpleGoal, formula: SimpleFormula, inPremises: boolean) => A,
             instantiateCase: (goal: SimpleGoal, formula: SimpleFormula, inPremises: boolean, term: SimpleTerm) => A): A;
}

class ApplyTactic implements InputEvent {
    constructor(readonly goal: SimpleGoal, readonly formula: SimpleFormula, readonly inPremises: boolean, readonly leftRight?: boolean) {}

    match<A>(applyTacticCase: (goal: SimpleGoal, formula: SimpleFormula, inPremises: boolean, leftRight?: boolean) => A,
             contractCase: (goal: SimpleGoal, formula: SimpleFormula, inPremises: boolean) => A,
             instantiateCase: (goal: SimpleGoal, formula: SimpleFormula, inPremises: boolean, term: SimpleTerm) => A): A {
        return applyTacticCase(this.goal, this.formula, this.inPremises, this.leftRight);
    }
}

class Contract implements InputEvent {
    constructor(readonly goal: SimpleGoal, readonly formula: SimpleFormula, readonly inPremises: boolean) {}

    match<A>(applyTacticCase: (goal: SimpleGoal, formula: SimpleFormula, inPremises: boolean, leftRight?: boolean) => A,
             contractCase: (goal: SimpleGoal, formula: SimpleFormula, inPremises: boolean) => A,
             instantiateCase: (goal: SimpleGoal, formula: SimpleFormula, inPremises: boolean, term: SimpleTerm) => A): A {
        return contractCase(this.goal, this.formula, this.inPremises);
    }
}

class Instantiate implements InputEvent {
    constructor(readonly goal: SimpleGoal, readonly formula: SimpleFormula, readonly inPremises: boolean, readonly term: SimpleTerm) {}

    match<A>(applyTacticCase: (goal: SimpleGoal, formula: SimpleFormula, inPremises: boolean, leftRight?: boolean) => A,
             contractCase: (goal: SimpleGoal, formula: SimpleFormula, inPremises: boolean) => A,
             instantiateCase: (goal: SimpleGoal, formula: SimpleFormula, inPremises: boolean, term: SimpleTerm) => A): A {
        return instantiateCase(this.goal, this.formula, this.inPremises, this.term);
    }
}

interface OutputEvent {
    match<A>(failedCase: (message: string) => A,
             newGoalsCase: (name: string, goals: Array<SimpleGoal>) => A,
             contractOrInstantiateCase: (goal: SimpleGoal, formula: SimpleFormula, inPremises: boolean) => A): A;
}

class Failed implements OutputEvent {
    constructor(readonly message: string) {}

    match<A>(failedCase: (message: string) => A,
             newGoalsCase: (name: string, goals: Array<SimpleGoal>) => A,
             contractOrInstantiateCase: (goal: SimpleGoal, formula: SimpleFormula, inPremises: boolean) => A): A {
        return failedCase(this.message);
    }
}

class NewGoals implements OutputEvent {
    constructor(readonly name: string, readonly goals: Array<SimpleGoal>) {}
    match<A>(failedCase: (message: string) => A,
             newGoalsCase: (name: string, goals: Array<SimpleGoal>) => A,
             contractOrInstantiateCase: (goal: SimpleGoal, formula: SimpleFormula, inPremises: boolean) => A): A {
        return newGoalsCase(this.name, this.goals);
    }
}

class ContractOrInstantiate implements OutputEvent {
    constructor(readonly goal: SimpleGoal, readonly formula: SimpleFormula, readonly inPremises: boolean) {}
    match<A>(failedCase: (message: string) => A,
             newGoalsCase: (name: string, goals: Array<SimpleGoal>) => A,
             contractOrInstantiateCase: (goal: SimpleGoal, formula: SimpleFormula, inPremises: boolean) => A): A {
        return contractOrInstantiateCase(this.goal, this.formula, this.inPremises);
    }
}

/* Intuitionisticc Logic *********************************************************************************************************************************************/

type Logic = (input: InputEvent) => OutputEvent;

// Use LJT, the system used by Logitext and Djinn and described in "Contraction-Free Sequent Calculi for Intuitionistic Logic", to handle intuitionistic logic.
// Look at LJF from "Focusing and Polarization in Intuitionistic Logic" which contains LJT as a subsystem. This may better organize LJT.
// Supporting this will require some changes to the user interface.
// Handling natural deduction is awkward because the elimination rules have the connective in the premises. The user interface would
// be something like clicking on a formula, and then choosing a connective that was eliminated to produce that formula.

// Test case:  ¬(A ∨ ¬A) ⇒ ⊥
const ljCalculus: Logic = (input) => input.match(
    (goal, formula, inPremises, leftRight) => formula.match<OutputEvent>( // TODO: Refactor and finish.
        (predicate, ...terms) => {
            if(inPremises) {
                if(goal.consequences[0].matches(predicate, terms)) {
                    return new NewGoals('Ax', []);
                } else {
                    return new Failed('Formula does not match conclusion.');
                }
            } else {
                if(goal.premises.some(c => c.matches(predicate, terms))) {
                    return new NewGoals('Ax', []);
                } else {
                    return new Failed('Formula not found in premises.');
                }
            }
        },
        connective => {
            switch(connective) {
                case TOP_SYMBOL:
                    if(inPremises) {
                        return new NewGoals('⊤L', [new Goal(goal.premises.filter(f => f !== formula), goal.consequences)]);
                    } else {
                        return new NewGoals('⊤R', []);
                    }
                case BOT_SYMBOL:
                    if(inPremises) {
                        return new NewGoals('⊥L', []);
                    } else {
                        // TODO: Make ⊥ not clickable in conclusion.
                        // Behave as if we clicked on ⊥ in the premises, if there is a ⊥.
                        if(goal.premises.some(p => p instanceof NullaryConnective && p.connective === BOT_SYMBOL)) {
                            return new NewGoals('⊥L', []);
                        } else {
                            return new Failed('Didn\'t find ⊥ in premises.'); // TODO: Need to make this option inaccessible.');
                        }
                    }
                default:
                    throw 'Not implemented.';
                }
        },
        (connective, f2) => {
            switch(connective) {
                case NOT_SYMBOL:
                    if(inPremises) {
                        // TODO: This performs the contraction that LJT eliminates, i.e. duplicating formula in the first goal.
                        return new NewGoals('¬L', [new Goal(goal.premises, [f2])]);
                    } else {
                        return new NewGoals('¬R', [new Goal(goal.premises.concat(f2), [new NullaryConnective(BOT_SYMBOL)])]);
                    }
                default:
                    throw 'Not implemented.';
            }
        },
        (lf, connective, rf) => {
            switch(connective) {
                case AND_SYMBOL:
                    if(inPremises) {
                        // NOTE: This is treating ∧ like ∧^+ (i.e. with a positive polarity).
                        return new NewGoals('∧L', [new Goal(goal.premises.flatMap(f => f === formula ? [lf,rf] : [f]), goal.consequences)]);
                    } else {
                        return new NewGoals('∧R', [new Goal(goal.premises, [lf]), new Goal(goal.premises, [rf])]);
                    }
                case OR_SYMBOL:
                    if(inPremises) {
                        return new NewGoals('∨L', [new Goal(goal.premises.map(f => f === formula ? lf : f), goal.consequences),
                                                   new Goal(goal.premises.map(f => f === formula ? lf : f), goal.consequences)]);
                    } else {
                        if(leftRight === void(0)) return new Failed('Select left or right subformula.');
                        return new NewGoals(`∨R_${leftRight ? '1' : '2'}`, [new Goal(goal.premises, [leftRight ? lf : rf])]);
                    }
                case IMP_SYMBOL:
                    if(inPremises) {
                        // TODO: This performs the contraction that LJT eliminates, i.e. duplicating formula in the first goal.
                        return new NewGoals('⇒L', [new Goal(goal.premises, [lf]),
                                                   new Goal(goal.premises.map(f => f === formula ? rf : f), goal.consequences)]);
                    } else {
                        return new NewGoals('⇒R', [new Goal(goal.premises.concat(lf), [rf])]);
                    }
                default:
                    throw 'Not implemented.';
            }
        },
        (quantifier, v, f2) => {
            switch(quantifier) {
                case FORALL_SYMBOL:
                    if(inPremises) {
                        return new ContractOrInstantiate(goal, formula, inPremises);
                    } else {
                        const variableContext = goal.freeVariables();
                        const f3 = variableContext.has(v) ? f2.alphaRename(v, v.freshen(variableContext)) : f2;
                        return new NewGoals('∀R', [new Goal(goal.premises, [f3])]);
                    }
                case EXISTS_SYMBOL:
                    if(inPremises) {
                        const variableContext = goal.freeVariables();
                        const f3 = variableContext.has(v) ? f2.alphaRename(v, v.freshen(variableContext)) : f2;
                        return new NewGoals('∃L', [new Goal(goal.premises.map(f => f === formula ? f3 : f), goal.consequences)]);
                    } else {
                        return new ContractOrInstantiate(goal, formula, inPremises);
                    }
                default:
                    throw 'Not implemented.';
            }
        }),
    (goal, formula, inPremises) => {
        if(!inPremises) throw 'Should never happen.';
        return new NewGoals('CL', [new Goal(goal.premises.concat(formula), goal.consequences)]);
    },
    (goal, formula, inPremises, term) => {
        if(!(formula instanceof Quantifier)) throw 'Quantified formula expected.';
        // NOTE: Can't be as gung-ho about filtering out the original formulas from the contexts due to contraction.

        if(inPremises) { // then forall case
            let first = 0; // HACK: Horrible hack
            const f2 = formula.formula.substitute(formula.variable, term);
            return new NewGoals('∀L', [new Goal(goal.premises.map(f => f === formula && first++ === 0 ? f2 : f),
                                                goal.consequences)]);
        } else { // exists case
            const f2 = formula.formula.substitute(formula.variable, term);
            return new NewGoals('∃R', [new Goal(goal.premises, [f2])]);
        }
    });

/* Classical Logic **************************************************************************************************************************************************/

const classicalSequentCalculus: Logic = (input) => input.match(
    (goal, formula, inPremises) => formula.match<OutputEvent>( // TODO: Refactor and finish.
        (predicate, ...terms) => {
            if(inPremises) {
                if(goal.consequences.some(c => c.matches(predicate, terms))) {
                    return new NewGoals('Ax', []);
                } else {
                    return new Failed('Formula not found in conclusions.');
                }
            } else {
                if(goal.premises.some(c => c.matches(predicate, terms))) {
                    return new NewGoals('Ax', []);
                } else {
                    return new Failed('Formula not found in premises.');
                }
            }
        },
        connective => {
            switch(connective) {
                case TOP_SYMBOL:
                    if(inPremises) {
                        return new NewGoals('⊤L', [new Goal(goal.premises.filter(f => f !== formula), goal.consequences)]);
                    } else {
                        return new NewGoals('⊤R', []);
                    }
                case BOT_SYMBOL:
                    if(inPremises) {
                        return new NewGoals('⊥L', []);
                    } else {
                        return new NewGoals('⊥R', [new Goal(goal.premises, goal.consequences.filter(f => f !== formula))]);
                    }
                default:
                    throw 'Not implemented.';
            }
        },
        (connective, f2) => {
            switch(connective) {
                case NOT_SYMBOL:
                    if(inPremises) {
                        return new NewGoals('¬L', [new Goal(goal.premises.filter(f => f !== formula), goal.consequences.concat(f2))]);
                    } else {
                        return new NewGoals('¬R', [new Goal(goal.premises.concat(f2), goal.consequences.filter(f => f !== formula))]);
                    }
                default:
                    throw 'Not implemented.';
            }
        },
        (lf, connective, rf) => {
            switch(connective) {
                case AND_SYMBOL:
                    if(inPremises) {
                        return new NewGoals('∧L', [new Goal(goal.premises.flatMap(f => f === formula ? [lf,rf] : [f]), goal.consequences)]);
                    } else {
                        return new NewGoals('∧R', [new Goal(goal.premises, goal.consequences.map(f => f === formula ? lf : f)),
                                                   new Goal(goal.premises, goal.consequences.map(f => f === formula ? rf : f))]);
                    }
                case OR_SYMBOL:
                    if(inPremises) {
                        return new NewGoals('∨L', [new Goal(goal.premises.map(f => f === formula ? lf : f), goal.consequences),
                                                   new Goal(goal.premises.map(f => f === formula ? rf : f), goal.consequences)]);
                    } else {
                        return new NewGoals('∨R', [new Goal(goal.premises, goal.consequences.flatMap(f => f === formula ? [lf,rf] : [f]))]);
                    }
                case IMP_SYMBOL:
                    if(inPremises) {
                        return new NewGoals('⇒L', [new Goal(goal.premises.filter(f => f !== formula), goal.consequences.concat(lf)),
                                                   new Goal(goal.premises.map(f => f === formula ? rf : f), goal.consequences)]);
                    } else {
                        return new NewGoals('⇒R', [new Goal(goal.premises.concat(lf), goal.consequences.map(f => f === formula ? rf : f))]);
                    }
                default:
                    throw 'Not implemented.';
            }
        },
        (quantifier, v, f2) => {
            switch(quantifier) {
                case FORALL_SYMBOL:
                    if(inPremises) {
                        return new ContractOrInstantiate(goal, formula, inPremises);
                    } else {
                        const variableContext = goal.freeVariables();
                        const f3 = variableContext.has(v) ? f2.alphaRename(v, v.freshen(variableContext)) : f2;
                        return new NewGoals('∀R', [new Goal(goal.premises, goal.consequences.map(f => f === formula ? f3 : f))]);
                    }
                case EXISTS_SYMBOL:
                    if(inPremises) {
                        const variableContext = goal.freeVariables();
                        const f3 = variableContext.has(v) ? f2.alphaRename(v, v.freshen(variableContext)) : f2;
                        return new NewGoals('∃L', [new Goal(goal.premises.map(f => f === formula ? f3 : f), goal.consequences)]);
                    } else {
                        return new ContractOrInstantiate(goal, formula, inPremises);
                    }
                default:
                    throw 'Not implemented.';
            }
        }),
    (goal, formula, inPremises) => {
        if(inPremises) {
            return new NewGoals('CL', [new Goal(goal.premises.concat(formula), goal.consequences)]);
        } else {
            return new NewGoals('CR', [new Goal(goal.premises, goal.consequences.concat(formula))]);
        }
    },
    (goal, formula, inPremises, term) => {
        if(!(formula instanceof Quantifier)) throw 'Quantified formula expected.';
        // NOTE: Can't be as gung-ho about filtering out the original formulas from the contexts due to contraction.

        if(inPremises) { // then forall case
            let first = 0; // HACK: Horrible hack
            const f2 = formula.formula.substitute(formula.variable, term);
            return new NewGoals('∀L', [new Goal(goal.premises.map(f => f === formula && first++ === 0 ? f2 : f),
                                                goal.consequences)]);
        } else { // exists case
            let first = 0; // HACK: Horrible hack
            const f2 = formula.formula.substitute(formula.variable, term);
            return new NewGoals('∃R', [new Goal(goal.premises,
                                                goal.consequences.map(f => f === formula && first++ === 0 ? f2 : f))]);
        }
    });

const logics: {[l: string]: Logic} = {
    lk: classicalSequentCalculus,
    lj: ljCalculus
};

/* Main *************************************************************************************************************************************************************/

export function main(containerId: string, options : {logic: 'lk' | 'lj', toLaTeX?: boolean, showInput?: boolean, defaultGoal?: string}) {
    const container = document.getElementById(containerId);
    if(container === null) throw `Container missing. Element with ${containerId} not found.`;

    const defaultGoalString = options.defaultGoal || '((A \\/ B) -> C) -> ((A -> C) /\\ (B -> C))';
    const defaultGoal = goalFromString(defaultGoalString);
    if(defaultGoal === null) throw `Error parsing default goal: ${defaultGoalString}`;

    let example: SimpleDerivation = open(defaultGoal);

    const goalInput = wire()`<input type="text" id="goalInput" value="${defaultGoalString}"/>`;

    const toast = wire()`<div id="toast"></div>`;
    const termInput = wire()`<input type="text" id="termInput"/>`;
    const termBtn = wire()`<button id="termBtn">Go</button>`;
    const contractBtn = wire()`<button id="contractBtn">Contract</button>`;
    const popup = wire()`<div id="popup"><div id="popupBody">${[termInput, termBtn, contractBtn]}<p>Enter a term and click Go, or click Contract to perform a contraction.</p></div></div>`;

    const latexBtn = wire()`<button id="latexBtn">LaTeX</button>`;
    const latex = wire()`<code id="latex"></code>`;
    const latexContainer = wire()`<div class="${options.toLaTeX ? '' : 'hidden'}">${latexBtn}<pre>${latex}</pre></div>`;

    const logic = options.logic === void(0) ? classicalSequentCalculus : logics[options.logic];

    const derivationFromHash = () => {
        try {
            // Compress and decompress? http://lzma-js.github.io/LZMA-JS/ or http://pieroxy.net/blog/pages/lz-string/index.html
            const derivationJson = JSON.parse(decompressFromEncodedURIComponent(location.hash.slice(1)));
            if(derivationJson !== void(0)) {
                const json = expandCse(derivationJson);
                const derivation = derivationFromJson(json);
                if(derivation !== null) {
                    example = derivation;
                    (goalInput as any).value = '';
                } else {
                    console.log({expanded: json, unexpanded: derivationJson, string: location.hash.slice(1)});
                }
            }
        } catch(SyntaxError) {} // Ignore SyntaxErrors
    };

    const dummy = {};

    const refresh = (changeHash: boolean = true) => {
        document.title = 'Proving ' + example.conclusion.toDisplayString(true);
        if(changeHash) location.hash = '#'+compressToEncodedURIComponent(JSON.stringify(cse(example.toJson())));
        bind(container)`${[
            wire(dummy, 'goalBox')`<div id="goalBox" class="${options.showInput ? '' : 'hidden'}">Enter goal or formula: ${goalInput}</div>`,
            toast,
            wire(dummy, 'wrapper')`<div id="derivationWrapper">${renderDerivation(example, new StartPath('root.'), new GoalExtender(example.conclusion), true, true)}</div>`,
            popup,
            latexContainer
        ]}`;
    };

    const SHOWN_CLASS = 'shown';
    const FORALL_CLASS = 'forall';
    const EXISTS_CLASS = 'exists';

    const onClick = (event: MouseEvent) => {
        const target: any = event.target;
        let extraData = target.data as {extender: DerivationExtender, formula?: SimpleFormula, inPremises?: boolean};
        if(target.data === void(0)) {
            const closest = target.closest('.active');
            if(closest === null) return;
            extraData = closest.data; // TODO: Include some information about the clicked element.
        }

        if(extraData.formula === void(0)) {
            example = extraData.extender.open();
        } else {
            const leftRight = target.closest('.left') ? true : target.closest('.right') ? false : void(0);
            const output = logic(new ApplyTactic(extraData.extender.goal, extraData.formula, extraData.inPremises!!, leftRight));
            example = output.match(
                (message) => {
                    toast.textContent = message;
                    toast.classList.add(SHOWN_CLASS);
                    return example;
                },
                (name, goals) => extraData.extender.extend(name, goals.map(g => new OpenDerivation(g))),
                (goal, formula, inPremises) => {
                    (popup as any).data = extraData;
                    popup.style.left = (event.pageX-45) + 'px';
                    popup.style.top = (event.pageY-40) + 'px';
                    popup.className = 'shown ' + (inPremises ? FORALL_CLASS : EXISTS_CLASS);
                    termInput.focus();
                    return example;
                });
        }
        refresh();
    };

    const onTermInput = (event: Event) => {
        const extraData = (popup as any).data as {extender: DerivationExtender, formula: SimpleFormula, inPremises: boolean};
        let output: OutputEvent;
        if(event.target === contractBtn) {
            output = logic(new Contract(extraData.extender.goal, extraData.formula, extraData.inPremises));
        } else { // termBtn was clicked or termInput changed, either way do the same thing
            const termString: string = (termInput as any).value;
            const term = termFromString(termString);
            if(term === null) {
                output = new Failed(`Failed to parse term: ${termString}`);
            } else {
                output = logic(new Instantiate(extraData.extender.goal, extraData.formula, extraData.inPremises, term));
            }
        }
        (termInput as any).value = '';
        popup.className = '';
        example = output.match(
            (message) => {
                toast.textContent = message;
                toast.classList.add(SHOWN_CLASS);
                return example;
            },
            (name, goals) => extraData.extender.extend(name, goals.map(g => new OpenDerivation(g))),
            (goal, formula, inPremises) => {
                throw 'Shouldn\'t happen'; // Right?
            });
        refresh();
    };

    const onGoalInput = (event: Event) => {
        const goalText: string = (goalInput as any).value;
        const goal = goalFromString(goalText);
        if(goal === null || (options.logic === 'lj' && goal.consequences.length !== 1)) {
            toast.textContent = 'Failed to parse goal.';
            toast.classList.add(SHOWN_CLASS);
        } else {
            example = new OpenDerivation(goal);
            refresh();
        }
    };

    const onAnimationEnd = (event: Event) => toast.classList.remove(SHOWN_CLASS);
    const onMouseLeave = (event: Event) => { (popup as any).data = void(0); popup.className = ''; };
    const onHashChange = (event: Event) => { derivationFromHash(); refresh(false); };
    const onLaTeX = (event: Event) => { latex.textContent = example.toLaTeX(true); };

    const scheduler = newDefaultScheduler();

    runEffects(tap(onClick, click(container, true)), scheduler);
    runEffects(tap(onTermInput, merge(change(termInput), merge(click(termBtn), click(contractBtn)))), scheduler);
    runEffects(tap(onGoalInput, change(goalInput)), scheduler);
    runEffects(tap(onAnimationEnd, domEvent('animationend', toast)), scheduler);
    runEffects(tap(onMouseLeave, mouseleave(popup)), scheduler);
    runEffects(tap(onHashChange, hashchange(window)), scheduler);
    runEffects(tap(onLaTeX, click(latexBtn)), scheduler);

    derivationFromHash();
    refresh(false);
}
