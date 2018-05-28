import { bind, wire } from "hyperhtml/esm";
import { runEffects, tap, merge } from "@most/core";
import { click, domEvent, mouseleave, change } from "@most/dom-event";
import { newDefaultScheduler } from "@most/scheduler";
import { Set } from "immutable";
import { cse } from "./json-with-sharing"

type Json = any;

interface ToJson {
    toJson(): Json;
}

interface FreeVariables<V, T> {
    freeVariables(): Set<V>;
    substitute(f: (v: V) => T): this;
}

/* Terms ************************************************************************************************************************************************************/

interface GenericTerm<V, O> extends ToJson, FreeVariables<V, GenericTerm<V, O>> {
    match<A>(variableCase: (v: V) => A,
             operatorCase: (operator: O, ...terms: Array<GenericTerm<V, O>>) => A): A;
    equals(other: GenericTerm<V, O>): boolean;
}

class Variable<V, O> implements GenericTerm<V, O> {
    constructor(readonly variable: V) {}
    match<A>(variableCase: (v: V) => A, opCase: (o: O, ...ts: Array<GenericTerm<V, O>>) => A): A {
        return variableCase(this.variable);
    }

    toJson(): Json {
        return this.variable;
    }

    freeVariables(): Set<V> {
        return Set.of(this.variable);
    }

    substitute(f: (v: V) => GenericTerm<V, O>): this {
        return f(this.variable) as this;
    }

    equals(other: GenericTerm<V, O>): boolean {
        return other.match(
                    v => v === this.variable,
                    _ => false);
    }
}

class Operator<V, O> implements GenericTerm<V, O> {
    readonly terms: Array<GenericTerm<V, O>>;
    constructor(readonly operator: O, ...ts: Array<GenericTerm<V, O>>) { this.terms = ts; }
    match<A>(variableCase: (v: V) => A, opCase: (o: O, ...ts: Array<GenericTerm<V, O>>) => A): A {
        return opCase(this.operator, ...this.terms);
    }

    toJson(): Json {
        return [this.operator, this.terms.map(t => t.toJson())];
    }

    freeVariables(): Set<V> {
        return Set.union(this.terms.map(t => t.freeVariables()));
    }

    substitute(f: (v: V) => GenericTerm<V, O>): this {
        return new Operator(this.operator, ...this.terms.map(t => t.substitute(f))) as this;
    }

    equals(other: GenericTerm<V, O>): boolean {
        return other.match(
                    v => false,
                    (o, ...ts) => o === this.operator 
                               && this.terms.length === ts.length
                               && ts.every((t, i) => t.equals(this.terms[i])));
    }
}

/*
function termFromJson(json: Json): SimpleTerm | null {
    if(typeof json === 'string') return new Variable(json);
    if(typeof json !== 'object' || json === null || !(json instanceof Array) || json.length < 1) return null;
}
*/

// TODO: fromJson

/* Formulas *********************************************************************************************************************************************************/

interface GenericFormula<V, P, C, Q, O, T extends GenericTerm<V, O>> extends ToJson, FreeVariables<V, GenericTerm<V, O>> {
    match<A>(predicateCase: (predicate: P, ...terms: Array<T>) => A,
             nullaryCase: (connective: C) => A,
             unaryCase: (connective: C, formula: GenericFormula<V, P, C, Q, O, T>) => A,
             binaryCase: (leftFormula: GenericFormula<V, P, C, Q, O, T>, connective: C, rightFormula: GenericFormula<V, P, C, Q, O, T>) => A,
             quantifierCase: (quantifier: Q, v: V, formula: GenericFormula<V, P, C, Q, O, T>) => A): A;
    matches(predicate: P, terms: Array<T>): boolean;
}

class Predicate<V, P, C, Q, O, T extends GenericTerm<V, O>> implements GenericFormula<V, P, C, Q, O, T> {
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
        return [this.predicate, this.terms.map(t => t.toJson())];
    }

    freeVariables(): Set<V> {
        return Set.union(this.terms.map(t => t.freeVariables()));
    }

    substitute(f: (v: V) => GenericTerm<V, O>): this {
        return new Predicate(this.predicate, ...this.terms.map(t => t.substitute(f))) as this;
    }

    matches(predicate: P, terms: Array<T>): boolean { 
        return this.predicate === predicate
            && this.terms.length === terms.length
            && terms.every((t, i) => t.equals(this.terms[i]));
    }
}

class NullaryConnective<V, P, C, Q, O, T extends GenericTerm<V, O>> implements GenericFormula<V, P, C, Q, O, T> {
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

    freeVariables(): Set<V> {
        return Set();
    }

    substitute(f: (v: V) => GenericTerm<V, O>): this { return this; }

    matches(predicate: P, terms: Array<T>): boolean { return false; }
}

class UnaryConnective<V, P, C, Q, O, T extends GenericTerm<V, O>> implements GenericFormula<V, P, C, Q, O, T> {
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

    freeVariables(): Set<V> {
        return this.formula.freeVariables();
    }

    substitute(f: (v: V) => GenericTerm<V, O>): this {
        return new UnaryConnective(this.connective, this.formula.substitute(f)) as this;
    }

    matches(predicate: P, terms: Array<T>): boolean { return false; }
}

class BinaryConnective<V, P, C, Q, O, T extends GenericTerm<V, O>> implements GenericFormula<V, P, C, Q, O, T> {
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

    freeVariables(): Set<V> {
        return this.leftFormula.freeVariables().union(this.rightFormula.freeVariables());
    }

    substitute(f: (v: V) => GenericTerm<V, O>): this {
        return new BinaryConnective(this.leftFormula.substitute(f), this.connective, this.rightFormula.substitute(f)) as this;
    }

    matches(predicate: P, terms: Array<T>): boolean { return false; }
}

class Quantifier<V, P, C, Q, O, T extends GenericTerm<V, O>> implements GenericFormula<V, P, C, Q, O, T> {
    constructor(readonly quantifier: Q, readonly variable: V, readonly formula: GenericFormula<V, P, C, Q, O, T>) {}
    match<A>(predicateCase: (predicate: P, ...terms: Array<T>) => A,
             nullaryCase: (connective: C) => A,
             unaryCase: (connective: C, formula: GenericFormula<V, P, C, Q, O, T>) => A,
             binaryCase: (leftFormula: GenericFormula<V, P, C, Q, O, T>, connective: C, rightFormula: GenericFormula<V, P, C, Q, O, T>) => A,
             quantifierCase: (quantifier: Q, v: V, formula: GenericFormula<V, P, C, Q, O, T>) => A): A {
        return quantifierCase(this.quantifier, this.variable, this.formula);
    }

    toJson(): Json {
        return {q: this.quantifier, v: this.variable, f: this.formula.toJson()};
    }

    freeVariables(): Set<V> {
        return this.formula.freeVariables().delete(this.variable);
    }

    substitute(f: (v: V) => GenericTerm<V, O>): this {
        // TODO: This is where we'd need to do some renaming.
        return new Quantifier(this.quantifier, this.variable, this.formula.substitute(f)) as this;
    }

    matches(predicate: P, terms: Array<T>): boolean { return false; }
}

// TODO: fromJson

/* Goals ************************************************************************************************************************************************************/

interface GenericGoal<F extends ToJson> extends ToJson {
    match<A>(f: (premises: Array<F>, consequences: Array<F>) => A): A;
    readonly premises: Array<F>;
    readonly consequences: Array<F>;
}

class Goal<F extends ToJson> implements GenericGoal<F> {
    constructor(readonly premises: Array<F>, readonly consequences: Array<F>) {}
    match<A>(f: (premises: Array<F>, consequences: Array<F>) => A): A {
        return f(this.premises, this.consequences);
    }

    toJson(): Json {
        return [this.premises.map(p => p.toJson()), this.consequences.map(c => c.toJson())];
    }
}

// TODO: fromJson

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
        [Lexer.NAME_TOKEN]: /^\s*([a-zA-Z][a-zA-Z0-9]*)/giu,
        [Lexer.LPAREN_TOKEN]: /^\s*(\()/giu,
        [Lexer.RPAREN_TOKEN]: /^\s*(\))/giu,
        [Lexer.COMMA_TOKEN]: /^\s*(,)/giu,
        [Lexer.PERIOD_TOKEN]: /^\s*(\.)/giu,
        [Lexer.TURNSTILE_TOKEN]: /^\s*(\|-|⊢)/giu,
        [Lexer.BOT_TOKEN]: /^\s*(_\|_|⊥)/giu,
        [Lexer.TOP_TOKEN]: /^\s*(⊤)/giu, // TODO: ASCII version?
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
        //nameRE.lastIndex = this.position;
        const input = this.inputString.slice(this.position);
        nameRE.lastIndex = 0;
        const nameResult = nameRE.exec(input);
        if(nameResult !== null) {
            this.position += nameRE.lastIndex;
            const s = nameResult[1];
            if(/^forall$/i.test(s)) return [Lexer.FORALL_TOKEN, s];
            if(/^exists$/i.test(s)) return [Lexer.EXISTS_TOKEN, s];
            return [Lexer.NAME_TOKEN, s];
        } else {
            for(const reName in Lexer.lexTable) {
                if(reName === Lexer.NAME_TOKEN) continue;
                const re = Lexer.lexTable[reName as TokenType];
                //re.lastIndex = this.position;
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

// TODO: Improve error messages.

/*
Term ::= NAME (LPAREN TermList RPAREN)?
TermList ::= Term (COMMA Term)*
*/
function parseTerm(lexer: Lexer): SimpleTerm | null {
    const nameToken = lexer.peek();
    if(nameToken === null || nameToken[0] !== Lexer.NAME_TOKEN) return null;
    const lparenToken = lexer.next();
    if(lparenToken === 'error') return null;
    if(lparenToken === 'done' || lparenToken[0] !== Lexer.LPAREN_TOKEN) return new Variable(nameToken[1]);
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
function parseFormula(lexer: Lexer): SimpleFormula | null {
    const leadToken = lexer.peek();
    if(leadToken === null) return null;
    switch(leadToken[0]) {
        case Lexer.NOT_TOKEN:
            lexer.next();
            const f = parseAtomicFormula(lexer);
            if(f === null) return null;
            return new UnaryConnective(NOT_SYMBOL, f);
        case Lexer.FORALL_TOKEN:
        case Lexer.EXISTS_TOKEN:
            const nameToken = lexer.next();
            if(nameToken === 'done' || nameToken === 'error' || nameToken[0] !== Lexer.NAME_TOKEN) return null;
            const periodToken = lexer.next();
            if(periodToken === 'done' || periodToken === 'error' || periodToken[0] !== Lexer.PERIOD_TOKEN) return null;
            lexer.next();
            const formula = parseAtomicFormula(lexer);
            if(formula === null) return null;
            return new Quantifier(leadToken[0] === Lexer.FORALL_TOKEN ? FORALL_SYMBOL : EXISTS_SYMBOL, nameToken[1], formula);
        default:
            const lf = parseAtomicFormula(lexer);
            if(lf === null) return null;
            const rf = parseFormulaTail(lexer);
            if(rf === null) return lf;
            const conn = rf[0] === Lexer.AND_TOKEN ? AND_SYMBOL : rf[0] === Lexer.OR_TOKEN ? OR_SYMBOL : IMP_SYMBOL;
            return new BinaryConnective(lf, conn, rf[1]);
    }
}

function parseAtomicFormula(lexer: Lexer): SimpleFormula | null {
    const leadToken = lexer.peek();
    if(leadToken === null) return null;
    switch(leadToken[0]) {
        case Lexer.TOP_TOKEN:
            lexer.next();
            return new NullaryConnective(TOP_SYMBOL);
        case Lexer.BOT_TOKEN:
            lexer.next();
            return new NullaryConnective(BOT_SYMBOL);
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

type BinaryConnectiveName = 'AND' | 'OR' | 'IMPLIES';

function parseFormulaTail(lexer: Lexer): [BinaryConnectiveName, SimpleFormula] | null {
    const bc = lexer.peek();
    if(bc === null || (bc[0] !== Lexer.AND_TOKEN && bc[0] !== Lexer.OR_TOKEN && bc[0] !== Lexer.IMP_TOKEN)) return null;
    lexer.next();
    const rf = parseAtomicFormula(lexer);
    if(rf === null) return null;
    return [bc[0] as BinaryConnectiveName, rf];
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

interface GenericDerivation<G extends ToJson> extends ToJson {
    match<A>(openCase: (conclusion: G) => A, inferenceCase: (name: string, premises: Array<GenericDerivation<G>>, conclusion: G) => A): A;
    conclusion: G;
    isCompleted(): boolean;
}

class OpenDerivation<G extends ToJson> implements GenericDerivation<G> {
    constructor(readonly conclusion:  G) {}
    match<A>(openCase: (conclusion: G) => A, inferenceCase: (name: string, premises: Array<GenericDerivation<G>>, conclusion: G) => A): A {
        return openCase(this.conclusion);
    }

    toJson(): Json {
        return {c: this.conclusion.toJson()};
    }

    isCompleted(): boolean { return false; }
}

class Inference<G extends ToJson> implements GenericDerivation<G> {
    constructor(readonly name: string, readonly premises: Array<GenericDerivation<G>>, readonly conclusion: G) {}
    match<A>(openCase: (conclusion: G) => A, inferenceCase: (name: string, premises: Array<GenericDerivation<G>>, conclusion: G) => A): A {
        return inferenceCase(this.name, this.premises, this.conclusion);
    }

    toJson(): Json {
        return {n: this.name, c: this.conclusion.toJson(), p: this.premises.map(p => p.toJson())};
    }

    isCompleted(): boolean { return this.premises.every(p => p.isCompleted()); }
}

// TODO: fromJson

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

type Var = string;

type SimpleTerm = GenericTerm<Var, string>;
type SimpleFormula = GenericFormula<Var, string, string, string, string, SimpleTerm>;
type SimpleGoal = GenericGoal<SimpleFormula>;
type SimpleDerivation = GenericDerivation<SimpleGoal>;

function renderTerm(t: SimpleTerm): Element {
    return t.match(
        v => wire()`<span class="occurrence">${v}</span>`,
        (o, ...ts) => wire()`<span class="operator">${o}</span>(${
                                ts.flatMap((t, i) => i+1 === ts.length ? [renderTerm(t)] : [renderTerm(t), wire()`, `])
                             })`);
}

// TODO: Add precedence system.
function renderFormula(f: SimpleFormula, path: Path, inPremises: boolean, extender?: DerivationExtender): Element {
    const id = path.toString();
    if(extender !== void(0)) {
        const extraData = {extender: extender, formula: f, inPremises: inPremises};
        return f.match(
            (p, ...ts) => wire(f, id)`<div id="${id}" data=${extraData} class="formula topLevel"><!--
                                         --><span class="predicate"><span class="predicateSymbol">${p}</span>${
                                                ts.length === 0 ? '' : '('}${
                                                ts.flatMap((t, i) => i+1 === ts.length ? [renderTerm(t)]
                                                                                       : [renderTerm(t), wire()`, `])
                                           }${ts.length === 0 ? '' : ')'}</span></div>`,
            c => wire(f, id)`<div id="${id}" data=${extraData} class="formula topLevel"><span class="connective nullary">${c}</span></div>`,
            (c, f) => wire(f, id)`<div id="${id}" data=${extraData} class="formula topLevel"><!--
                                     --><span class="connective unary">${c}</span>${
                                        renderFormula(f, path.extend(1), inPremises)
                                 }</div>`,
            (lf, c, rf) => wire(f, id)`<div id="${id}" data=${extraData} class="formula topLevel">${
                                            renderFormula(lf, path.extend(1), inPremises)
                                           }<span class="connective binary">${c}</span>${
                                            renderFormula(rf, path.extend(2), inPremises)
                                      }</div>`,
            (q, v, f) => wire(f, id)`<div id="${id}" data=${extraData} class="formula topLevel quantifier"><!--
                                     --><span class="connective quantifier">${q}</span><!--
                                     --><span class="boundVariable">${v}</span><!--
                                     --><span class="quantifierSeparator">.</span>${
                                        renderFormula(f, path.extend(1), inPremises)
                                    }</div>`);
    } else {
        return f.match(
            (p, ...ts) => wire(f, id)`<div id="${id}" class="formula"><!--
                                         --><span class="predicate"><span class="predicateSymbol">${p}</span>${
                                                ts.length === 0 ? '' : '('}${
                                                ts.flatMap((t, i) => i+1 === ts.length ? [renderTerm(t)]
                                                                                       : [renderTerm(t), wire()`, `])
                                           }${ts.length === 0 ? '' : ')'}</span></div>`,
            c => wire(f, id)`<div id="${id}" class="formula"><span class="connective nullary">${c}</span></div>`,
            (c, f) => wire(f, id)`<div id="${id}" class="formula">(<!--
                                     --><span class="connective unary">${c}</span>r${
                                        renderFormula(f, path.extend(1), inPremises)
                                 })</div>`,
            (lf, c, rf) => wire(f, id)`<div id="${id}" class="formula">(${
                                            renderFormula(lf, path.extend(1), inPremises)
                                           }<span class="connective binary">${c}</span>${
                                            renderFormula(rf, path.extend(2), inPremises)
                                      })</div>`,
            (q, v, f) => wire(f, id)`<div id="${id}" class="formula quantifier">(<!--
                                     --><span class="connective quantifier">${q}</span><!--
                                     --><span class="boundVariable">${v}</span><!--
                                     --><span class="quantifierSeparator">.</span>${
                                        renderFormula(f, path.extend(1), inPremises)
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
                          ps.flatMap((p, i) => i === psLenm1 ? [renderFormula(p, path.extend(i), true, extender)] 
                                                             : [renderFormula(p, path.extend(i), true, extender), wire()`, `])
                    }</div>`
            }<span class="turnstile" data=${{extender: extender}}>⊢</span>${
            wire(cs, id)`<div id="${id+"consequences"}" class="consequences context">${
                            cs.flatMap((c, i) => i === csLenm1 ? [renderFormula(c, path.extend(i+psLen), false, extender)]
                                                               : [renderFormula(c, path.extend(i+psLen), false, extender), wire()`, `])
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
                         --><div class="tag">${n}</div><!--
                         --><div class="row ruleConclusion">${
                                renderGoal(c, path.extend(ps.length), extender)
                            }</div></div>`);
}

/* Helpers **********************************************************************************************************************************************************/

const BOT_SYMBOL = '⊥';
const TOP_SYMBOL = '⊤';
const NOT_SYMBOL = '¬';
const AND_SYMBOL = '∧';
const OR_SYMBOL = '∨';
const IMP_SYMBOL = '⇒';
const FORALL_SYMBOL = '∀';
const EXISTS_SYMBOL = '∃';

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

function entails(premises: Array<SimpleFormula>, consequences: Array<SimpleFormula>): Goal<SimpleFormula> {
    return new Goal<SimpleFormula>(premises, consequences);
}

function infers(name: string, premises: Array<SimpleDerivation>, conclusion: SimpleGoal): Inference<SimpleGoal> {
    return new Inference<SimpleGoal>(name, premises, conclusion);
}

/* Events ***********************************************************************************************************************************************************/

interface InputEvent {
    match<A>(
        applyTacticCase: (goal: SimpleGoal, formula: SimpleFormula, inPremises: boolean) => A,
        contractCase: (goal: SimpleGoal, formula: SimpleFormula, inPremises: boolean) => A,
        instantiateCase: (goal: SimpleGoal, formula: SimpleFormula, inPremises: boolean, term: SimpleTerm) => A): A;
}

class ApplyTactic implements InputEvent {
    constructor(readonly goal: SimpleGoal, readonly formula: SimpleFormula, readonly inPremises: boolean) {}
    match<A>(
      applyTacticCase: (goal: SimpleGoal, formula: SimpleFormula, inPremises: boolean) => A,
      contractCase: (goal: SimpleGoal, formula: SimpleFormula, inPremises: boolean) => A,
      instantiateCase: (goal: SimpleGoal, formula: SimpleFormula, inPremises: boolean, term: SimpleTerm) => A): A {
        return applyTacticCase(this.goal, this.formula, this.inPremises);
    }
}

class Contract implements InputEvent {
    constructor(readonly goal: SimpleGoal, readonly formula: SimpleFormula, readonly inPremises: boolean) {}
    match<A>(
      applyTacticCase: (goal: SimpleGoal, formula: SimpleFormula, inPremises: boolean) => A,
      contractCase: (goal: SimpleGoal, formula: SimpleFormula, inPremises: boolean) => A,
      instantiateCase: (goal: SimpleGoal, formula: SimpleFormula, inPremises: boolean, term: SimpleTerm) => A): A {
        return contractCase(this.goal, this.formula, this.inPremises);
    }
}

class Instantiate implements InputEvent {
    constructor(readonly goal: SimpleGoal, readonly formula: SimpleFormula, readonly inPremises: boolean, readonly term: SimpleTerm) {}
    match<A>(
      applyTacticCase: (goal: SimpleGoal, formula: SimpleFormula, inPremises: boolean) => A,
      contractCase: (goal: SimpleGoal, formula: SimpleFormula, inPremises: boolean) => A,
      instantiateCase: (goal: SimpleGoal, formula: SimpleFormula, inPremises: boolean, term: SimpleTerm) => A): A {
        return instantiateCase(this.goal, this.formula, this.inPremises, this.term);
    }
}

interface OutputEvent {
    match<A>(
        failedCase: (message: string) => A,
        newGoalsCase: (name: string, goals: Array<SimpleGoal>) => A,
        contractOrInstantiateCase: (goal: SimpleGoal, formula: SimpleFormula, inPremises: boolean) => A): A;
}

class Failed implements OutputEvent {
    constructor(readonly message: string) {}
    match<A>(
      failedCase: (message: string) => A,
      newGoalsCase: (name: string, goals: Array<SimpleGoal>) => A,
      contractOrInstantiateCase: (goal: SimpleGoal, formula: SimpleFormula, inPremises: boolean) => A): A {
        return failedCase(this.message);
    }
}

class NewGoals implements OutputEvent {
    constructor(readonly name: string, readonly goals: Array<SimpleGoal>) {}
    match<A>(
      failedCase: (message: string) => A,
      newGoalsCase: (name: string, goals: Array<SimpleGoal>) => A,
      contractOrInstantiateCase: (goal: SimpleGoal, formula: SimpleFormula, inPremises: boolean) => A): A {
        return newGoalsCase(this.name, this.goals);
    }
}

class ContractOrInstantiate implements OutputEvent {
    constructor(readonly goal: SimpleGoal, readonly formula: SimpleFormula, readonly inPremises: boolean) {}
    match<A>(
      failedCase: (message: string) => A,
      newGoalsCase: (name: string, goals: Array<SimpleGoal>) => A,
      contractOrInstantiateCase: (goal: SimpleGoal, formula: SimpleFormula, inPremises: boolean) => A): A {
        return contractOrInstantiateCase(this.goal, this.formula, this.inPremises);
    }
}

/* Logic ************************************************************************************************************************************************************/

type Logic = (input: InputEvent) => OutputEvent;

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
                        return new NewGoals('∧L', [new Goal(goal.premises.filter(f => f !== formula).concat(lf,rf), goal.consequences)]);
                    } else {
                        const cs = goal.consequences.filter(f => f !== formula);
                        return new NewGoals('∧R', [new Goal(goal.premises, cs.concat(lf)),
                                                   new Goal(goal.premises, cs.concat(rf))]);
                    }
                case OR_SYMBOL:
                    if(inPremises) {
                        const ps = goal.premises.filter(f => f !== formula);
                        return new NewGoals('∨L', [new Goal(ps.concat(lf), goal.consequences),
                                                   new Goal(ps.concat(rf), goal.consequences)]);
                    } else {
                        return new NewGoals('∨R', [new Goal(goal.premises, goal.consequences.filter(f => f !== formula).concat(lf,rf))]);
                    }
                case IMP_SYMBOL:
                    if(inPremises) {
                        const ps = goal.premises.filter(f => f !== formula);
                        return new NewGoals('⇒L', [new Goal(ps, goal.consequences.concat(lf)),
                                                   new Goal(ps.concat(rf), goal.consequences)]);
                    } else {
                        return new NewGoals('⇒R', [new Goal(goal.premises.concat(lf), goal.consequences.filter(f => f !== formula).concat(rf))]);
                    }
                default: 
                    throw 'Not implemented.'; 
            }
        },
        (quantifier, v, f2) => { 
            switch(quantifier) {
                // TODO: Variable renaming shenanigans should occur here-ish.
                case FORALL_SYMBOL:
                    if(inPremises) {
                        return new ContractOrInstantiate(goal, formula, inPremises);
                    } else {
                        return new NewGoals('∀R', [new Goal(goal.premises, goal.consequences.filter(f => f !== formula).concat(f2))]);
                    }
                case EXISTS_SYMBOL:
                    if(inPremises) {
                        return new NewGoals('∃L', [new Goal(goal.premises.filter(f => f !== formula).concat(f2), goal.consequences)]);
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
        if(!(formula instanceof Quantifier)) throw 'Non-quantified expression not expected.';
        // NOTE: Can't be as gung-ho about filtering out the original formulas from the contexts due to contraction.

        if(inPremises) { // then forall case
        
        } else { // exists case
        
        }
        throw 'Not implemented yet.';
    });

/* Main *************************************************************************************************************************************************************/

const A = predicate('A');
const B = predicate('B');

// let example: SimpleDerivation = open(entails([], [implies(implies(implies(A, B), A), A)]));
let example: SimpleDerivation = open(entails([exists('x', forall('y', predicate('P', variable('x'), variable('y'))))], [forall('x', exists('y', predicate('P', variable('x'), variable('y'))))]));

const container = document.getElementById('container');
const toast = document.getElementById('toast');
const popup = document.getElementById('popup');
const termInput = document.getElementById('termInput');
const termBtn = document.getElementById('termBtn');
const contractBtn = document.getElementById('contractBtn');
if(popup === null) throw 'Popup missing.';
if(toast === null) throw 'Toast missing.';
if(termInput === null) throw 'Term Input missing.';
if(termBtn === null) throw 'Term button missing.';
if(contractBtn === null) throw 'Contract button missing.';
if(container === null) throw 'Container missing.';

const refresh = () => {
    location.hash = '#'+encodeURIComponent(JSON.stringify(cse(example.toJson())));
    bind(container)`${renderDerivation(example, new StartPath('root.'), new GoalExtender(example.conclusion), true, true)}`;
};

const onClick = (event: MouseEvent) => {
    const target: any = event.target;
    let extraData = target.data as {extender: DerivationExtender, formula?: SimpleFormula, inPremises?: boolean};
    if(target.data === void(0)) {
        const closest = target.closest('.topLevel');
        if(closest === null) return;
        extraData = closest.data;
    }

    if(extraData.formula === void(0)) {
        example = extraData.extender.open();
    } else {
        const output = classicalSequentCalculus(new ApplyTactic(extraData.extender.goal, extraData.formula, extraData.inPremises!!));
        example = output.match(
            (message) => {
                toast.textContent = message;
                toast.className = 'shown';
                return example;
            },
            (name, goals) => extraData.extender.extend(name, goals.map(g => new OpenDerivation(g))),
            (goal, formula, inPremises) => {  // TODO: Save the extender so it can be used when the user is done interacting with the popup.
                (popup as any).data = extraData;
                popup.style.left = (event.pageX-45) + 'px';
                popup.style.top = (event.pageY-40) + 'px';
                popup.className = 'shown';
                return example;
            });
    }
    refresh();
};

const onTermInput = (event: Event) => {
    const extraData = (popup as any).data as {extender: DerivationExtender, formula: SimpleFormula, inPremises: boolean};
    let output: OutputEvent;
    if(event.target === contractBtn) {
        output = classicalSequentCalculus(new Contract(extraData.extender.goal, extraData.formula, extraData.inPremises));
    } else { // termBtn was clicked or termInput changed, either way do the same thing
        const termString: string = (termInput as any).value;
        const term = termFromString(termString);
        if(term === null) {
            output = new Failed(`Failed to parse term: ${termString}`);
        } else {
            output = classicalSequentCalculus(new Instantiate(extraData.extender.goal, extraData.formula, extraData.inPremises, term));
        }
    }
    (termInput as any).value = '';
    popup.className = '';
    example = output.match(
        (message) => {
            toast.textContent = message;
            toast.className = 'shown';
            return example;
        },
        (name, goals) => extraData.extender.extend(name, goals.map(g => new OpenDerivation(g))),
        (goal, formula, inPremises) => {
            throw "Shouldn't happen"; // Right?
        });
    refresh();
};

const onAnimationEnd = (event: Event) => toast.className = '';
const onMouseLeave = (event: Event) => { (popup as any).data = void(0); popup.className = ''; }

const scheduler = newDefaultScheduler();
runEffects(tap(onClick, click(container, true)), scheduler);
runEffects(tap(onTermInput, merge(change(termInput), merge(click(termBtn), click(contractBtn)))), scheduler);
runEffects(tap(onAnimationEnd, domEvent('animationend', toast, false)), scheduler);
runEffects(tap(onMouseLeave, mouseleave(popup, false)), scheduler);

refresh();
