import { bind, wire } from "hyperhtml/cjs";
import { runEffects, tap } from "@most/core";
import { click } from "@most/dom-event";
import { newDefaultScheduler } from "@most/scheduler";
import { Set } from "immutable";

type Json = any;

interface ToJson {
    toJson(): Json;
}

interface FreeVariables<V> {
    freeVariables(): Set<V>;
    mapVariables(f: (v: V) => V): this;
}

/* Terms ************************************************************************************************************************************************************/

interface GenericTerm<V, O> extends ToJson, FreeVariables<V> {
    match<A>(variableCase: (v: V) => A,
             operatorCase: (operator: O, ...terms: Array<GenericTerm<V, O>>) => A): A;
}

class Variable<V, O> implements GenericTerm<V, O> {
    constructor(readonly variable: V) {}
    match<A>(variableCase: (v: V) => A, opCase: (o: O, ...ts: Array<GenericTerm<V, O>>) => A): A {
        return variableCase(this.variable);
    }

    toJson(): Json {
        return {variable: this.variable};
    }

    freeVariables(): Set<V> {
        return Set.of(this.variable);
    }

    mapVariables(f: (v: V) => V): this {
        return new Variable(f(this.variable)) as this;
    }
}

class Operator<V, O> implements GenericTerm<V, O> {
    readonly terms: Array<GenericTerm<V, O>>;
    constructor(readonly operator: O, ...ts: Array<GenericTerm<V, O>>) { this.terms = ts; }
    match<A>(variableCase: (v: V) => A, opCase: (o: O, ...ts: Array<GenericTerm<V, O>>) => A): A {
        return opCase(this.operator, ...this.terms);
    }

    toJson(): Json {
        return {operator: this.operator, args: this.terms.map(t => t.toJson())};
    }

    freeVariables(): Set<V> {
        return Set.union(this.terms.map(t => t.freeVariables()));
    }

    mapVariables(f: (v: V) => V): this {
        return new Operator(this.operator, ...this.terms.map(t => t.mapVariables(f))) as this;
    }
}

// TODO: Make a Term parser.
// TODO: Structural equality.
// TODO: fromJson

/* Formulas *********************************************************************************************************************************************************/

interface GenericFormula<V, P, C, Q, T extends ToJson & FreeVariables<V>> extends ToJson, FreeVariables<V> {
    match<A>(predicateCase: (predicate: P, ...terms: Array<T>) => A,
             nullaryCase: (connective: C) => A,
             unaryCase: (connective: C, formula: GenericFormula<V, P, C, Q, T>) => A,
             binaryCase: (leftFormula: GenericFormula<V, P, C, Q, T>, connective: C, rightFormula: GenericFormula<V, P, C, Q, T>) => A,
             quantifierCase: (quantifier: Q, v: V, formula: GenericFormula<V, P, C, Q, T>) => A): A;
}

class Predicate<V, P, C, Q, T extends ToJson & FreeVariables<V>> implements GenericFormula<V, P, C, Q, T> {
    readonly terms: Array<T>;
    constructor(readonly predicate: P, ...ts: Array<T>) { this.terms = ts; }
    match<A>(predicateCase: (predicate: P, ...terms: Array<T>) => A,
             nullaryCase: (connective: C) => A,
             unaryCase: (connective: C, formula: GenericFormula<V, P, C, Q, T>) => A,
             binaryCase: (leftFormula: GenericFormula<V, P, C, Q, T>, connective: C, rightFormula: GenericFormula<V, P, C, Q, T>) => A,
             quantifierCase: (quantifier: Q, v: V, formula: GenericFormula<V, P, C, Q, T>) => A): A {
        return predicateCase(this.predicate, ...this.terms);
    }

    toJson(): Json {
        return {predicate: this.predicate, args: this.terms.map(t => t.toJson())};
    }

    freeVariables(): Set<V> {
        return Set.union(this.terms.map(t => t.freeVariables()));
    }

    mapVariables(f: (v: V) => V): this {
        return new Predicate(this.predicate, ...this.terms.map(t => t.mapVariables(f))) as this;
    }
}

class NullaryConnective<V, P, C, Q, T extends ToJson & FreeVariables<V>> implements GenericFormula<V, P, C, Q, T> {
    constructor(readonly connective: C) { }
    match<A>(predicateCase: (predicate: P, ...terms: Array<T>) => A,
             nullaryCase: (connective: C) => A,
             unaryCase: (connective: C, formula: GenericFormula<V, P, C, Q, T>) => A,
             binaryCase: (leftFormula: GenericFormula<V, P, C, Q, T>, connective: C, rightFormula: GenericFormula<V, P, C, Q, T>) => A,
             quantifierCase: (quantifier: Q, v: V, formula: GenericFormula<V, P, C, Q, T>) => A): A {
        return nullaryCase(this.connective);
    }

    toJson(): Json {
        return {connective: this.connective};
    }

    freeVariables(): Set<V> {
        return Set();
    }

    mapVariables(f: (v: V) => V): this { return this; }
}

class UnaryConnective<V, P, C, Q, T extends ToJson & FreeVariables<V>> implements GenericFormula<V, P, C, Q, T> {
    constructor(readonly connective: C, readonly formula: GenericFormula<V, P, C, Q , T>) { }
    match<A>(predicateCase: (predicate: P, ...terms: Array<T>) => A,
             nullaryCase: (connective: C) => A,
             unaryCase: (connective: C, formula: GenericFormula<V, P, C, Q, T>) => A,
             binaryCase: (leftFormula: GenericFormula<V, P, C, Q, T>, connective: C, rightFormula: GenericFormula<V, P, C, Q, T>) => A,
             quantifierCase: (quantifier: Q, v: V, formula: GenericFormula<V, P, C, Q, T>) => A): A {
        return unaryCase(this.connective, this.formula);
    }

    toJson(): Json {
        return {connective: this.connective, right: this.formula.toJson()};
    }

    freeVariables(): Set<V> {
        return this.formula.freeVariables();
    }

    mapVariables(f: (v: V) => V): this {
        return new UnaryConnective(this.connective, this.formula.mapVariables(f)) as this;
    }
}

class BinaryConnective<V, P, C, Q, T extends ToJson & FreeVariables<V>> implements GenericFormula<V, P, C, Q, T> {
    constructor(readonly leftFormula: GenericFormula<V, P, C, Q, T>, readonly connective: C, readonly rightFormula: GenericFormula<V, P, C, Q , T>) { }
    match<A>(predicateCase: (predicate: P, ...terms: Array<T>) => A,
             nullaryCase: (connective: C) => A,
             unaryCase: (connective: C, formula: GenericFormula<V, P, C, Q, T>) => A,
             binaryCase: (leftFormula: GenericFormula<V, P, C, Q, T>, connective: C, rightFormula: GenericFormula<V, P, C, Q, T>) => A,
             quantifierCase: (quantifier: Q, v: V, formula: GenericFormula<V, P, C, Q, T>) => A): A {
        return binaryCase(this.leftFormula, this.connective, this.rightFormula);
    }

    toJson(): Json {
        return {connective: this.connective, left: this.leftFormula.toJson(), right: this.rightFormula.toJson()};
    }

    freeVariables(): Set<V> {
        return this.leftFormula.freeVariables().union(this.rightFormula.freeVariables());
    }

    mapVariables(f: (v: V) => V): this {
        return new BinaryConnective(this.leftFormula.mapVariables(f), this.connective, this.rightFormula.mapVariables(f)) as this;
    }
}

class Quantifier<V, P, C, Q, T extends ToJson & FreeVariables<V>> implements GenericFormula<V, P, C, Q, T> {
    constructor(readonly quantifier: Q, readonly variable: V, readonly formula: GenericFormula<V, P, C, Q, T>) {}
    match<A>(predicateCase: (predicate: P, ...terms: Array<T>) => A,
             nullaryCase: (connective: C) => A,
             unaryCase: (connective: C, formula: GenericFormula<V, P, C, Q, T>) => A,
             binaryCase: (leftFormula: GenericFormula<V, P, C, Q, T>, connective: C, rightFormula: GenericFormula<V, P, C, Q, T>) => A,
             quantifierCase: (quantifier: Q, v: V, formula: GenericFormula<V, P, C, Q, T>) => A): A {
        return quantifierCase(this.quantifier, this.variable, this.formula);
    }

    toJson(): Json {
        return {quantifier: this.quantifier, variable: this.variable, formula: this.formula.toJson()};
    }

    freeVariables(): Set<V> {
        return this.formula.freeVariables().delete(this.variable);
    }

    mapVariables(f: (v: V) => V): this {
        return new Quantifier(this.quantifier, f(this.variable), this.formula.mapVariables(f)) as this;
    }
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
        return {premises: this.premises.map(p => p.toJson()), consequences: this.consequences.map(c => c.toJson())};
    }
}

// TODO: fromJson

/* Derivations ******************************************************************************************************************************************************/

interface GenericDerivation<G extends ToJson> extends ToJson {
    match<A>(openCase: (conclusion: G) => A, inferenceCase: (premises: Array<GenericDerivation<G>>, conclusion: G) => A): A;
    conclusion: G;
}

class OpenDerivation<G extends ToJson> implements GenericDerivation<G> {
    constructor(readonly conclusion:  G) {}
    match<A>(openCase: (conclusion: G) => A, inferenceCase: (premises: Array<GenericDerivation<G>>, conclusion: G) => A): A {
        return openCase(this.conclusion);
    }

    toJson(): Json {
        return {conclusion: this.conclusion.toJson()};
    }
}

class Inference<G extends ToJson> implements GenericDerivation<G> {
    constructor(readonly premises: Array<GenericDerivation<G>>, readonly conclusion: G) {}
    match<A>(openCase: (conclusion: G) => A, inferenceCase: (premises: Array<GenericDerivation<G>>, conclusion: G) => A): A {
        return inferenceCase(this.premises, this.conclusion);
    }

    toJson(): Json {
        return {conclusion: this.conclusion.toJson(), premises: this.premises.map(p => p.toJson())};
    }
}

// TODO: fromJson

/* Path *************************************************************************************************************************************************************/

interface Path {
    extend(branch: number): Path;
    toString(): string;
}

class StartPath implements Path {
    constructor(private readonly start: string) {}
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
    extend(premises: Array<SimpleDerivation>): SimpleDerivation;
    open(): SimpleDerivation;
    goal: SimpleGoal;
}

class GoalExtender implements DerivationExtender {
    constructor(readonly goal: SimpleGoal) {}
    extend(premises: Array<SimpleDerivation>): SimpleDerivation { return new Inference(premises, this.goal); }
    open(): SimpleDerivation { return new OpenDerivation(this.goal); }
}

class InferenceExtender implements DerivationExtender {
    constructor(
        private readonly left: Array<SimpleDerivation>,
        readonly goal: SimpleGoal,
        private readonly right: Array<SimpleDerivation>,
        private readonly extender: DerivationExtender) {}
    extend(premises: Array<SimpleDerivation>): SimpleDerivation {
        return this.extender.extend(this.left.concat(new Inference(premises, this.goal), this.right));
    }
    open(): SimpleDerivation {
        return this.extender.extend(this.left.concat(new OpenDerivation(this.goal), this.right));
    }
}

/* Rendering ********************************************************************************************************************************************************/

type SimpleTerm = GenericTerm<string, string>;
type SimpleFormula = GenericFormula<string, string, string, string, SimpleTerm>;
type SimpleGoal = GenericGoal<SimpleFormula>;
type SimpleDerivation = GenericDerivation<SimpleGoal>;

function renderTerm(t: SimpleTerm): string {
    return t.match<string>(
        v => v,
        (o, ...ts) => `${o}(${ts.map(renderTerm).join(', ')})`);
}

// TODO: Add precedence system.
function renderFormula(f: SimpleFormula, path: Path, inPremises: boolean, extender?: DerivationExtender): Element {
    const id = path.toString();
    if(extender !== void(0)) {
        const extraData = {extender: extender, formula: f, inPremises: inPremises};
        return f.match(
            (p, ...ts) => wire(f, id)`<div id="${id}" data=${extraData} class="formula topLevel">
                                            <span class="predicate">${p}${ts.length === 0 ? '' : `(${ts.map(renderTerm).join(', ')})`}</span>
                                      </div>`,
            c => wire(f, id)`<div id="${id}" data=${extraData} class="formula topLevel"><span class="connective nullary">${c}</span></div>`,
            (c, f) => wire(f, id)`<div id="${id}" data=${extraData} class="formula topLevel">
                                        <span class="connective unary">${c}</span>
                                        ${renderFormula(f, path.extend(1), inPremises)}
                                  </div>`,
            (lf, c, rf) => wire(f, id)`<div id="${id}" data=${extraData} class="formula topLevel">
                                            ${renderFormula(lf, path.extend(1), inPremises)}
                                            <span class="connective binary">${c}</span>
                                            ${renderFormula(rf, path.extend(2), inPremises)}
                                       </div>`,
            (q, v, f) => wire(f, id)`<div id="${id}" data=${extraData} class="formula topLevel quantifier">
                                        <span class="connective quantifier">${q}</span>
                                        <span class="boundVariable">${v}</span>
                                        <span class="quantifierSeparator">.</span>
                                        ${renderFormula(f, path.extend(1), inPremises)}
                                     </div>`);
    } else {
        return f.match(
            (p, ...ts) => wire(f, id)`<div id="${id}" class="formula">
                                        <span class="predicate">${p}${ts.length === 0 ? '' : `(${ts.map(renderTerm).join(', ')})`}</span>
                                      </div>`,
            c => wire(f, id)`<div id="${id}" class="formula"><span class="connective nullary">${c}</span></div>`,
            (c, f) => wire(f, id)`<div id="${id}" class="formula">(
                                        <span class="connective unary">${c}</span>
                                        ${renderFormula(f, path.extend(1), inPremises)}
                                  )</div>`,
            (lf, c, rf) => wire(f, id)`<div id="${id}" class="formula">(
                                            ${renderFormula(lf, path.extend(1), inPremises)}
                                            <span class="connective binary">${c}</span>
                                            ${renderFormula(rf, path.extend(2), inPremises)}
                                       )</div>`,
            (q, v, f) => wire(f, id)`<div id="${id}" class="formula quantifier">(
                                        <span class="connective quantifier">${q}</span>
                                        <span class="boundVariable">${v}</span>
                                        <span class="quantifierSeparator">.</span>
                                        ${renderFormula(f, path.extend(1), inPremises)}
                                     )</div>`);
    }
}

function renderGoal(g: SimpleGoal, path: Path, extender: DerivationExtender): Element {
    const id = path.toString();
    return g.match((ps, cs) => {
        const psLen = ps.length;
        const psLenm1 = psLen - 1;
        const csLenm1 = cs.length - 1;
        return wire(g, id)`<div id="${id}" class="goal">
            ${wire(ps, id)`<div id="${id+"premises"}" class="premises context">
                            ${ps.flatMap((p, i) => i === psLenm1 ? [renderFormula(p, path.extend(i), true, extender)] 
                                                                 : [renderFormula(p, path.extend(i), true, extender), wire()`, `])}
                       </div>`}
            <span class="turnstile" data=${{extender: extender}}>⊢</span>
            ${wire(cs, id)`<div id="${id+"consequences"}" class="consequences context">
                            ${cs.flatMap((c, i) => i === csLenm1 ? [renderFormula(c, path.extend(i+psLen), false, extender)]
                                                                 : [renderFormula(c, path.extend(i+psLen), false, extender), wire()`, `])}
                       </div>`}
            </div>`
    });
}

function renderDerivation(d: SimpleDerivation, path: Path, extender: DerivationExtender, first: boolean = true): Element {
    const id = path.toString();
    const classes = first ? "derivation first" : "derivation";
    return d.match(
        c => wire(d, id)`<div id="${id}" class="${classes + ' open'}">${renderGoal(c, path, extender)}</div>`,
        (ps, c) => 
            wire(d, id)`<div id="${id}" class="${classes + ' closed'}">
                            <div class="row rulePremise">
                                ${ps.map((p, i) => {
                                    const newExtender = new InferenceExtender(
                                                                ps.slice(0, i),
                                                                p.conclusion,
                                                                ps.slice(i+1),
                                                                extender);
                                    return renderDerivation(p, path.extend(i), newExtender, i === 0);
                                 })}
                            </div>
                            <div class="row ruleConclusion">
                                ${renderGoal(c, path, extender)}
                            </div>
                        </div>`);
}

/* Helpers **********************************************************************************************************************************************************/

const BOT_SYMBOL = '⊥';
const TOP_SYMBOL = '⊤';
const NOT_SYMBOL = '¬';
const AND_SYMBOL = '∧';
const OR_SYMBOL = '∨';
const IMP_SYMBOL = '⇒';

const bot: SimpleFormula = new NullaryConnective<string, string, string, string, SimpleTerm>(BOT_SYMBOL);
const top: SimpleFormula = new NullaryConnective<string, string, string, string, SimpleTerm>(TOP_SYMBOL);

function not(f: SimpleFormula): SimpleFormula {
    return new UnaryConnective<string, string, string, string, SimpleTerm>(NOT_SYMBOL, f);
}

function and(lf: SimpleFormula, rf: SimpleFormula): SimpleFormula {
    return new BinaryConnective<string, string, string, string, SimpleTerm>(lf, AND_SYMBOL, rf);
}

function or(lf: SimpleFormula, rf: SimpleFormula): SimpleFormula {
    return new BinaryConnective<string, string, string, string, SimpleTerm>(lf, OR_SYMBOL, rf);
}

function implies(lf: SimpleFormula, rf: SimpleFormula): SimpleFormula {
    return new BinaryConnective<string, string, string, string, SimpleTerm>(lf, IMP_SYMBOL, rf);
}

function open(conclusion: SimpleGoal): SimpleDerivation { return new OpenDerivation<SimpleGoal>(conclusion); }

function entails(premises: Array<SimpleFormula>, consequences: Array<SimpleFormula>): Goal<SimpleFormula> {
    return new Goal<SimpleFormula>(premises, consequences);
}

function infers(premises: Array<SimpleDerivation>, conclusion: SimpleGoal): Inference<SimpleGoal> {
    return new Inference<SimpleGoal>(premises, conclusion);
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
        newGoalsCase: (goals: Array<SimpleGoal>) => A,
        contractOrInstantiateCase: (goal: SimpleGoal, formula: SimpleFormula, inPremises: boolean) => A): A;
}

class NewGoals implements OutputEvent {
    constructor(readonly goals: Array<SimpleGoal>) {}
    match<A>(
      newGoalsCase: (goals: Array<SimpleGoal>) => A,
      contractOrInstantiateCase: (goal: SimpleGoal, formula: SimpleFormula, inPremises: boolean) => A): A {
        return newGoalsCase(this.goals);
    }
}

class ContractOrInstantiate implements OutputEvent {
    constructor(readonly goal: SimpleGoal, readonly formula: SimpleFormula, readonly inPremises: boolean) {}
    match<A>(
      newGoalsCase: (goals: Array<SimpleGoal>) => A,
      contractOrInstantiateCase: (goal: SimpleGoal, formula: SimpleFormula, inPremises: boolean) => A): A {
        return contractOrInstantiateCase(this.goal, this.formula, this.inPremises);
    }
}

/* Logic ************************************************************************************************************************************************************/

type Logic = (input: InputEvent) => OutputEvent;

const classicalSequentCalculus: Logic = (input) => input.match(
    (goal, formula, inPremises) => formula.match( // TODO: Refactor and finish.
        (predicate, ...terms) => { throw 'Not implemented yet.'; },
        connective => { throw 'Not implemented yet.'; },
        (connective, formula) => { throw 'Not implemented yet.'; },
        (lf, connective, rf) => { 
            switch(connective) {
                case AND_SYMBOL:
                    if(inPremises) { // TODO: Remove old formula.
                        return new NewGoals([new Goal(goal.premises.filter(f => f !== formula).concat(lf,rf), goal.consequences)]);
                    } else {
                        const cs = goal.consequences.filter(f => f !== formula);
                        return new NewGoals([new Goal(goal.premises, cs.concat(lf)),
                                             new Goal(goal.premises, cs.concat(rf))]);
                    }
                default: 
                    throw 'Not implemented yet.'; 
            }
        },
        (quantifier, v, formula) => { throw 'Not implemented yet.'; }),
    (goal, formula, inPremises) => new NewGoals([inPremises ? new Goal(goal.premises, goal.consequences.concat(formula))
                                                            : new Goal(goal.premises.concat(formula), goal.consequences)]),
    (goal, formula, inPremises, term) => { throw 'Not implemented yet.'; });

/* Main *************************************************************************************************************************************************************/

const A = new Predicate<string, string, string, string, SimpleTerm>('A'); 
const B = new Predicate<string, string, string, string, SimpleTerm>('B'); 

let example: SimpleDerivation = infers([open(entails([A,B], [not(A)])), infers([], entails([A,B], [B]))], entails([A, B], [and(A, B)]));

const container = document.getElementById('container');
if(container === null) throw 'Container missing.';

const refresh = () => {
    bind(container)`${renderDerivation(example, new StartPath(':root.'), new GoalExtender(example.conclusion))}`; // NOTE: StartPath MUST start with colon.
};

const onClick = (event: MouseEvent) => {
    const target: any = event.target;
    let extraData = target.data as {extender: DerivationExtender, formula?: SimpleFormula, inPremises?: boolean};
    if(target.data === void(0)) {
        extraData = target.closest('.topLevel').data;
    }

    if(extraData.formula === void(0)) {
        example = extraData.extender.open();
    } else {
        const output = classicalSequentCalculus(new ApplyTactic(extraData.extender.goal, extraData.formula, extraData.inPremises!!));
        example = output.match(
            goals => extraData.extender.extend(goals.map(g => new OpenDerivation(g))),
            (goal, formula, inPremises) => { throw 'Not implemented yet.'; }); // TODO
    }
    refresh();
};

runEffects(tap(onClick, click(container, true)), newDefaultScheduler());

refresh();
