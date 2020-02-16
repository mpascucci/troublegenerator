// UTILITY FUNCTIONS
class CustomError extends Error {
    constructor(message: string) {super(message);}
}

function assert(condition: boolean, message: string) {
    if (!condition) {
        throw new CustomError(message);
    }
}

function randomChoice(choices: any[]) {
    let index : number;
    index = Math.floor(Math.random() * choices.length);
    return choices[index];
}

function shuffle(array) {
    var currentIndex = array.length, temporaryValue, randomIndex;
  
    // While there remain elements to shuffle...
    while (0 !== currentIndex) {
  
      // Pick a remaining element...
      randomIndex = Math.floor(Math.random() * currentIndex);
      currentIndex -= 1;
  
      // And swap it with the current element.
      temporaryValue = array[currentIndex];
      array[currentIndex] = array[randomIndex];
      array[randomIndex] = temporaryValue;
    }
    return array;
  }

function sample(choices: any[], k:number=1) {
    let rest = shuffle(choices);
    let sample = rest.splice(0,k);
    return [sample, rest];
}

function is_in(x : any, list: any[]) : boolean {
    // return true if x in list
    return list.indexOf(x) >= 0;
}

// INTERFACES


interface Rule {
    name : string; 
    arity : number;
    premises : string[];
    conclusion : string;
    conj? : string;
    is_applicable(premises : Sequent[]) : {value:boolean, message:string};
    apply(premises : Sequent[]) : Sequent; 
}

interface Formula{
    content : string;
}

interface Sequent {
    content : Formula[];
}

// interface Connective {
//     arity : number;     // the arity of the connective
//     symbol : string;    // the symbol of the connective
// }

class Sequent implements Sequent{
    constructor(public content : Formula []) {};
    public toString() : string {
        let contents:string[] = [];
        for (let i = 0; i<this.content.length; i++) {
            contents.push(this.content[i].content);
        }
        return contents.join(',');
    }
    public copy() {
        let contents: Formula[] = []
        for (let i = 0; i<this.content.length; i++) {
            contents.push(this.content[i].copy());
        }
        return new Sequent(contents);
    }
}

class Formula implements Formula{
    constructor(public content : string) {};
    public copy(){
        return new Formula(this.content);
    }
}

abstract class BasicRule implements Rule {
    arity : number;
    constructor( public name: string, public premises : string[], public conclusion : string) {
        this.arity = this.premises.length;
    };
    // the rule can be applied given certain premises
    public abstract is_applicable(premises : Sequent[]) : {value:boolean, message:string};
    public abstract apply(premises : Sequent[]) : Sequent;
    public toString() : string {
        return `${this.name}: ${this.premises} >>> ${this.conclusion}`
    }
}

// class Connective implements Connective {
//     constructor(public symbol: string, public arity: number) {
//         assert(this.arity === 1 || this.arity === 2 , "the arity of a connective must be 1 or 2");
//     }
//     public apply(args: Formula[]) : Formula {
//         assert(args.length === this.arity, "wrong number of arguments for connective.");
//         if (this.arity === 1){
//             return new Formula(this.symbol + args[0].content);
//         } else if (this.arity === 2){
//             return new Formula(args[0].content + this.symbol + args[1].content);
//         }
//     }
// }

class ContextPreservingRule extends BasicRule {
    // a rule that modifies only the active formulas in the premises
    // and leaves the context unchanged
    constructor( name: string, premises : string[], conclusion : string) {
        super(name, premises, conclusion);

        // check that the active formula has only one connective
        // let re = /[^\w,;]/g;
        // let symbols = this.conclusion.match(re);
        // if (symbols.length > 1){ 
        //     throw Error("more than one connective");
        // }
    };
    public is_applicable(premises : Sequent[]) {
        // the number of given sequents in the premises corresponds to the rule arity.
        let rule_arity_check:boolean = premises.length === this.arity;
        if (!rule_arity_check){
            return { value : false, message :`wrong number of sequents (${premises.length}) for rule arity (${this.arity})` };
        }

        let n_formulae : number = 0;
        for (let k in premises) {
            n_formulae += premises[k].content.length;
        }
        // there are enough formulae for the arity of the connective
        if (n_formulae < this.conclusion.match(/\w+/g).length){
            return { value : false, message :"not enough input formulae for conclusion" };
        }

        return { value : true, message :"" };
    }
    public apply(premises: Sequent[]) : Sequent{
        let contexts = {};
        let activeVars = {};
        let context_name : string;
        let active_form_names : string[];
        let premise : string;
        let name : string;
        let idx : number;
        
        let prems = [];
        // COPY the premises
        for (let i = 0; i < this.premises.length; i++){
            prems[i] = premises[i].copy();
        }
        
        // associate the given premises to the rule's symbols
        for (let i = 0; i < this.premises.length; i++){
            premise = this.premises[i];
            context_name = premise.split(';')[0];
            active_form_names = premise.split(';')[1].split(',');
        
            for (let j = 0; j < active_form_names.length; j++){
                name = active_form_names[j];
                idx = prems[i].content.length-1; // take the last formula
                activeVars[name] = prems[i].content.splice(idx,1)[0];
            }
            contexts[context_name] = prems[i].content;
        }
        
        // interpret rule conclusion
        let conclusion_context_names:string[] = this.conclusion.split(';')[0].split(',');
        let principal_formula_names:string[] = this.conclusion.split(';')[1].match(/\w+/g);
        let conclusion_context: Formula[] = [];

        // copy the contexts (unchanged)
        for (let i = 0; i < conclusion_context_names.length; i++){
            name = conclusion_context_names[i];
            conclusion_context = conclusion_context.concat(contexts[name]);
        }

        let principal_formula_args : Formula[] = [];
        for (let i = 0; i < principal_formula_names.length; i++){
            name = principal_formula_names[i];
            if (name != undefined) {
                principal_formula_args.push(activeVars[name]);
                // console.log(">>>", name, activeVars[name], principal_formula_names);
            }
        }

        // CONCLUSION: substitute symbols with formulas
        let s = this.conclusion.split(';')[1];
        for (let word in activeVars){
            // console.log(word,activeVars[word]);
            s = s.replace(word,activeVars[word].content);
        }
        let principal_formula:Formula = new Formula(s);
        principal_formula.content = `(${principal_formula.content})`;
        let conclusion = conclusion_context
        conclusion.push(principal_formula);
        return new Sequent(conclusion);
    }
}

function applyRule(r: Rule, premises : Sequent[]): Sequent[] {
    try {
        let is_app = r.is_applicable(premises);
        if (!is_app.value) {
            let msg = `the rule ${r.name} is not applicable: ${is_app.message}`;
            throw Error(msg);
        }
        return [r.apply(premises)];
    } catch (e) {
        // console.log("rule:", r.toString(), premises);
        // console.log("Applicability:", r.is_applicable(premises));
        // console.log(e);
        return premises;
    }
}

function randomConclusion(sequents:Sequent[], rules:Rule[]) : Sequent{
    // copy leaves
    let leaves : Sequent[] = [];
    for (let i = 0; i < sequents.length; i++){
        leaves.push(sequents[i].copy());
    } 
    while (leaves.length > 1){
        rule = randomChoice(rules);
        if (rule.arity > leaves.length) continue;
        let res = sample(leaves, rule.arity);
        let premises = res[0];

        // shuffle the formulae
        for (let i = 0; i < premises.length; i++){
            premises[i].content = shuffle(premises[i].content);
        }

        let rest = res[1];
        leaves = rest.concat(applyRule(rule, premises));
    }
    return leaves[0];
}

let r1 = new ContextPreservingRule("dollar", ["G;A","D;B"], "G,D;A$B");
let r2 = new ContextPreservingRule("percent", ["G;A"], "G;%A");
let r3 = new ContextPreservingRule("bar", ["C;A,B"], "C;A|B");


let a = new Formula("a");
let b = new Formula("b");
let c = new Formula("c");
let d = new Formula("d");
let e = new Formula("e");
let f = new Formula("f");
let s1 = new Sequent([a,b]);
let s2 = new Sequent([c,d]);
let s3 = new Sequent([e,f]);

let leaves = [s1,s2,s3];
let rules = [r1,r2,r3];

let rule : Rule;
let premises,rest : Sequent[];

console.log("Leaves:");
for (let i in leaves) console.log(leaves[i].toString());
console.log("");

console.log("Rules:");
for (let r in rules) console.log(rules[r].toString());
console.log("");

console.log("Random conclusions:");
let trouble:Sequent
for (let i=0; i<10; i++){
    trouble = randomConclusion(leaves, rules);
    console.log(trouble.toString());
}

// let a1 = new Formula("a");
// let a2 = new Formula("b");
// let test = new Sequent([a1]);
// console.log(applyRule(r3, [test]));