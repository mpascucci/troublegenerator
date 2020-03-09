// UTILITY FUNCTIONS
class CustomError extends Error {
  constructor(message: string) { super(message); }
}

function assert(condition: boolean, message: string) {
  if (!condition) {
      throw new CustomError(message);
  }
}

function randomChoice(choices: any[]) {
  let index: number;
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

function sample(choices: any[], k: number = 1) {
  let rest = shuffle(choices);
  let sample = rest.splice(0, k);
  return [sample, rest];
}

function is_in(x: any, list: any[]): boolean {
  // return true if x in list
  return list.indexOf(x) >= 0;
}

// INTERFACES
interface Formula {
  symbol: string;
  negative: boolean;
}

class Formula implements Formula {
  constructor(public symbol: string, public negative: boolean) { };
  public copy() {
      return new Formula(this.symbol,this.negative);
  }
}

interface Sequent {
  formulas: Formula[];
}

class Sequent implements Sequent {
  constructor(public formulas: Formula[]) { };
  public copy() {
      let contents: Formula[] = []
      for (let i = 0; i < this.formulas.length; i++) {
          contents.push(this.formulas[i].copy());
      }
      return new Sequent(contents);
  }
}

function get_common_formulas(s1: Sequent, s2: Sequent) {
  // get the repeated symbols in two sequents (identical and negated)
  let same = [];
  let opposed = [];
  for (const i in s1.formulas) {
    let f1 = s1.formulas[i];
    for (const j in s2.formulas) {
      let f2 = s2.formulas[j];
      if (f2.symbol === f1.symbol) {
        if (f1.negative == f2.negative) {
          same.push(f1.symbol);
        } else {
          opposed.push(f1.symbol);
        }
      }
    }
  }
  return { same: same, opposed: opposed };
}

function parse_formula_symbol(s: string) {
  // parse a formula symbol and if it is negated
  let re = /(~?)(.+)/;
  let matchresult = s.match(re);
  let negative = matchresult[1] === '~';
  let symbol = matchresult[2];
  return new Formula(symbol, negative);
}

function generateLeave(axiom, alphabet, shuffleAlphapet=false) {
  // generate n leaves with the given axiom
  let this_alphabet = alphabet.slice(); // copy
  if (shuffleAlphapet) {
    this_alphabet = shuffle(this_alphabet);
  }
  let associations = {};

  let formulas = [];
  for (const i in axiom.consequences[0].active) {
    let c = axiom.consequences[0].active[i];
    let parsed = parse_formula_symbol(c);
    let negative = parsed.negative;
    let symbol = parsed.symbol;

    // chose a random letter and remove it from the alphabet
    if (this_alphabet.length == 0) {
      throw (new CustomError(`too many unique formulas in axiom "${axiom.name}"`));
    }
    let re = /([A-Z])/
    let m = symbol.match(re);
    while (m) {
      if (!associations[m[0]]) {
        associations[m[0]] = this_alphabet.pop();
      }
      symbol = symbol.replace(m[0],associations[m[0]])
      m = symbol.match(re);
    }

    formulas.push(new Formula(symbol, negative))
  }
  return new Sequent(formulas);
}

function removeFormula(s: string, fs: Formula[]) {
  let outFormulas = [];
  for (const i in fs) {
    if (fs[i].symbol !== s) {
      outFormulas.push(fs[i]);
    };
  }
  return outFormulas;
}

function formulaToSymbol(f: Formula) {
  return f.negative ? `~${f.symbol}` : f.symbol;
}
function sequentToString(s: Sequent) {
  let out = [];
  for (const i in s.formulas) {
    out.push(formulaToSymbol(s.formulas[i]));
  }
  return out.join(",");
}

function applyBinaryRule(rule, s1: Sequent, s2: Sequent) {
  // fare il check sulle condizioni
  s1 = s1.copy();
  s2 = s2.copy();
  let applicable = true;
  let result = null;
  if ((rule.premises[0].active.length > s1.formulas.length) ||
    (rule.premises[1].active.length > s1.formulas.length)) {
    //not enough formulas;
    applicable = false;
    return { is_applicable: applicable, result: result };
  }

  // CHECK CONDITIONS
  let cf = get_common_formulas(s1, s2); //common formulas in sequents s1, s2
  let af1: Formula[] = [];
  let af2: Formula[] = [];
  for (const i in rule.premises[0].active) {
    let f1 = parse_formula_symbol(rule.premises[0].active[i]);
    af1.push(f1);
  }
  for (const i in rule.premises[0].active) {
    let f2 = parse_formula_symbol(rule.premises[1].active[i]);
    af2.push(f2);
  }

  //common symbols in rule
  let cs = get_common_formulas(new Sequent(af1), new Sequent(af2));

  applicable = ((cs.opposed.length <= cf.opposed.length) &&
    (cs.same.length <= cf.same.length));

  if (applicable) {
    // remove the common symbols from the sequents
    // and remember the substitution
    let substitutions = {};
    for (const i in cs.opposed) {
      substitutions[cs.opposed[i]] = cf.opposed[i];
    }
    for (const i in cs.same) {
      substitutions[cs.same[i]] = cf.same[i];
    }
    for (const k in substitutions) {
      let s = substitutions[k];
      s1.formulas = removeFormula(s, s1.formulas);
      s2.formulas = removeFormula(s, s2.formulas);
    }

    // split context and active rules
    s1.formulas = shuffle(s1.formulas);
    s2.formulas = shuffle(s2.formulas);
    for (const i in af1) {
      let k = af1[i].symbol;
      if (!(k in substitutions)) {
        substitutions[k] = formulaToSymbol(s1.formulas.pop());
      }
    }
    for (const i in af2) {
      let k = af2[i].symbol;
      if (!(k in substitutions)) {
        substitutions[k] = formulaToSymbol(s2.formulas.pop());
      }
    }
    substitutions[rule.premises[0].context[0]] = sequentToString(s1);
    substitutions[rule.premises[1].context[0]] = sequentToString(s2);

    // apply the rule
    let cons = rule.consequences[0]
    cons = cons.context.concat(cons.active);
    let out = [];
    for (const i in cons) {
      for (const j in substitutions) {
        let v = substitutions[j];
        cons[i] = cons[i].replace(j,v);
      }
      // console.log(cons[i]);
      if (cons[i]) out.push(cons[i])
    }
    result = out.join(",");

  }


  return { is_applicable: applicable, result: result }
}

function applyRule(rule, premises: Sequent[]) {
  let arity = rule.premises.length
  assert(arity > 0 && arity <= 2, "arity must be 1 or 2");
  assert(arity == premises.length, "rule has wrong arity");
  assert(rule.consequences.length === 1, "only one sequent allowed in consequence");
  if (arity === 2) {
    return applyBinaryRule(rule, premises[0], premises[1]);
  } else if (arity === 1) {
    throw new CustomError("unary rules not implemented yet");
  }
}

function applyRandomRule(rules, leaves:Sequent[]) {
  let rule = sample(rules,1)[0][0];
  let arity = rule.premises.length;

  let premises:Sequent[] = [];
  for (let i=0; i<arity; i++) {
    premises.push(shuffle(leaves).pop());
  }

  let result = applyRule(rule,premises);
  // console.log(result);
  return {rule:rule.name, premises:premises, result:result.result};

  
}


function test() {

  let axiom = {
    "type": "axiom",
    "name": "axiom",
    "premises": [],
    "consequences": [
      {
        "type": "sequent",
        "context": [],
        "active": [
          "A",
          "~A"
        ]
      }
    ]
  }

  // let rule = {
  //   "type": "rule",
  //   "name": "cut",
  //   "premises": [
  //     {
  //       "type": "sequent",
  //       "context": [
  //         "C"
  //       ],
  //       "active": [
  //         "A"
  //       ]
  //     },
  //     {
  //       "type": "sequent",
  //       "context": [
  //         "D"
  //       ],
  //       "active": [
  //         "~A"
  //       ]
  //     }
  //   ],
  //   "consequences": [
  //     {
  //       "type": "sequent",
  //       "context": [],
  //       "active": [
  //         "C",
  //         "D"
  //       ]
  //     }
  //   ]
  // }
  let rule2 = {
    "type": "rule",
    "name": "cut",
    "premises": [
      {
        "type": "sequent",
        "context": [
          "C"
        ],
        "active": [
          "A"
        ]
      }
    ],
    "consequences": [
      {
        "type": "sequent",
        "context": [
          "C"
        ],
        "active": [
          "~A"
        ]
      }
    ]
  }

  let alphabet = ['a', 'b', 'c', 'd', 'e', 'f', 'g', 'h', 'i', 'j', 'k'];
  // let leaves = []; 
  // for (let i=0; i<3; i++) {
  //   leaves.push(generateLeave(axiom, alphabet,false));
  // }
  // console.log(leaves[2]);
 

  let s1 = new Sequent([
    new Formula('a',true),
    new Formula('a',false),
    // new Formula('u',true)
  ]);

  // let s2 = new Sequent([
  //   new Formula('a',true),
  //   new Formula('d',true)
  // ]);

  // console.log(get_common_formulas(s1,s2));
  console.log(applyRule(rule2,[s1]));
  // console.log(formulaToSymbol(s1.formulas[1]));
  // console.log(applyRandomRule([rule,rule],[s1,s2]));
  // console.log(
  //   generateLeave(axiom, alphabet, false)
  // );
}
test();