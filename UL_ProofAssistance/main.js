

// focus on what to manipulate

// const net = new brain.NeuralNetwork();

// net.train([
//   { input: { r: 0.03, g: 0.7, b: 0.5 }, output: { black: 1 } },
//   { input: { r: 0.16, g: 0.09, b: 0.2 }, output: { white: 1 } },
//   { input: { r: 0.5, g: 0.5, b: 1.0 }, output: { green: 1 } },
// ]);

// const output = net.run({ r: 1, g: 0.4, b: 0 }); // { white: 0.99, black: 0.002 }

// console.log(output)

import fs from 'fs'

import ProofAssistant from "./ProofAssistant.js";
import LatexParser from "./LatexParser.js";
import ProofStrategy from './ProofStrategy.js';

let latexparser = new LatexParser();
let allrules = [];

let tstatements = []
fs.readdirSync('./axiom/').forEach(file => {
    const chapter = latexparser.ParseFile( './axiom/', fs.readFileSync, file, false)
    for(const c of chapter.rules){
        let ret = latexparser.Parse(c)
        allrules.push(ret)
    }
})

let allexps = [];
fs.readdirSync('./theorems/').forEach(file => {
    let texps=[]
    let tts =[]
    let chapter = latexparser.ParseFile( './theorems/', fs.readFileSync, file, false)
    let exps = latexparser.trimExps(latexparser.ParseFile( './theorems/', fs.readFileSync, file, true))
    for(const e of exps){
        // console.log(e)
        let temp =[]
        for(const exp of e) {
            temp.push(exp.trim())
        }
        texps.push(temp)
    }
    for(const e of chapter.rules){
        tts.push(latexparser.Parse(e))
    }
    tstatements.push(tts)
    allexps.push(texps)
})

let pf = new ProofAssistant(allrules, latexparser, [])
// pf.PrintAllRules()

let rule1 = pf.genRule('!  , #100 $1 $2 #15 1 2 , #11 , #11 , #11 ,   @ , #100 $1 $1 #15 1 2 , #11 , #11 , ') 

// console.log(pf.RuleToString(pf.Operands_normalize(rule2)))
// console.log(pf.checkcv(rule22, rule2))
console.log(pf.MatchandCheck(rule1.leftexps, rule1.rightexps))
// console.log()

// let table = {}
// let x = pf.Operands_normalize_exps(rule1.leftexps, table)
// console.log(pf.ExpToString(x[0]))
// let x1 = pf.Operands_normalize_exps(rule2.leftexps, table)
// let x2 = pf.Operands_normalize_exps(rule2.rightexps, table)
// console.log(pf.ExpToString(x[0]), table )
// console.log(pf.flipKeyandValue(table))
// console.log(pf.ExpToString(x1[0]), table )
// console.log(pf.ExpToString(x2[0]), table )

// console.log(pf.getOperandSub(rule2.leftexps, rule2.rightexps))

// console.log(pf.ruleInBranch(rule6.leftexps,rule6.rightexps,rule5.leftexps))
// let r1 = pf.genRule('!,@,'+pf.ExpToString(rule2.leftexps))
// let s2 = pf.genRule('!,@,'+pf.ExpToString(rule2.rightexps))
// console.log(pf.checkcv(r1,s2))
// console.log(pf.ruleInBranch(rule2.leftexps, rule2.rightexps))
// for (const x of pf.getAllSubExps(rule7.leftexps)){
//     console.log(pf.ExpToString(x[0]),' --|',pf.ExpToString(x[1]),'|-- ',pf.ExpToString(x[2]))
// }

// let ps = new ProofStrategy(pf, tstatements, allexps)
// ps.Init()
// , #100 $1 $1 #10 1 2 , #100 $1 $1 #10 3 4 , #13 5 , #13 6 , #100 $1 $1 #10 3 4 , #13 7 , #13 8 , @ , #100 $1 $1 #10 3 4 , #100 $1 $1 #10 1 2 , #13 5 , #13 7 , #100 $1 $1 #10 1 2 , #13 6 , #13 8 ,

// , #100 $1 $1 #15 1 2 , #100 $1 $1 #15 3 4 , #13 5 , #13 6 , #100 $1 $1 #15 3 4 , #13 7 , #13 8 , @ , #100 $1 $1 #15 3 4 , #100 $1 $1 #15 1 2 , #13 5 , #13 7 , #100 $1 $1 #15 1 2 , #13 6 , #13 8 ,
// , #101 $0 $0 #10 1 2 , #101 $0 $0 #10 1 3 , @ , #101 $0 $0 #10 1 2 , #101 $0 $0 #10 2 3 ,


//rule : , #100 $1 $1 #10 1 2 , #100 $1 $1 #10 3 4 , #13 5 , #13 6 , #100 $1 $1 #10 3 4 , #13 7 , #13 8 , @ , #100 $1 $1 #10 3 4 , #100 $1 $1 #10 1 2 , #13 5 , #13 7 , #100 $1 $1 #10 1 2 , #13 6 , #13 8 ,