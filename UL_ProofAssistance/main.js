

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

// let rule1 = pf.genRule('! , #4 2 , #3 2 , #4 1 , #4 2 , @, #4 2 , #4 1 , #3 2 , #4 2 , ') 
// let rule2 = pf.genRule('!  , #3 1 , #4 2 , @ , #4 2 , #3 1 ,') 
// console.log(pf.isRule(rule2))
// console.log(pf.MatchandCheck(rule1.leftexps, rule1.rightexps))
// let branchexp = pf.genRule('!, #3 1, #102 $1 $2 #15 1 2, #6 1 , #10 1 , #7 1, @ ,').leftexps

// console.log(pf.ExpToString(rule1.leftexps), pf.ExpToString(rule1.rightexps), pf.MatchandCheck(rule1.leftexps, rule1.rightexps))

// let t = pf.genRule('!,@, #7 1 2 , #4 3 ,').rightexps
// for(const a of pf.getAllSubExps(rule1.leftexps)){
//     console.log(pf.ExpToString(a[0]),pf.ExpToString(a[1]),pf.ExpToString(a[2]))
//     // console.log(a[0],a[1],a[2])
// }
let ps = new ProofStrategy(pf, tstatements, allexps)
ps.Init()
