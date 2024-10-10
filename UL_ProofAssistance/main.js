

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
// console.log(allexps[0])
// // console.log(allexps[0].length, tstatements[0].length)
let pf = new ProofAssistant(allrules, latexparser, [])
// console.log(allexps)

let ps = new ProofStrategy(pf, tstatements, allexps)
ps.Init()

// pf.PrintAllRules()

// console.log(latexparser.branch)
// console.log(pf.parser.branch)
// console.log(latexparser.unaryOperators)
// console.log(latexparser.binaryOperators)