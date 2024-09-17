

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
        // console.log(c)
        let ret = latexparser.Parse(c)
        // console.log(ret)
        allrules.push(ret)
    }
})
let allexps = [];
fs.readdirSync('./theorems/').forEach(file => {
    let statmentexps = [latexparser.ParseFile( './theorems/', fs.readFileSync, file, true)]
    let c = latexparser.ParseFile( './theorems/', fs.readFileSync, file, false)
    const exps = latexparser.ChaptertoExps(statmentexps)
    for(const e of exps){
        allexps.push(e.trim())
    }
    for(const e of c.rules){
        tstatements.push(latexparser.Parse(e))
    }
})
let pf = new ProofAssistant(allrules, latexparser, allexps);
let ps = new ProofStrategy(pf, tstatements)
ps.Init()