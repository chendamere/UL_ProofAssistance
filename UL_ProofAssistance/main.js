

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
// console.log(allexps[0].length, tstatements[0].length)
let pf = new ProofAssistant(allrules, latexparser, [])
// let r = latexparser.Parse('!, #100 $1 $1 #15 1 3, @,  #100 $1 $1 #15 1 3,')
// console.log(pf.Same(r.leftexps,r.rightexps))
// console.log(latexparser.branch)

// let t = pf.genRule('! , #4 1 , #101 $2 $2 #10 2 3 , #3 1 , #4 1 , #3 1 , #4 1 , @ , #4 1 , #3 1 , #101 $1 $1 #10 2 3 , #4 1 , #4 1 ,')
// let x = pf.TrimBranch2(t.leftexps,t.rightexps)

let t1 = pf.genRule('! , #4 1 , #101 $2 $2 #10 2 3 , #3 1 , #4 1 , #3 1 , #101 $1 $1 #10 2 3 , #4 1 , #4 1 , @ , #4 1 , #3 1 , #101 $1 $1 #10 2 3 , #4 1 , #101 $1 $1 #10 2 3 , #4 1 , #4 1 ,')
// let t2 = pf.genRule('! ,#101 $1 $2 #10 2 3 ,#4 1 , #4 1 , #101 $1 $1 #10 2 3 , #4 1 , #4 1 , @ , #4 1 , #101 $0 $1 #10 2 3 , #101 $1 $1 #10 2 3 , #4 1 , #4 1 ,')
// let t3 = pf.genRule('! ,#101 $2 $2 #10 2 3 ,#4 1 , #101 $1 $1 #10 2 3 , #4 1 , #4 1 , #4 1 , #101 $1 $1 #10 2 3 , #4 1 , #4 1 , @ , #4 1 , #101 $1 $1 #10 2 3 , #101 $1 $1 #10 2 3 , #4 1 , #4 1 ,#101 $1 $1 #10 2 3 , #4 1 , #4 1 ,')
// let t3 = pf.genRule('! #4 1 ,#101 $2 $2 #10 2 3 ,#4 1 , #101 $1 $1 #10 2 3 , #4 1 , #4 1 , #4 1 , #101 $1 $1 #10 2 3 , #4 1 , #4 1 , @ , #4 1 , #4 1 , #101 $1 $1 #10 2 3 , #101 $1 $1 #10 2 3 , #4 1 , #4 1 ,#101 $1 $1 #10 2 3 , #4 1 , #4 1 ,')

// let lastbr = pf.getLastBr(t1.leftexps)
// console.log(lastbr)

let x1 = pf.TrimBranchFront(t1.leftexps,t1.rightexps)

// let x2 = pf.TrimBranchBack(x1[0], x1[1])
// console.log(pf.getFirstBr(t3.leftexps))
// let gettopbotexample = pf.getTopBot(t3.leftexps, pf.getFirstBr(t3.leftexps))
// console.log(pf.ExpToString(gettopbotexample[0]),'!', pf.ExpToString(gettopbotexample[1]))
console.log(pf.ExpToString(x1[0]),pf.ExpToString(x1[1]))

// console.log(pf.ExpToString(x1[0])+'@'+pf.ExpToString(x1[1]))
// let y = pf.parser.RuleNormalize('')
// console.log(x)

// console.log(pf.Trim2(x.leftexps, x.rightexps))
// pf.PrintAllRules()
// console.log(pf.isRule(pf.genRule('!,#0,@, #100 $0 $0 #10 1 2 ,')))
// console.log(pf.isRule(pf.genRule('! , #15 1 2 , @ , #15 2 1 ,')))
// let ps = new ProofStrategy(pf, tstatements, allexps)
// ps.Init()

// console.log(pf.isRule( pf.genRule('!,#11, @, #0,')))

// console.log(latexparser.branch)
// console.log(pf.parser.branch)
// console.log(latexparser.unaryOperators)
// console.log(latexparser.binaryOperators)