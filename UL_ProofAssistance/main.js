
import fs from 'fs'

import ProofAssistant from "./ProofAssistant.js";
import LatexParser from  "./LatexParser.js"
import {subexptest, subexpbranchtest} from "./tests.js"
import ProofStrategy from  './ProofStrategy.js';


//Load axioms and get all beginning expression in theorems
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
let ps = new ProofStrategy(pf, tstatements.slice(0,1), allexps)

// pf.PrintAllRules()
// ps.Init()


let rule = latexparser.Parse('!,#3 3, #4 3, @ , #4 3, #3 3, ')
let ind = latexparser.Parse('!, #3 3 , #4 3 , #7 1 2 , #4 3 , @ , #4 3 , #3 3 , #7 1 2 , #4 3 , ')
let sub = latexparser.Parse('!, @ , #3 3, #4 3, ').rightexps


// let x = pf.GetAllOperandsVariance(check.leftexps, rule.rightexps, rule.leftexps)
// for(const l of x){
//     console.log('rule left: ', pf.ExpToString(l[0]), 'rule right: ', pf.ExpToString(l[1]))
// }


// let result = pf.MatchandCheck(ind.leftexps, ind.rightexps)
let result = pf.Check(rule.rightexps, [sub, 0], ind.leftexps, ind.rightexps, true)
console.log(result)