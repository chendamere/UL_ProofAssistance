
import fs from 'fs'

import ProofAssistant from "./ProofAssistant.js";
import LatexParser from  "./LatexParser.js"
import {subexptest, subexpbranchtest, indtests} from "./tests.js"
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
let ps = new ProofStrategy(pf, tstatements.slice(0,2), allexps)

// pf.PrintAllRules()
// let assumedAxiom = ps.AxiomsUptoChapter(1)
// console.log(assumedAxiom.length)
// for(const r of assumedAxiom){
//     console.log(pf.RuleToString(r))
// }
// ps.ProveChapter(0)
// ps.ProveChapter(1)

p()
// f()


function f() { 

    for(const test of indtests.slice(indtests.length-1, indtests.length)){
        let rule = latexparser.Parse(test[0])
        let ind = latexparser.Parse(test[1])
        console.log('rule left: ', pf.ExpToString(rule.leftexps))
        console.log('ind left: ', pf.ExpToString(ind.leftexps))
        let [s1, s2] = pf.getsub(ind.leftexps)
        let allsub = s1.concat(s2)
        let subexps = pf.addEmpty(allsub)
        subexps = pf.sort_subexp(subexps)
        for(const sub of subexps){
            console.log(sub[1], pf.ExpToString(sub[0]))
            if(pf.Same(pf.cloneExp(rule.leftexps), sub[0])){
                console.log('index: ', sub[1], 'sub: ', pf.ExpToString(sub[0]))
                let result = pf.Check(rule.rightexps, sub, ind.leftexps, ind.rightexps, true)
                console.log('Check result: ', result)
                // if(!result){
                //     // console.log('   pf.substitute(ind.leftexps, sub, ind.leftexps): ')
                //     let c = pf.substitute(rule.rightexps, sub, ind.leftexps)
                //     console.log('substitute: ', pf.ExpToString(c))
                //     console.log()
                // }
                console.log('----------------')
            }
        }
        console.log('++++++++++++++++++++\n\n')
    }
}

function p(){
    for(const test of indtests.slice(indtests.length-1, indtests.length)){
        let ind = latexparser.Parse(test[1])
        console.log(pf.Proving(pf.ExpToString(ind.leftexps),pf.ExpToString(ind.rightexps)), true)
        console.log('++++++++++++++++++++\n\n')
    }
}
