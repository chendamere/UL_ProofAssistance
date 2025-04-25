
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
ps.ProveChapter(1)


// console.log(pf.generateCombinations(0, 0))
// console.log(pf.generateCombinations(5, 5))
// console.log(pf.generateCombinations(4, 8))
// let ind = latexparser.Parse('!, #11, #7 1 2, #4 1, #4 2, @ , #11, #13 1, #13 2, ')
// let srcexp = ind.leftexps
// let tarexp = ind.rightexps
// console.log(pf.checkcv2(srcexp , tarexp ))
// p()
// CombineTest()
// f()

function CombineTest(){
    for(const test of indtests.slice(indtests.length-1, indtests.length)){
        let ind = latexparser.Parse(test[1])

        let [s1, s2] = pf.getsub(ind.leftexps)
        let allsub = s1.concat(s2)
        let subexps = pf.addEmpty(allsub)
        subexps = pf.sort_subexp(subexps)
        for(const sub of subexps){ 
            console.log('sub: ', sub[1], pf.ExpToString(sub[0]))
            let combinelist = pf.getAllCombine(sub[0], sub, ind.leftexps)
            for(const c of combinelist){
                console.log('   combine: ',pf.Same(ind.leftexps, c), pf.ExpToString(c))
                // if(!pf.Same(ind.leftexps, c)){
                //     console.log('   combine: ',pf.Same(ind.leftexps, c), pf.ExpToString(c),)
                // }
            }
            console.log()
        }
        console.log('src: ', pf.ExpToString(ind.leftexps))
        console.log('subexps length: ', subexps.length)

        console.log('------')
    }
}

function f() { 

    for(const test of indtests.slice(indtests.length-1, indtests.length)){
        let rule = latexparser.Parse(test[0])
        let ind = latexparser.Parse(test[1])
        console.log('rule left: ', pf.ExpToString(rule.leftexps), 'rule right: ', pf.ExpToString(rule.rightexps))
        console.log('ind left: ', pf.ExpToString(ind.leftexps))
        let [s1, s2] = pf.getsub(ind.leftexps)
        let allsub = s1.concat(s2)
        let subexps = pf.addEmpty(allsub)
        subexps = pf.sort_subexp(subexps)
        for(const sub of subexps){

            let ret = pf.CheckFromRules(rule, sub, ind.leftexps, ind.rightexps, true)
            if(ret){
                console.log("ret: ", ret)
            }
            
            // let oprvariance = pf.GetAllOperandsVariance(sub[0],rule.leftexps,rule.rightexps)
            // if(pf.ExpToString(sub[0]).includes(', #3 3 , #7 1 2 ,') && sub[1] == 1){
                // let combine = pf.GetAllVariance(rule.rightexps, sub, ind.leftexps)
                // console.log()
                // for(const x of oprvariance){
                //     console.log(pf.ExpToString(x[0]),pf.ExpToString(x[1]))
                // }
            // }

            // console.log(sub[1], pf.ExpToString(sub[0]))
            // console.log('------------\n')
            // for(const nrule of oprvariance){
            //     console.log( pf.ExpToString(nrule[0]))

            //     if(pf.ExpToString(nrule[0]).includes(', #101 $0 $0 #15 3 4 ,')){
            //         // console.log(pf.ExpToString(nrule[0]), sub[1], pf.ExpToString(sub[0]))
            //     }

            //     if(pf.Same(pf.cloneExp(nrule[0]), sub[0])){
            //         console.log('index: ', sub[1], 'sub: ', pf.ExpToString(sub[0]))
            //         let result = pf.Check(nrule[1], sub, ind.leftexps, ind.rightexps, true)
            //         console.log('Check result: ', result)
            //         let c = pf.substitute(rule.rightexps, sub, ind.leftexps)
            //         console.log('substitute: ', pf.ExpToString(c))
            //         // if(!result){
            //         //     // console.log('   pf.substitute(ind.leftexps, sub, ind.leftexps): ')
            //         //     let c = pf.substitute(rule.rightexps, sub, ind.leftexps)
            //         //     console.log('substitute: ', pf.ExpToString(c))
            //         //     console.log()
            //         // }
            //         console.log('----------------')
            //     }
            // }
        }
        console.log('++++++++++++++++++++\n\n')
    }
}

function p(){
    for(const test of indtests.slice(indtests.length-1, indtests.length)){
        let ind = latexparser.Parse(test[1])
        console.log(pf.Proving(pf.ExpToString(ind.leftexps),pf.ExpToString(ind.rightexps), true))
        console.log('++++++++++++++++++++\n\n')
    }
}
