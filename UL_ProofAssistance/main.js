
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
ps.Init()

let check = latexparser.Parse('!, #4 1 , #101 $2 $2 #10 2 3 , #3 1 , #4 1 , #3 1 , #4 1 , @   , #4 1 , #3 1 , #101 $1 $1 #10 2 3 , #4 1 , #4 1 , ')
let check2 = latexparser.Parse('!, #101 $1 $1 #10 2 3 , #3 1 , #3 1 , @   ,#3 1 , #101 $0 $0 #10 2 3 ,')
// let check3 = latexparser.Parse('! , #3 1 , #3 1 , @   , #3 1 , #3 1 ,#4 1 , #4 1 ,  ')
// let check4 = latexparser.Parse('!, #101 $1 $1 #10 2 3 , #3 1 , #3 1 , @   , #4 1 , #3 1 , #101 $1 $1 #10 2 3 , #4 1 , #4 1 , ')

// let [sub1, sub2] = pf.getsub(check.leftexps)

// sub1 = pf.addEmpty(sub1.concat(sub2))
// for(const x of sub1){
//     console.log('!', x[1], pf.ExpToString(x[0]))
// }


// let ret = pf.Proving(pf.ExpToString(check.leftexps), pf.ExpToString(check.rightexps), true)

// console.log(ret)

// let rest = pf.Check(check2.rightexps, [check2.leftexps,1], check.leftexps )


// for(const x of rest){
//     console.log(pf.ExpToString(x))
// }
// console.log(pf.ExpToString(rest))
// console.log(latexparser.Parse('!,@,'))

// for(const testexp of subexpbranchtest){
//     let src = latexparser.Parse(testexp).leftexps
//     let [t,s] = pf.getsub(src)
//     console.log('----- Start -----')

//     console.log('test exp: ', pf.ExpToString(src))
//     //main 
//     for(const x of t){
//         console.log('!', x[1], pf.ExpToString(x[0]))
//     }
//     console.log('-----------------')

//     //sub
//     for(const x of s){
//         console.log('!', x[1], pf.ExpToString(x[0]))
//     }
//     console.log('----- End -------')
//     // let allnext = pf.MatchandCheck(src, [])

// }