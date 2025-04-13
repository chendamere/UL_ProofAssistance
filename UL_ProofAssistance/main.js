
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
// console.log(latexparser.cv)
// ps.Init()

let tests = [
    ['!, @ , #3 1, #4 1, ', 
        '!, #7 1 , #101 $0 $2 #10 2 3 , #5 1, #5 2, @ , #7 1 , #101 $2 $2 #10 2 3 , #3 1 , #4 1 , #5 1, #5 2,'
    ],
    ['!, @ , #3 1, #4 1, ',
        '!, #7 1 , #101 $2 $2 #10 2 3, #6 1, #6 2, #5 1, #5 2, @ ,'
    ],
    ['!,#4 1, #3 1, @ , #3 1, #4 1,',
        '!, #7 1 , #101 $2 $2 #10 2 3, #6 1, #6 1, #4 2, #3 2, @ , #7 1 , #101 $2 $2 #10 2 3, #6 1, #6 1, #3 2, #4 2, '],
    ['!, @, #100 $1 $1 #10 1 2, #4 3, #4 4, ',
        '!, #100 $1 $0 #10 3 4, #6 3, @, #100 $2 $0 #10 3 4, #6 3, #100 $1 $1 #10 1 2, #4 3, #4 4, '
    ],
    ['!, #101 $0 $0 #17 1 , @ , #2 2 , #101 $1 $1 #15 1 2 , #5 2 , #5 2 , ',
        '!, #4 1, #101 $1 $1 #17 1, #4 1, #4 1, @ , #4 1,  #2 2, #101 $2 $2 #15 1 2 , #5 2 ,#4 1, #5 2 , #4 1, '
    ],
    ['!, #101 $0 $0 #17 1 , @ , #2 2 , #101 $1 $1 #15 1 2 , #5 2 , #5 2 , ',
        '!, #4 1, #101 $0 $0 #17 1, @ , #4 1,  #2 2, #101 $1 $1 #15 1 2 , #5 2 , #5 2 ,  '
    ]
]
// let sub = latexparser.Parse('!, @ , ').rightexps


// let x = pf.GetAllOperandsVariance(check.leftexps, rule.rightexps, rule.leftexps)
// for(const l of x){
//     console.log('rule left: ', pf.ExpToString(l[0]), 'rule right: ', pf.ExpToString(l[1]))
// }

// let allsub = pf.getsub(ind.leftexps)[0]

// for(const x of allsub){
//     // console.log(x)
//     console.log(pf.ExpToString(x[0]))
// }

// let result = pf.MatchandCheck(ind.leftexps, ind.rightexps)
// let br = pf.getFirstBr(ind.leftexps)
// console.log(br)
// let [top, bot] = pf.getTopBot(ind.leftexps, br)
// console.log(bot)
// console.log(pf.ExpToString(top))
// console.log(pf.ExpToString(bot))

for(const test of tests.slice(tests.length-1, tests.length)){
    let rule = latexparser.Parse(test[0])
    let ind = latexparser.Parse(test[1])
    console.log('rule left: ', pf.ExpToString(rule.leftexps))
    console.log('ind left: ', pf.ExpToString(ind.leftexps))
    let [s1, s2] = pf.getsub(ind.leftexps)
    let allsub = s1.concat(s2)
    let subexps = pf.addEmpty(allsub)
    subexps = pf.sort_subexp(subexps)
    for(const sub of subexps){
        if(pf.Same(pf.cloneExp(rule.leftexps), sub[0])){
            console.log(sub[1], 'sub: ', pf.ExpToString(sub[0]))
            let result = pf.Check(rule.rightexps, sub, ind.leftexps, ind.rightexps, true)
            console.log(result)
            if(!result){
                console.log('pf.substitute(ind.leftexps, sub, ind.leftexps): ')
                let c = pf.substitute(rule.rightexps, sub, ind.leftexps)
                console.log(pf.ExpToString(c))
                console.log()
            }
            console.log('----------------')
        }
    }
    console.log('++++++++++++++++++++\n\n')
}
