

import ProofAssistant from "./ProofAssistant.js";
import LatexParser from  "./LatexParser.js"
import {subexptest, subexpbranchtest, indtests} from "./tests.js"
import ProofStrategy from  './ProofStrategy.js';
import FileParser from  './FileParser.js';

let latexparser = new LatexParser();
let fs = new FileParser(latexparser)
let allrules = fs.ParseRulesFromFile('./axiom/');
let [tstatements,allexps] = fs.ParseExpressionsFromFile('./theorems/');


let pf = new ProofAssistant(allrules, latexparser,[])

// for(const chapter of allexps){
//     for(const list_of_exp of chapter){
//         for(const exp of list_of_exp){
//             let pexp =  pf.ExpToString(latexparser.Parse('!,@'+exp).rightexps)
//             if(pexp){
//                 if(pexp.includes(' #0 ')){
//                     continue
//                 }else{
//                     console.log('exp:',pexp)

//                 }
//             }
//         }
//     }
// }
// console.log(allexps)

let ps = new ProofStrategy(pf, tstatements.slice(0,2), allexps)

// console.log(allexps)
// pf.PrintAllRules()
// let assumedAxiom = ps.AxiomsUptoChapter(1)
// console.log(assumedAxiom.length)
// for(const r of assumedAxiom){
//     console.log(pf.RuleToString(r))
// }
// ps.ProveChapter(0)
// ps.ProveChapter(1)

// let test = latexparser.Parse('!, #11 , @ , #3 2, ')
// console.log(pf.ExpToString(test.leftexps), pf.ExpToString(test.rightexps))
// console.log(pf.Same(test.leftexps, test.rightexps))

// console.log(pf.generateCombinations(0, 0))
// console.log(pf.generateCombinations(5, 5))
// console.log(pf.generateCombinations(4, 8))
// let ind = latexparser.Parse('!, #2 1 , #101 $0 $0 #15 2 3 ,  @  , #2 1 , #101 $0 $0 #10 2 3 ,')
// let srcexp = ind.leftexps
// let tarexp = ind.rightexps
// console.log(pf.checkcv2(srcexp , tarexp ))
p()
// CombineTest()
// f()
// console.log(pf.generateLowerCombinations([2,2,2]))

// console.log(pf.ObrMatchCbr(srcexp, tarexp))

// let exp =  latexparser.Parse('!, @ , #100 $0 $1 #15 1 2 , #11 , #100 $1 $1 #15 3 4 , #13 5 , #13 6 , ').rightexps

// let allsub = pf.getsub(exp)
// let l1 = allsub[0]
// let l2 = allsub[1]
// console.log('-----l1----')

// for(const sub of l1){
//     console.log(sub[1], pf.ExpToString(sub[0]))
// }
// console.log('-----l2----')
// for(const sub of l2){
//     console.log(sub[1], pf.ExpToString(sub[0]))
// }

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
        console.log('ind left: ', pf.ExpToString(ind.leftexps), 'ind right: ', pf.ExpToString(ind.rightexps))
        let [s1, s2] = pf.getsub(ind.leftexps)
        let allsub = s1.concat(s2)
        let subexps = pf.addEmpty(allsub)
        subexps = pf.sort_subexp(subexps)
        if(pf.hasCV(rule.leftexps) || pf.hasCV(rule.rightexps)){
            let CvCheck = pf.MatchCv(rule.leftexps, rule.rightexps, ind.leftexps,ind.rightexps)
            console.log(CvCheck)

        }
        for(const sub of subexps){
            
            let ret = pf.CheckFromRules(rule, sub, ind.leftexps, ind.rightexps, true)
            if(ret){
                console.log("ret: ", ret, pf.ExpToString(sub), sub)
            }
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
