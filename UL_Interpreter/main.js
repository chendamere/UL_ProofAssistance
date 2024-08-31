
import {LatexChapters, LatexExps,Parse_rules_and_titles,Parser} from'./latex-chapters.js'
import ParseTokens from './parser-analyser.js'
import ProofAssistant from './ProofAssistant.js'
import AnalyseCode from './lexer-analyser.js'
import ReadFiles from './fileReader.js'
import brain from 'brain.js'
let rf = ReadFiles(Parse_rules_and_titles)
var p = Parser(AnalyseCode, ParseTokens)


let axioms = LatexChapters(rf, './axiom', p)

let tstatements = LatexChapters(rf, './theorems', p)

let tpexp = LatexExps(rf,'./theorems',true)

var pf = new ProofAssistant(axioms, p, tpexp)
// pf.PrintAllRules()

// console.log(pf.isRule(pf.genRule('!,#11, @, #11, #11, \n')[0]))
// console.log(tpexp)
let beginexp = []
let endexp = []
let expstack =[]

for(const r of tstatements){
    let s = pf.RuleToString(r)

    let el = s.split('@')[0]
    let er = s.split('@')[1]

    if(!beginexp.includes(el)){
        beginexp.push(el)
    }
    if(!endexp.includes(er)){
        endexp.push(er)
    }
}
let expi = 0
var index = 1
var next = []
while(expi < beginexp.length){
    console.log('---------- proof ',expi,' begin ----------')
    expstack.push([])
    let fromstack = false 

    let p = beginexp[expi]
    let q = endexp[expi]
    console.log('start: ',p, 'end: ', q)
    
    let r = (pf.genRule('!'+p+'@'+q+'\n')[0])
    // console.log(pf.RuleToString(r))
    if(!pf.isRule(r)){
        //try all expression in pf
        let e = proveExps(tpexp, p)
        next = e[0]
        index = e[1]
        let tempnext, tempstack
        if(next == -1) {
            [tempnext, tempstack] = provefromstack(p)

            if(tempnext != -1){
                fromstack = true
                // console.log('fromstack: ', fromstack)
                next = tempnext

                tempstack.splice(0,1)
            }
        }
        else{
            // console.log('next: ', next)

            expstack[expi].push(next)
            tpexp.splice(index,1)

        }

        let npr = pf.genRule('!'+next +'@'+endexp[expi]+'\n')[0]

        //prove the rest
        while(next != -1 && !pf.Same(npr.leftexps, npr.rightexps)){
            p = next 

            if(fromstack){
                let e = proveExps(tempstack, p)
                next = e[0]
                index = e[1]
                if(next!= -1){
                    tempstack.splice(0,1)
                }
            }
            else{

                let e = proveExps(tpexp, p)
                next = e[0]
                index = e[1]
                if(next!= -1){
                    tpexp.splice(index,1)
                }

            }

            expstack[expi].push(next)
            if(next == -1) {
                console.debug('next: ', next)
            }
            npr = pf.genRule('!'+next +'@'+endexp[expi]+'\n')[0]
            // console.log('next :', next)
        }
    }

    

    let newrule = pf.genRule('!'+beginexp[expi]+'@'+endexp[expi]+'\n')[0]
    console.log('newrule: ', pf.RuleToString(newrule))
    pf.allrules.push(newrule)

    console.log('--------- proof ',expi,' end ----------')
    console.log()

    expi += 1

}


function switchtopbot(exp){
    let br
    let ret=[]
    let ti =0
    while(ti< exp.length){
        let e = exp[ti]
        if(e.Opparam){
            if(e.Opparam[0]){
                if(e.Opparam[0].value == '#12'){
                    
    
                    br = e.Opparam
                    let topi = parseInt(br[1].value[1])
                    let boti = parseInt(br[2].value[1])
                    e.Opparam[1].value = e.Opparam[2].value
                    e.Opparam[2].value = e.Opparam[1].value
                    ret.push(e)
    
                    // console.log('topi: ', topi)
                    let tii = ti + topi +1
                    while(tii<= ti+topi+boti){
                        e = exp[tii]
                        ret.push(e)
                        tii +=1
                    }
                    tii = ti + 1
                    while(tii <= ti+topi){
                        e = exp[tii]
                        ret.push(e)
                        tii +=1
                    }
                    ti = ti + topi + boti+1
                    continue 
                }
            }
        }
        ret.push(e)
        ti +=1
    }
    // console.log(ret)

    return ret
}

function proveExps(tpexp, p) { 
    let i = 0
    let done = false

    if(!tpexp) return [-1,-1]
    while (tpexp[i] && tpexp[i].length !=0){
        let l = tpexp[i]
        // console.log(l)
        if(!done){
            console.log(p,l)
            let t = pf.Proving(p, l)
            if(t != -1) {
                // console.log('here: ',t)

                return [t[0], i]
                //add every exp execpt for the one just used
            }
        }
        
        i+=1
    }
    
    return [-1,-1]
}
function provefromstack(p){
    let i=0
    // console.log(beginexp.length, expstack.length,expstack)
    while ( i < beginexp.length){
        let l = beginexp[i]
        let fakerule = pf.genRule('!'+p+'@'+l+'\n')[0]

        let x = getchangeoperator(fakerule)

        // console.log(pf.RuleToString(fakerule), ': ',checkParams(getParams(fakerule.leftexps), getParams(fakerule.rightexps)))
    
        let leftparam  = getParams(fakerule.leftexps)
        let rightparam = getParams(fakerule.rightexps)
        // console.log(leftparam)
        // if(!checkParams(leftparam, rightparam)) {i+=1; continue}
        
        //switch top and bot in the stack

        // console.log(br)

        // if(x.length==0 || !x || !expstack[i]) {i+= 1; continue}

        let tstack = []
        for(const l of expstack[i]){
            let r = replaceoperator(x[0],x[1], l)
            if(r) 
            {
                tstack.push(r)
            }
        }
        // console.log('here')

        let e= proveExps(tstack,p)
        let ret=e[0]
        // console.log(ret)
        // console.log('here')
        // console.log(ret)
        // let index=e[1]
        if(ret != -1){
            return [ret,tstack]
        }
        // console.log('here')

        // let stbe = switchtopbot(l)
        // let flipedr = pf.genRule('!'+p+'@'+stbe+'\n')[0]
        let flipstack =[]
        // console.log(expstack,i)
        for(const l of expstack[i]){
            console.log(l)
            if(l ==[]) l =''
            
            // console.log(stb)
            // stb = stb.trim()
            flipstack.push(l)
        }
        // console.log(flipstack)
        e= proveExps(flipstack,p)
        ret=e[0]
        // console.log(ret)
        // let index=e[1]
        if(ret != -1){
            return [ret,flipstack]
        }
        i+=1

    }
    console.log('no matching begin expression')
    return [-1,-1]
}
function replaceoperator(src, tar, l){
    let dummystatement = pf.genRule('!'+',@'+l+'\n')[0]
    
    for (const op of dummystatement.rightexps){
        if(op.operator){
            if(op.operator.value == src){
                op.operator.value = tar 
            
                if(op.Opparam){
                    if(op.Opparam.value != '')
                    {
                        for(const v of op.Opparam){
                            srctablel.push(v)
                        }
                    }
                }

                if(pf.binaryOperators.includes(src) && pf.unaryOperators.includes(tar)){
                    op.operands = op.operands.slice(0,op.operands.length-1)
                }
                else if(pf.binaryOperators.includes(tar) && pf.unaryOperators.includes(src)){
                    op.operands.push(op.operands[op.operands.length]+1)
                }
                
                let ret = pf.ExpToString(dummystatement.rightexps)
                console.log('dummy: ',ret)
                return ret
            
            }
        }
    }
    return []
}

function getchangeoperator(fakerule) {
    //look for similar statements, defined here as statements with only 1 different operation (should do the job)

    let optl= getOperators(fakerule.leftexps)
    let optr= getOperators(fakerule.rightexps)

    const d1 = optl.filter((element) => !optr.includes(element));
    const d2 = optr.filter((element) => !optl.includes(element));

    // console.log(d1)

    if (d1.length != 1 ||d2.length != 1) {
        return []
    }
    else{
        return [d2[0],d1[0]]

    }
}

function getOperators(exps){
    let ret = []
    for (const e of exps){
        if(e.operator){
            if(!ret.includes(e.operator.value))
                ret.push(e.operator.value)
        }
    }
    return ret
}
function getParams(exps){
    let ret = []
    for (const e of exps){
        if(e.Opparam){
            if(!e.Opparam.value){
                let r = e.Opparam
                ret.push(r)
            }
        }
    }
    return ret
}

function checkParams(l1, l2){
    let i = 0
    if(l1.length != l2.length) return false
    while(i< l1.length ){
        if( l1[i].value=='' && l2[i].value =='')
        {
            i+=1;continue;
        }

        else{
            let j =0
            while(j < l1[i].length){
                if(!l2[i][j]) return false
                
                if(l1[i][j].value != l2[i][j].value) { return false}
                
                j+= 1
            }
        }
        i+= 1
    }
    return true
}
// focus on what to manipulate

// const net = new brain.NeuralNetwork();

// net.train([
//   { input: { r: 0.03, g: 0.7, b: 0.5 }, output: { black: 1 } },
//   { input: { r: 0.16, g: 0.09, b: 0.2 }, output: { white: 1 } },
//   { input: { r: 0.5, g: 0.5, b: 1.0 }, output: { green: 1 } },
// ]);

// const output = net.run({ r: 1, g: 0.4, b: 0 }); // { white: 0.99, black: 0.002 }

// console.log(output)