
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

//expression does not contain duplicate of beggin expressions, but it contains end expressions
let tpexp = LatexExps(rf,'./theorems',true)

var pf = new ProofAssistant(axioms, p, tpexp)
// pf.PrintAllRules()

// console.log(pf.isRule(pf.genRule('!,#11, @, #11, #11, \n')[0]))
// console.log(tpexp)

var beginexp = []
var endexp = []
for(const r of tstatements){
    let s = pf.RuleToString(r)

    let el = s.split('@')[0]
    let er = s.split('@')[1]
    beginexp.push(el)
    endexp.push(er)
}

// console.log(pf.isRule(pf.genRule('!, #12 $1 $1 , #11 , #15 1 ,  @ , #13 $1 $1 #10 2 3 , #4 1 , #4 1 ,\n')[0]))
var expstack =[]

var expi = 0
var index = 1
var stackindex=0
var next = []
// let ret = pf.genRule('!,#4 1,@,#4 1,\n')[0]
// console.log(pf.Same(ret.leftexps, ret.rightexps))

// console.log(beginexp)
console.log('-----------')
// console.log(endexp)

//prove all rules
while(expi < beginexp.length){
    console.log('---------- proof ',expi,' begin ----------')

    expstack.push([])
    let fromstack = false 
    let p = beginexp[expi]
    let q = endexp[expi]
    console.log('begin start: ',p, 'end: ', q)
    
    //check if rule is already a rule 
    //isRule matches code variables with operations
    let r = (pf.genRule('!'+p+'@'+q+'\n')[0])

    if(!pf.isRule(r)){
        //first try, look for provable expressions in tpexp,
        //e is the next rule to prove, or else is -1
        
        let e = proveExps(tpexp, p)
        next = e[0]
        index = e[1]
        
        let tempstack
        if(next == -1) {
            let x = provefromstack(p,stackindex)
            if(x[0] != -1){
                fromstack = true
                next = x[0]
                tempstack=x[1]
                tempstack.splice(0,1)
                expstack[expi].push(next)
                stackindex = x[2]
                console.log('add to stack0: ',next)

                // console.log('add to stack0: ',next)
            }
            else{
                throw new Error('no matching expression in provefromstack')
            }
        }
        else{

            //keep track of all expression that are used in a stack
            expstack[expi].push(next)
            console.log('add to stack1: ',next)

            //remove the found expression in tpexp
            tpexp.splice(index,1)
        }

        //by this point we have proven 1 rule, next is either -1 or the next rule
        let npr = pf.genRule('!'+next +'@'+endexp[expi]+'\n')[0]

        //prove the rest
        //if next == -1 then it will pass automatically
        while(next != -1 && !pf.Same(npr.leftexps, npr.rightexps)){
            if(fromstack){
                let e = proveExps(tempstack, next)
                
                if(e[0] != -1){
                    // tempstack=x[1]
                    tempstack.splice(0,1)
                    next = e[0]
                    // console.log('add to stack0: ',next)
                }
                else{
                    //maybe here look for the next stack given stack index

                    let x = provefromstack(next, stackindex)
                    // console.log('*&*&', x )

                    if(x[0] != -1){
                        fromstack = true
                        next = x[0]
                        tempstack=x[1]
                        tempstack.splice(0,1)
                        stackindex = x[2]

                        // console.log('*&*&', tempstack)
                    }else{
                        throw new Error('failed in prove rest from proveExps->tempstack->provefromstack')
                    }
                }
            }
            else{
                let e = proveExps(tpexp, next)

                if(e[0] != -1){
                    next = e[0]
                    index = e[1]
                    tpexp.splice(index,1)
                }
                else if(next ==-1){
                    //reset next and run the loop again
                    let x = provefromstack(next, stackindex)
                    // console.log('*&*&', x )

                    if(x[0] != -1){
                        fromstack = true
                        next = x[0]
                        tempstack=x[1]
                        tempstack.splice(0,1)
                        stackindex = x[2]

                        // console.log('*&*&', tempstack)
                    }                    
                }
                else{
                    throw new Error('failed in prove rest from proveExps->texp && provefromstack')
                }
            }

            if(next == -1) {
                throw new Error('debug next: ', next)
            }
            else{
                //add to the expstack
                expstack[expi].push(next)
                console.log('add to stack5: ',next)
                npr = pf.genRule('!'+next +'@'+endexp[expi]+'\n')[0]
                console.log(pf.isRule(npr), pf.RuleToString(npr))
            }
        }
        
    }

    

    let newrule = pf.genRule('!'+beginexp[expi]+'@'+endexp[expi]+'\n')[0]
    console.log('newrule: ', pf.RuleToString(newrule))
    console.log('expstack[expi]:',expstack[expi])
    pf.allrules.push(newrule)

    console.log('--------- proof ',expi,' end ----------')
    console.log()

    expi += 1

}



function proveExps(exps, p) { 
    let i = 0

    if(!exps) return [-1,-1]
    while (exps[i] && exps[i].length !=0){
        let l = exps[i]
        console.log('from proveExps?: ',p,l)
        let t = pf.Proving(p, l)
        console.log('t: ',t)
        if(t != -1) {
            return [t[0], i]
        }
    
        
        i+=1
    }
    
    return [-1,-1]
}
function provefromstack(p, stackindex){
    let i =0
    if(stackindex != 0) i = stackindex
    else i=0
    console.log('provefromstack:')
    // console.log(beginexp.length, expstack.length,expstack)
    while ( i < beginexp.length){
        let l = beginexp[i]
        let fakerule = pf.genRule('!'+p+'@'+l+'\n')[0]

        let x = getchangeoperator(fakerule)

        let tstack = []
        console.log(expstack[i])
        
        for(const l of expstack[i]){
            let r = replaceoperator(x[0],x[1], l)
            if(r) 
            {
                if(r.length==0){
                    tstack.push(l)
                }
                tstack.push(r)
            }
        }
        // console.log('JKJK: ', tstack)
        let e= proveExps(tstack,p)
        let ret=e[0]
        if(ret != -1){
            return [ret,tstack, i]
        }

        let flipstack =[]
        for(const l of expstack[i]){
            // console.log(l)
            if(l ==[]) l =''
            flipstack.push(l)
        }
        e= proveExps(flipstack,p)
        ret=e[0]

        if(ret != -1){
            return [ret,flipstack, i]
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
    
    return l
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