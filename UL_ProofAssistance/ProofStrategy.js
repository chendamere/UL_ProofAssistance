import { stat } from "fs"

export default class ProofStrategy {
    constructor(pf, tstatements, allexps){
        this.pf = pf
        this.beginexp = []
        this.endexp = []
        this.expstack =[]
        this.tstatements=tstatements
        this.allexps = allexps
        this.expioffset = 0
    }

    AxiomsUptoChapter(chapterindex){

        let ret= []
        for(let i = 0; i < chapterindex; i++){
            // console.log(this.tstatements[i])
            for(const r of this.tstatements[i]){
                ret.push(r)
            }
        }
        return ret

    }
    ProveChapter(chapterindex){
        // console.log(this.tstatements)
        // console.log(this.allexps)
        // assume all statements in previous chapters are correct (move them to this.pf.allaxioms)

        // console.log(this.pf.allrules.length)
        this.pf.allrules = this.pf.allrules.concat(this.AxiomsUptoChapter(chapterindex))
        // console.log(this.pf.allrules.length)
        // this.pf.printallrule()
        let begine = []
        let ende = []
        for(const r of this.tstatements[chapterindex]){
            let s = this.pf.RuleToString(r)    
            let el = s.split('@')[0].trim()
            let er = s.split('@')[1].trim()
            begine.push(el)
            ende.push(er)
            this.beginexp.push(el)
            this.endexp.push(er)
        }
        this.ProveAll(begine, ende, chapterindex)
        this.expioffset += this.beginexp.length
        this.beginexp = []
        this.endexp = []
    }
    ProveAll(beginexps, endexps, expindex, debugi = beginexps.length-1) {
        let tpexp = this.allexps[expindex]
        var expi = 0
        var stackindex=0
        let debugging = true
        
        while(expi < beginexps.length){
            console.log('--- Proof ', expi, ' begins ----')

            //take all beginning expression in stack and pair up with ending expression
            this.expstack.push([beginexps[expi]])
            let p = beginexps[expi]
            let q = endexps[expi]
            let newrule = (this.pf.genRule('!'+p+'@'+q))
            console.log('tar rule: ', this.pf.RuleToString(newrule))

            //check if statement is already a rule
            console.log('--CHECKING IF STATEMENT IS A RULE OR MATCHCV--')

            // let statement = this.pf.genRule('!'+p+'@'+q)
            if(this.pf.Proving(p, q, true) == 1){
                this.expstack[this.expstack.length-1].push(q)
                expi += 1
                console.log('finished proof in ProveAll -> this.Proving!', this.pf.RuleToString(newrule))
                console.log()
                continue
            }

            //prove the statement in the user provided stack 
            // console.log( tpexp.length, this.expstack.length)
            // console.log(tpexp[expi].length)

            console.log('--BEGIN PROVING FROM USER PROVIDED EXPRESSION--')
            console.log(tpexp[expi])

            let ret = this.proveExps(tpexp[expi], p, q, debugging)
            if(ret != -1){
                
                this.expstack[this.expstack.length-1] = this.expstack[this.expstack.length-1].concat(ret)
                this.pf.allrules.push(newrule)
                expi += 1

                // console.log(this.expstack[this.expstack.length-1])
                console.log('finished proof in ProveAll -> proveExps!', this.pf.RuleToString(newrule))
                console.log()
                continue
            }
            
            //provefromstack will try to create duplicates from previous stacks with changing operators
            // assuming that operators have similar definition and axiom, similar looking proof will have similar proof step
            // similar defined as same operands when normalized, and same expression when all operators are substituted
            
            console.log('--BEGIN PROVING FROM STACK--')
            ret = this.provefromstack(expi+this.expioffset, p, q, stackindex, debugging)
            if(ret != -1){
                this.expstack[this.expstack.length-1] = this.expstack[this.expstack.length-1].concat(ret[0])
                stackindex = ret[1]
                this.pf.allrules.push(newrule)
                console.log(this.expstack[this.expstack.length-1])
                console.log('finished proof in ProveAll -> provefromstack!', this.pf.RuleToString(newrule))
                expi += 1
                continue
            }

            throw new Error('failed in ProveAll')
        }
    }

    //normalizes the first proof-step and use that table to convert all remaining 
    normalizeProof(exps, table){
        let srctable
        let ret =[]
        if(!table){
            srctable = this.pf.Operands_normalize_exps( this.pf.cloneExp((this.pf.genRule('!,@'+exps[0]).rightexps)), {})[1]
        }else[
            srctable = {...table}
        ]
        for(const exp of exps){
            let rexp = this.pf.ExpToString(this.pf.Operands_normalize_exps(this.pf.genRule('!,@'+exp).rightexps, this.pf.flipKeyandValue(srctable))[0])
            ret.push(rexp)
        }
        // ret = [src].concat(ret)
        return ret
    }
    matchAndCheckExp(exps, start, end, debug = false){
        // console.log(exps)
        console.log('matchandecheck: ', exps[exps.length-1], end)
        let srcend = this.pf.genRule('!,@'+exps[exps.length-1]).rightexps
        let tarend = this.pf.genRule('!,@'+end).rightexps
        const [nl, nlt] = this.pf.Operands_normalize_exps(this.pf.cloneExp(srcend), {})
        const [nr, nrt] = this.pf.Operands_normalize_exps(this.pf.cloneExp(tarend), {})

        if(this.pf.Same(nl, nr)){
            let dict = this.pf.flipKeyandValue(this.pf.matchDictionaries(nlt, this.pf.flipKeyandValue(nrt)))
            let retlist = this.normalizeProof(exps, dict)
            return retlist
        }
        return false
    }
    proveExps(exps, start, end, debug=false) { 
        // console.log('stop1')

        if(exps.length == 0){return -1}
        // console.log("exps: ", exps)
        const cexps = this.matchAndCheckExp(exps,start, end, debug)
        // const cexps = exps
        // console.log("cexps: ", cexps)
        let prev=start;
        let next;
        let i = 0

        if(cexps){
            while(cexps[i]){
                next = cexps[i]
                let check = this.pf.Proving(prev, next, true)
                if(check != -1){
                    prev = next    
                    i+=1
                }
                else{
                    return -1
                }
            }
            if(i == cexps.length){
                return cexps
            }
        }
        // console.log('ret: ', ret)
        return -1
    }

    proveReduceOprExps(tstack, p, q, debug){
        let ret = []
        for(const exp of tstack){
            let nr = this.pf.genRule('!,@'+exp).rightexps
            for(const opt of nr){
                let j =0
                while(j < opt.operands.length){
                    let x = parseInt(opt.operands[j])
                    if(x > 1){
                        x=x-1
                        opt.operands[j] = x.toString()
                    }
                    j += 1
                }
            }
            ret.push(this.pf.ExpToString(nr))
        }
        let ret1 = this.proveExps(ret, p , q, debug)
        return ret1
    }

    getStack(srctar, index, alt){
        let tstack = []
        let [srcoperator, taroperator] = srctar
        const slicelst = this.expstack[index].slice(0,this.expstack[index].length)
        // console.log("slicelst: ", )
        for(const l of slicelst){
            let r = this.replaceoperator(srcoperator,taroperator, l, alt)
            if(r){
                if(r.length==0){
                    tstack.push(l)
                }else{
                    tstack.push(r)
                }
            }
        }
        console.log(tstack)
        return tstack
    }
    provefromstack(end, p, q, stackindex, alt, debug=false){
        let index = stackindex
        while ( index < this.expstack.length-1 && index < end){
            if(index + this.expioffset>= end) break

            //get the changing operator from beginning lines, if the changed lines are not same, then repeat the process with end line
            let l = this.expstack[index][0]
            let tempr = this.pf.genRule('!'+p+'@'+l)
            let pair_of_operators = this.getchangeoperator(tempr)

            let tstack = this.getStack(pair_of_operators, index, alt)
            // console.log("tstack: ", tstack, index)

            let ret= this.proveExps(tstack,p, q,debug)
            if(ret != -1){
                return [tstack, index]
            }
            index+=1
    
        }
        return -1
    }
    replaceoperator(src, tar, l, alt){
        let dummystatement = this.pf.genRule('!'+',@'+l)
        for (const op of dummystatement.rightexps){
            if(op.operator){
                if(op.operator == src){
                    op.operator = tar 
                    if(this.pf.binaryOperators.includes(src) && this.pf.unaryOperators.includes(tar)){
                        if(alt){
                            //get second operand
                            let temp = op.operands[1]
                            op.operands = op.operands.slice(0,0)
                            op.operands.push(temp)    
                        }
                        else{
                            //get all but last operand
                            op.operands = op.operands.slice(0,op.operands.length-1)
                        }
                    }
                    else if(this.pf.unaryOperators.includes(src) && this.pf.binaryOperators.includes(tar) ){
                        //add the next operand to operands
                        op.operands.push((parseInt(op.operands[op.operands.length-1])+1).toString())
                    }
                    
                }
            }
        }
        let ret = this.pf.ExpToString(dummystatement.rightexps)
        return ret  
    }
    getchangeoperator(fakerule) {
        //look for similar statements, defined here as statements with only 1 different operation (should do the job)
    
        let optl= this.getOperators(fakerule.leftexps)
        let optr= this.getOperators(fakerule.rightexps)
    
        const d1 = optl.filter((element) => !optr.includes(element));
        const d2 = optr.filter((element) => !optl.includes(element));
    
        if (d1.length != 1 ||d2.length != 1) {
            return []
        }
        else{
            return [d2[0],d1[0]]
        }
    }
    getOperators(exps){
        let ret = []
        for (const e of exps){
            if(e.operator){
                if(!ret.includes(e.operator))
                    ret.push(e.operator)
            }
        }
        return ret
    }
    
}

