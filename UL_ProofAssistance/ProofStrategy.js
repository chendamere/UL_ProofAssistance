
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
    Init(){
        // console.log(this.tstatements)
        // console.log(this.allexps)
        for(let i =0; i < this.allexps.length; i ++){
            let begine = []
            let ende = []
            for(const r of this.tstatements[i]){
                let s = this.pf.RuleToString(r)    
                let el = s.split('@')[0].trim()
                let er = s.split('@')[1].trim()
                begine.push(el)
                ende.push(er)
                this.beginexp.push(el)
                this.endexp.push(er)
            }
            this.ProveAll(begine, ende, i)
            this.expioffset += this.beginexp.length
            this.beginexp = []
            this.endexp = []
        }
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
            if(this.pf.isRule(newrule)){
                this.expstack[this.expstack.length-1].push(q)
                expi += 1
                console.log('finished proof in ProveAll -> isrule!', this.pf.RuleToString(newrule))
                continue
            }

            //prove the statement in the user provided stack 
            let ret = this.proveExps(tpexp[expi], p, q, debugging)
            if(ret != -1){
                
                this.expstack[this.expstack.length-1] = this.expstack[this.expstack.length-1].concat(ret)
                this.pf.allrules.push(newrule)
                console.log(this.expstack[this.expstack.length-1])
                console.log('finished proof in ProveAll -> proveExps!', this.pf.RuleToString(newrule))
                expi += 1
                continue
            }
            
            //provefromstack will try to create duplicates from previous stacks with changing operators
            // assuming that operators have similar definition and axiom, similar looking proof will have similar proof step
            // similar defined as same operands when normalized, and same expression when all operators are substituted
            
            console.log('proveExp failed, trying provefromstack')
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

    matchAndCheckExp(start, end, debug = false){
        let begincheck = this.pf.genRule('!'+start+'@'+end)
        let r1variant = this.pf.try_match_operand_order(begincheck)
        for(const v of r1variant){
            if(this.pf.Proving(this.pf.ExpToString(v.leftexps), this.pf.ExpToString(v.rightexps), debug) == 1){
                return this.pf.ExpToString(v.rightexps)
            }
        }
        // return this.pf.Proving(start, end, debug) == 1 
        return false
    }
    proveExps(exps, start, end, debug=false) { 
        if(exps.length == 0){return -1}
        let i = 0
        let prev=start;
        let next;
        let ret = []
        //makes sure end expressions match
        if(!this.matchAndCheckExp(end, exps[exps.length-1])) return -1

        while(exps[i]){
            next = exps[i]
            let check = this.matchAndCheckExp(prev, next, debug)
            if(check){
                prev = check    
                ret.push(prev)   
                i+=1
            }
            else{
                return -1
            }    
        }
        // console.log('ret: ', ret)
        return ret
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

    provefromstack(end, p, q, stackindex, alt, debug=false){
        let i = stackindex
        while ( i < this.expstack.length-1 && i < end){
            if(i + this.expioffset>= end) break

            //get the changing operator from beginning lines, if the changed lines are not same, then repeat the process with end line
            let l = this.expstack[i][0]
            let tempr = this.pf.genRule('!'+p+'@'+l)
            let x = this.getchangeoperator(tempr)

            let tstack = []
            const slicelst = this.expstack[i].slice(0,this.expstack[i].length)
            for(const l of slicelst){
                let r = this.replaceoperator(x[0],x[1], l, alt)
                if(r){
                    if(r.length==0){
                        tstack.push(l)
                    }
                    tstack.push(r)
                }
            }
            let ret= this.proveExps(tstack,p, q,debug)
            if(ret != -1){
                return [tstack, i]
            }
            ret = this.proveReduceOprExps(tstack, p, q, debug)
            if(ret != -1){
                return [tstack, i]
            }
            i+=1
    
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
                    else if(this.pf.binaryOperators.includes(tar) && this.pf.unaryOperators.includes(src)){
                        //add the next operand to operands
                        op.operands.push(op.operands[op.operands.length]+1)
                    }
                    let ret = this.pf.ExpToString(dummystatement.rightexps)
                    return ret               
                }
            }
        }
        return l
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

