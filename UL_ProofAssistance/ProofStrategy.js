
export default class ProofStrategy {
    constructor(pf, tstatements){
        this.pf = pf
        this.beginexp = []
        this.endexp = []
        this.expstack =[]
        for(const r of tstatements){
            let s = this.pf.RuleToString(r)

            let el = s.split('@')[0].trim()
            let er = s.split('@')[1].trim()
            this.beginexp.push(el)
            this.endexp.push(er)
        }
        
    }
    Init(){

        // console.log(this.pf.genRule('!,#12 $1 $0 #10 1 2,  1, @ ,#3 1, \n')[0].leftexps)
        this.ProveAll(this.beginexp, this.endexp)
    }
    ProveAll(beginexp, endexp) {
        let tpexp = this.pf.Exps.slice()
        // console.log(tpexp)
        
        var expi = 0
        var index = 1
        var stackindex=0
        var next = []
        
        while(expi < beginexp.length){
            console.log('---------- proof ',expi,' begin ----------')
        
            this.expstack.push([])
            let fromstack = false 
            let p = beginexp[expi]
            let q = endexp[expi]
            console.log('begin start: ',p, 'end: ', q)
            
            //check if rule is already a rule 
            //isRule matches code variables with operations
            let r = (this.pf.genRule('!'+p+'@'+q))

            if(!this.pf.isRule(r)){
                //first try, look for provable expressions in tpexp,
                //e is the next rule to prove, or else is -1
                
                let e = this.proveExps(tpexp, p)
                next = e[0]
                index = e[1]
                
                let tempstack
                
                if(next == -1) {
                    let x = this.provefromstack(expi, p,stackindex)
                    if(x[0] != -1){
                        fromstack = true
                        next = x[0]
                        tempstack=x[1]
                        tempstack.splice(0,1)
                        this.expstack[expi].push(next)
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
                    this.expstack[expi].push(next)
                    console.log('add to stack1: ',next)
        
                    //remove the found expression in tpexp
                    tpexp.splice(index,1)
                }
        
                //by this point we have proven 1 rule, next is either -1 or the next rule
                let npr = this.pf.genRule('!'+next +'@'+endexp[expi])
                // throw new Error('here')

                //prove the rest
                //if next == -1 then it will pass automatically
                while(next != -1 && !this.pf.Same(npr.leftexps, npr.rightexps)){
                    if(fromstack){
                        let e = this.proveExps(tempstack, next)
                        
                        if(e[0] != -1){
                            tempstack.splice(0,1)
                            next = e[0]
                        }
                        else{
                            //maybe here look for the next stack given stack index
        
                            let x = this.provefromstack(expi, next, stackindex, false)
        
                            if(x[0] != -1){
                                next = x[0]
                                tempstack=x[1]
                                tempstack.splice(0,1)
                                stackindex = x[2]
        
                            }else{
                                //try again but altnerative operand 
                                x = this.provefromstack(expi, beginexp[expi], stackindex, true )
                                if(x[0] != -1){
                                    next = x[0]
                                    tempstack=x[1]
                                    tempstack.splice(0,1)
                                    stackindex = x[2]
                                    this.expstack[expi] = []
                                }
                                else{
                                    throw new Error('failed in prove rest from proveExps->tempstack->provefromstack')
                                }
                            }
                        }
                    }
                    else{
                        let e = this.proveExps(tpexp, next)
        
                        if(e[0] != -1){
                            next = e[0]
                            index = e[1]
                            tpexp.splice(index,1)
                        }
                        else if(next ==-1){
                            //reset next and run the loop again
                            let x = this.provefromstack(expi, next, stackindex, false)
        
                            if(x[0] != -1){
                                fromstack = true
                                next = x[0]
                                tempstack=x[1]
                                tempstack.splice(0,1)
                                stackindex = x[2]
        
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
                        this.expstack[expi].push(next)
                        console.log('add to stack5: ',next, expi)
                        npr = this.pf.genRule('!'+next +'@'+endexp[expi])
                        // console.log('same?', this.pf.Same(npr.leftexps, npr.rightexps), npr)

                    }
                }
                
            }
        
            
            if(next == -1){
                throw new Error('failed')
            }
        
            let newrule = this.pf.genRule('!'+beginexp[expi]+'@'+endexp[expi])
            console.log('newrule: ', this.pf.RuleToString(newrule))
            console.log('expstack[expi]:',this.expstack[expi])
            this.pf.allrules.push(newrule)
        
            console.log('--------- proof ',expi,' end ----------')
            console.log()
        
            expi += 1
        
        }
    }
    proveExps(exps, p) { 
        let i = 0
    
        if(!exps) return [-1,-1]
        while (exps[i] && exps[i].length !=0){
            let l = exps[i]
            // console.log('from proveExps?: ',p,l)
            let t = this.pf.Proving(p, l)
            // console.log('t: ',t)
            if(t != -1) {
                return [t[0], i]
            }
        
            
            i+=1
        }
        
        return [-1,-1]
    }
    provefromstack(end, p, stackindex, alt){
        let i =0
        if(stackindex != 0) i = stackindex
        else i=0
        // console.log('provefromstack:')
        while ( i < this.beginexp.length-1 && i< end){
            let l = this.beginexp[i]
            let fakerule = this.pf.genRule('!'+p+'@'+l)
    
            let x = this.getchangeoperator(fakerule)
    
            let tstack = []
            
            for(const l of this.expstack[i]){
                let r = this.replaceoperator(x[0],x[1], l, alt)
                if(r) 
                {
                    if(r.length==0){
                        tstack.push(l)
                    }
                    tstack.push(r)
                }
            }
            // console.log('JKJK: ', tstack)
            let e= this.proveExps(tstack,p)
            let ret=e[0]
            if(ret != -1){
                return [ret,tstack, i]
            }
    
            let flipstack =[]
            for(const l of this.expstack[i]){
                // console.log(l)
                if(l ==[]) l =''
                flipstack.push(l)
            }
            e= this.proveExps(flipstack,p)
            ret=e[0]
    
            if(ret != -1){
                return [ret,flipstack, i]
            }
            i+=1
    
        }
        console.log('no matching begin expression')
        return [-1,-1]
    }
    replaceoperator(src, tar, l, alt){
        let dummystatement = this.pf.genRule('!'+',@'+l)
        
        for (const op of dummystatement.rightexps){
            if(op.operator){
                if(op.operator == src){
                    op.operator = tar 
                
                    if(op.Opparam){
                        if(op.Opparam != '')
                        {
                            for(const v of op.Opparam){
                                srctablel.push(v)
                            }
                        }
                    }
    
                    if(this.pf.binaryOperators.includes(src) && this.pf.unaryOperators.includes(tar)){
                        if(alt){
                            // console.log('before', op.operands)
                            let temp = op.operands[1]
                            op.operands = op.operands.slice(0,0)
                            op.operands.push(temp)
                            // console.log('after',op.operands)
    
                        }
                        else{
                            op.operands = op.operands.slice(0,op.operands.length-1)
                        }
                    }
                    else if(this.pf.binaryOperators.includes(tar) && this.pf.unaryOperators.includes(src)){
                        op.operands.push(op.operands[op.operands.length]+1)
                    }
                    let ret = this.pf.ExpToString(dummystatement.rightexps)
                    // console.log('dummy: ',ret)
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
    
        // console.log(d1)
    
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

