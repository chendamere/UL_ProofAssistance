



//Proof assistance handles checking if certain proof exists in the database
//or if a rule can be generated inductively
//for a proof to satisfy, there need to exist one or more equivalent expression.
//there exist one or more equivalent expression if 

import { error, table } from "console"

class ProofAssistant {
    constructor (allrules, parser, Exps){
        this.allrules = allrules
        this.parser = parser
        this.Exps = Exps
        this.AllOperators =  this.Get_all_operator()
        this.unaryOperators = this.parser.unaryOperators
        this.binaryOperators = this.parser.binaryOperators
        this.BrOperators =  this.parser.branch
        this.AddSpacetoExp()
    }

    //--Prove--
    Proving(start, end, debug= false) {

        //operands are not binded yet
        if(debug){
            console.log('------Proving-------')
            console.log('   start: ', start, 'end: ', end)
        }
        let tempv = this.genRule('!'+start+'@'+end)
        if (this.Same(tempv.leftexps, tempv.rightexps)) return 1
        if(this.MatchandCheck(tempv.leftexps, tempv.rightexps, debug)) {
            return 1    
        }
        
        return -1
    }
    
    // -- Trimmer --
    trimfront(exp, k=0){
        let i = 0
        let ret = []
        while(i < exp.length){
            i += 1
            ret.push([exp.slice(0, i),k])
        }
        return ret
    }
    trimback(exp, k=0){
        let i = 0
        let ret = []
        while(i < exp.length){
            let checkbr = this.getBr(exp)
            if(checkbr.index == i){
                i = this.getBranchEnd(exp,checkbr)
                continue
            }
            ret.push([exp.slice(i,exp.length),k+i])
            i += 1
        }
        return ret
    }

    //ideally, first call of trimbranchfront should have branch as the first operation
    trimbranchfront(exp, k =0){
        let i = 0
        let ret = []
        let sub = []
        let check 
        while(exp[i]){
            let checkbr = this.getBr(exp.slice(0,i+1), false)

            if(checkbr.index == i){
                check = checkbr

                let range = this.getBranchEnd(exp,checkbr)
                let branchexp = this.cloneExp(exp.slice(i, range))
                let br = this.getBr(branchexp)
                let [topexp, botexp] = this.getTopBot(branchexp,br)
                let trimbackt = this.trimbranchfront(topexp, k+i+1)
                let trimbackb = this.trimbranchfront(botexp, k+i+1 + topexp.length)
                let topbr = this.getBr(topexp)
                let botbr = this.getBr(botexp)
                sub = sub.concat(trimbackt[1])
                sub = sub.concat(trimbackb[1])

                if(topbr.index != -1){
                    sub = sub.concat(trimbackt[0].slice(0,trimbackt[0].length-1))
                }
                if(botbr.index != -1){
                    sub = sub.concat(trimbackb[0].slice(0,trimbackb[0].length-1))
                }
                let topsub = [[[],i]].concat(trimbackt[0])
                let botsub = [[[],i]].concat(trimbackb[0])

                if(checkbr.br == '#100'){
                    branchexp[0].Opparam[0] = '#101'
                }
                let frontexp = exp.slice(0,i)

                for(const topexp of topsub){
                    for(const botexp of botsub){
                        let brexp = this.updateBr(this.cloneExp(branchexp), topexp[0], botexp[0], br)
                        let updatedbrexp = frontexp.concat(brexp)
                        ret.push([updatedbrexp, k])
                    }
                }
                i = range
                
                if(checkbr.br == '#100'){
                    branchexp[0].Opparam[0] = '#100'
                    ret.push([exp.slice(0,i), k])
                }
            }
            else{                
                i += 1 
                let fexp = [exp.slice(0,i), k]
                ret.push(fexp)
            }
        }
        if(!check){
            let frontsub = this.trimfront(exp,k)
            sub = sub.concat(frontsub)
        }
        return [ret, sub] 
    }

    trimbranchback(exp, k = 0){
        let i = exp.length-1
        let ret = []
        let sub = []
        let check
        while(i >= 0){
            let checkbr = this.getBr(exp.slice(0,i+1), false)
            let range = this.getBranchEnd(exp,checkbr)
            if(checkbr.index <= i && i < range && checkbr.index != -1){
                //prepare top and bototm expression, get br operation, and recursive step
                check = checkbr
                let branchexp = this.cloneExp(exp.slice(checkbr.index, range))
                let br = this.getBr(branchexp)
                let [topexp, botexp] = this.getTopBot(branchexp,br)

                let trimbackt = this.trimbranchback(topexp, checkbr.index + k + 1)
                let trimbackb = this.trimbranchback(botexp, checkbr.index + k + topexp.length + 1)

                //check if this was the last branch (no next br), if we are in the last then add
                //top and bot sub, which contains trimback of the highest dimension expressions
                //if top or bot has branch, then add its branch variants as sub exp as well
                let topbr = this.getBr(topexp)
                let botbr = this.getBr(botexp)
                sub = sub.concat(trimbackt[1])
                sub = sub.concat(trimbackb[1])

                if(topbr.index != -1){
                    sub = sub.concat(trimbackt[0].slice(0,trimbackt[0].length-1))
                }
                if(botbr.index != -1){
                    sub = sub.concat(trimbackb[0].slice(0,trimbackb[0].length-1))
                }

                //constructing branch variant with next branchs' variants
                let topsub = [[[],i]].concat(trimbackt[0])
                let botsub = [[[],i]].concat(trimbackb[0])

                //#102 represents back branch
                let tempoperator = branchexp[0].operator
                let tempoperands = this.deepClone(branchexp[0].operands)
                if(checkbr.br == '#100'){
                    branchexp[0].Opparam[0] = '#102'
                    branchexp[0].operator = ''
                    branchexp[0].operands = []
                }
                let backexp = exp.slice(i+1, exp.length)
                for(const topexp of topsub){
                    for(const botexp of botsub){
                        let brexp = this.updateBr(this.cloneExp(branchexp), topexp[0], botexp[0], br)
                        let updatedbrexp = brexp.concat(backexp)
                        ret.push([updatedbrexp, k+checkbr.index])
                    }
                }
                i = checkbr.index-1
                //pushing identity
                if(checkbr.br == '#100'){
                    branchexp[0].Opparam[0] = '#100'
                    branchexp[0].operator = tempoperator
                    branchexp[0].operands = tempoperands
                    ret.push([branchexp, k+checkbr.index])
                }
            }
            else{
                let nexp = exp.slice(i, exp.length)
                ret.push([nexp, k+i])
                i -= 1 
            }
        }
        // normal expression, return trimback
        if(!check){
            let frontsub = this.trimback(exp,k).slice(1,exp.length)
            sub = sub.concat(frontsub)
        }
        return [ret, sub] 
    }

    getsubnorm(exp, k=0){
        let i =0 
        let ret = []
        while(exp[i]){
            ret = ret.concat(this.trimfront(exp.slice(i, exp.length), k+i))
            i+=1
        }
        return ret
    }

    getsub(exp){
        let i = 0
        let ret = []
        let sublist = []
        let check
        while(i < exp.length){
            // console.log(i)
            let sub = exp.slice(i,exp.length)
            let checkbr = this.getBr(sub)
            if(checkbr.index != -1){
                check = checkbr
                let bend = this.getBranchEnd(sub, checkbr)
                let front = exp.slice(i, checkbr.index+i)
                let brexp = sub.slice(checkbr.index, bend) 
                let subf = this.trimback(front).concat([[[],checkbr.index]])
                let brsubf = this.trimbranchfront(brexp, checkbr.index)
                for(const x of subf){
                    for(const y of brsubf[0]){
                        ret.push([x[0].concat(y[0]), x[1]+i])
                    }
                }

                i += bend
                let nextbr = this.getBr(exp.slice(i, exp.length))
                let endi = nextbr.index == -1 ? exp.length : i + nextbr.index

                let back = exp.slice(i, endi)                    
                let subb = [[[],checkbr.index]].concat(this.trimfront(back))
                let brsubb = this.trimbranchback(brexp, checkbr.index)

                for(const x of brsubb[0]){
                    for (const y of subb){
                        ret.push([x[0].concat(y[0]), x[1]+i-bend])
                    }
                }
               
                for(const x of brsubf[1]){
                    sublist.push([x[0], x[1] + i -bend])
                }
                for(const x of brsubb[1]){
                    sublist.push([x[0], x[1] + i -bend])
                }
                // sublist = sublist.concat(brsubf[1]).concat(brsubb[1])
                sublist = sublist.concat(this.getsubnorm(front, i-bend)).concat(this.getsubnorm(back, i))
            }
            else{
                i += 1
            }

        }
        if(!check){
            ret=ret.concat(this.getsubnorm(exp))
        }
        if(check){
            let comb = this.getbranchsubcomb(ret)
            ret = ret.concat(comb)
        }
        return [ret, sublist]
    }

    getbranchsubcomb(list){
        let ret = []
        for(const sub1 of list){
            // console.log(this.ExpToString(sub1[0]))
            let sub1br = this.getBr(sub1[0])
            if(sub1br.index != -1 && sub1br.br != '#101'){
                for(const sub2 of list){
                    // console.log(this.ExpToString(sub2[0]))

                    let sub2br = this.getBr(sub2[0])
                    if(sub2br.index != -1 && sub2br.br != '#102'){

                        if(sub2[1]+ sub2br.index > sub1[1] + sub1br.index){
                            // console.log(sub1[1],sub2[1],this.ExpToString(sub1[0]))

                            ret.push([sub1[0].concat(sub2[0]), sub1[1]])
                        }
                    }
                }
            }
        }
        return ret 
    }

    hasCV(exps){
        for(const a of exps){
            if(this.parser.cv == a.operator) return true
        }
        return false
    }

    flipKeyandValue(table){
        let rettable = {}
        for(const [key, value] of Object.entries(table)){
            rettable[value] = parseInt(key)
        }
        return rettable 
    }

    FilterAxioms(axioms, filter){
        let ret = []
        for(const r of axioms){
            let leftlen = r.leftexps[0].operator=='#0' ? 0 : r.leftexps.length
            let rightlen =  r.rightexps[0].operator=='#0' ? 0 : r.rightexps.length

            if(typeof filter === 'number'){
                let rdiff = Math.abs(leftlen - rightlen)
                if(rdiff == filter) ret.push(r)
            }
            else if(typeof filter === 'string'){
                if(this.ExpToString(r.leftexps).includes(' '+filter+' ') || this.ExpToString(r.rightexps).includes(' '+filter+' ')){
                    ret.push(r)
                }
            }
        }
        return ret
    }

    MatchandCheck(src, tar,debug =false){
        // this.PrintAllRules()
        let nsrc = src
        if(this.ExpToString(src).includes(' #0 ') && src.length == 1){
            nsrc = []
        }
        let srcsubs = this.getsub(nsrc)
        let srcexps = srcsubs[0].concat(srcsubs[1])
        let srcexpsnonil = [...srcexps]

        let tarsubs = this.getsub(tar)

        srcexps = this.addEmpty(srcexps)
        // srcexps = this.sort_subexp(srcexps)

        let lendiff = Math.abs(nsrc.length - tar.length)
        let lenRules = this.FilterAxioms(this.allrules, lendiff)
        let cvRules = this.FilterAxioms(this.allrules, this.parser.cv)
        for(const x of srcexpsnonil){
            // console.log('x: ', this.ExpToString(x[0]))
        }
        
        for(const rule of cvRules){
            if(this.MatchCv(this.cloneExp(rule.leftexps), this.cloneExp(rule.rightexps), nsrc, tar, srcexpsnonil)) 
            {
                
                if(debug){
                    console.log('   Proving --> MatchCV    rule: ', this.RuleToString(rule))                    
                }
                return true
            }
        }

        //we filter the axioms by having the same difference in length as the statement


        for(const rule of lenRules){
            for(const sub of srcexps){

                if(this.CheckFromRules(rule, sub, nsrc, tar, debug)){
                    if(debug){
                        console.log('   Proving --> CheckFromRules    rule: ', this.RuleToString(rule))                    

                    } 
                    return true
                }
            }

        }
        return false
    }
    GetAllVariance(lst, choice=lst.length){
        let ret = []
        if(choice == 0){
            return [ret]
        }
        if(lst.length == 1 ){
            return [lst]
        }
        else{
            for(let i = 0; i < lst.length; i ++){
                let item = [lst[i]]
                let rmlst = lst.slice(0,i).concat(lst.slice(i+1, lst.length))
                let nextlv = this.GetAllVariance(rmlst, choice-1)
                //take all the list from the next level and concat the removed element to every list.
                //if rule expression has less unique operands than subexp then skip the first n level where n is the difference

                for(const l of nextlv) {
                    ret.push(item.concat(l))
                }    
                
            }
        }
        return ret
    }

    //return a list of all independent operands in the expression
    // ex. , #7 1 2, #4 1, #101 $1 $1 #10 1 2, #4 2, #4 3 ,  --> [1, 2, 3]
    GetAllOperands(exp){
        let ret = []
        for(const opt of exp){
            if (!opt.operands) continue
            for(const opr of opt.operands){
                if(!ret.includes(opr)){
                    ret.push(opr)
                }
            }
        }
        return ret 
    }

    UpdateOperands(exp, comb){
        let nexp = this.cloneExp(exp)
        for(let subi = 0 ; subi < nexp.length; subi++ ){
            if(nexp[subi].operands){
                let ops = nexp[subi].operands
                for(let i = 0; i < ops.length; i++ ){
                    nexp[subi].operands[i] = comb[parseInt(nexp[subi].operands[i])-1]
                }
            }
        }
        return nexp
    }
    ReplaceOperandsVariance(src, combinations){
        let ret = []
        let csrc = this.Operands_normalize_exps(this.cloneExp(src), {})[0]
        for(const comb of combinations){
            let nsrc = this.cloneExp(csrc)
            let sub = this.UpdateOperands(nsrc, comb)
            ret.push(sub)
        }
        return ret
    }
    GetAllOperandsVariance(srcx, tarl, tarr){
        let src = this.GetAllOperands(srcx)
        let tar = this.GetAllOperands(tarl.concat(tarr))
        let combinations = this.GetAllVariance(tar, src.length)
        let ret = this.ReplaceOperandsVariance(srcx, combinations) 

        return ret 
    }

    MatchCv(rl, rr, src, tar, srcsubs, tarsub){
        //record sub operands, sub is not be normalized 
        let [trl,trr] = [this.cloneExp(rl), this.cloneExp(rr)]
        //filter subexpressions based on sub index, length, and sameneess of beggining and rest
        // let filteredpair = this.getCVsub(src,tar,srcsub,tarsub)        
        // let filteredpair = [srcsub, tarsub]      
        

        for(const srcsub of srcsubs){

            if(this.hasCV(trl)){     

                let table = this.checkcv(srcsubs,srcsub, rl)                      
                // console.log(this.ExpToString(srcsub[0]), table)

                if(table){
                    let repl = this.replacecvexp({...table},this.cloneExp(rr))
                    let sub = srcsub

                    if(!this.Same(repl, sub[0])){
                        let getAllCombine = this.getAllCombine(repl, sub, src)
                        // let substited = this.substitute(repl,sub,src)
                        
                        for(const substited of getAllCombine){
                            if(this.ExpToString(repl).includes(', #102 $1 $1 , #11 , #11 ,')){
                            console.log('ret: ', this.ExpToString(substited),'|','repl:',this.ExpToString(repl),'sub:',this.ExpToString(sub[0]),'src:', this.ExpToString(src))
                            console.log('rr: ', this.ExpToString(rr),'rl: ', this.ExpToString(rl),{...table}, sub[1])
                            console.log('   ')        
                            }

                        
                            // console.log('substituted: ', this.ExpToString(substited))
                            if(this.Same(substited, tar)){
                                return true 
                            }
                        }
                        
                    }
                   

                    // if(this.substituteCV(pairofsub[1], rr, table)){
                    //     return true
                    // }
                }
            }
            if(this.hasCV(trr)){     
                let table = this.checkcv(srcsubs,srcsub, rr)    
                
                if(table){
                    let repl = this.replacecvexp({...table},this.cloneExp(rl))
                    let sub = srcsub

                    if(!this.Same(repl, sub[0])){
                        let getAllCombine = this.getAllCombine(repl, sub, src)
                        // let substited = this.substitute(repl,sub,src)
                        
                        for(const substited of getAllCombine){
                            if(this.ExpToString(repl).includes(', #102 $1 $1 , #11 , #11 ,')){
                                console.log('ret: ', this.ExpToString(substited),'|','repl:',this.ExpToString(repl),'sub:',this.ExpToString(sub[0]),'src:', this.ExpToString(src))
                                console.log('rr: ', this.ExpToString(rr),'rl: ', this.ExpToString(rl),{...table}, sub[1])
                                console.log('   ')        
                            }
                            // console.log('substituted: ', this.ExpToString(substited))
                            if(this.Same(substited, tar)){
                                return true 
                            }
                        }                  
                    }
                }
            }
        }
            
        return false
    }

    CheckFromRules(rule, sub, src, tar, debug = false, debugdata){
        let sublen = sub[0].length == 0 ? 1 : sub[0].length

        if(sublen != rule.leftexps.length && sublen != rule.rightexps.length) return false

        //it is a good idea to check operator equivalence before operands equivalenec
        let [rl,rr] = [rule.leftexps, rule.rightexps]

        //if no target operands, then generate permutation of all with the replacing expression matching matching all operands in src
        if(this.GetAllOperands(sub[0]).length == 0){

            let oprvariancel = this.GetAllOperandsVariance(rl, src, tar)
            for(const x of oprvariancel){

                if(this.Check(x, sub, src, tar, debug)) return true
            }
            let oprvariancr = this.GetAllOperandsVariance(rr, src, tar)
            for(const x of oprvariancr){

                if(this.Check(x, sub, src, tar, debug)) return true
            }

        }else{

            let [nrl, nrlt] = this.Operands_normalize_exps(this.cloneExp(rl), {})
            let [nrr, nrrt]= this.Operands_normalize_exps(this.cloneExp(rr), {})

            let [nsub, nsub_table] = this.Operands_normalize_exps(this.cloneExp(sub[0]), {})

            if(this.Same(nrl, nsub)){
                
                let table = this.matchDictionaries(this.flipKeyandValue(nrrt), this.flipKeyandValue(this.matchDictionaries(nsub_table, this.flipKeyandValue(nrlt))))



                let repl = this.Operands_normalize_exps(nrr, table)[0]

                if(this.Check(repl, sub, src, tar, debug)) return true
            }
            if(this.Same(nrr, nsub)){
                let table = this.matchDictionaries(this.flipKeyandValue(nrlt), this.flipKeyandValue(this.matchDictionaries(nsub_table, this.flipKeyandValue(nrrt))))

                let repl = this.Operands_normalize_exps(nrl, table)[0]
                
                if(this.Check(repl, sub, src, tar, debug)) return true
            }
        }
        return false
    }

    matchDictionaries(src, tar) {
        const result = {};
        
        for (const srcKey in src) {
            const srcValue = src[srcKey];
        
            for (const tarKey in tar) {
            const tarKeyInt = parseInt(tarKey, 10);
        
            if (tarKeyInt === srcValue) {
                result[srcKey] = tar[tarKey];
                break; // Stop after the first match
            }
            }
        }
    
        return result;
    }

    Check(normalized, sub, src, tar, debug = false){
        let allnew = this.getAllCombine(normalized, sub, src)
        if(debug){
            for(const x of allnew){
            }

        }
        for(const v of allnew){
            if(this.Same(v, tar)){
                return true
            }
        }
        return false
    }

    //getAllCombine takes care of all different ways of substituing when 
    //expression contains branches
    getAllCombine(normalized, sub, src){

        let begin = src.slice(0, sub[1])
        let beginbr = this.getBr(begin, false)

        let all = []
        
        //go to last br 
        if(beginbr.index != -1){
            let [top, bot] = this.getTopBot(src, beginbr)
            let range = this.getBranchEnd(src, beginbr)
            let end = src.slice(range,src.length)
            if(this.ExpToString(normalized).includes(', #102 $1 $1 , #11 , #11 ,')){
                console.log('end: ', this.ExpToString(end))
            }
            if((sub[1] > beginbr.index && sub[1] <= beginbr.index + top.length) 
                || (sub[1] == beginbr.index+top.length+1 && sub[0].length == 0)
            ){

                let ntops = this.getAllCombine(normalized, [sub[0], sub[1]-(beginbr.index+1)], top)
                for(const x of ntops){                    
                    let n = this.updateBr(begin, x, bot, beginbr).concat(end)
                    all.push(n)
                }
            }
            
            if((sub[1] > beginbr.index + top.length  && sub[1] <= beginbr.index + top.length + bot.length) 
                || (sub[1] == beginbr.index + bot.length + top.length+1 && sub[0].length == 0)
            ){

                
                let nbots = this.getAllCombine(normalized, [sub[0], sub[1]-(beginbr.index+top.length+1)], bot)
                for(const x of nbots){
                    let n = this.updateBr(begin, top, x, beginbr).concat(end)

                    all.push(n)
                }                    
            }
                //right after the branch
            if(sub[1] == beginbr.index+top.length+bot.length+1){

                let n = this.substitute(normalized, sub, src)

                all.push(n)
            }
        }
        else{
            //begin starts after all branch closed
            let n = this.substitute(normalized, sub, src)

            all.push(n)
        }
        
        
        return all
    }

    substitute(repl, tsub, src){
        let sub = tsub
        let srcbr = this.getBr(src)
        let offset = srcbr.index
        while(offset != -1 && sub[1] > offset) offset += 1 
        
        if(offset != -1){
            srcbr.index += offset
            srcbr = this.getBr(src.slice(offset, src.length))
        }

        let subbrcheck = this.getBr(sub[0])
        let begin = src.slice(0, sub[1])

        //if src has branch
        if(srcbr.index != -1 && subbrcheck.index != -1){
            //if sub has branch

            let rest = this.getRest(src,sub[0])
            let combine

            // if(repl[0] && repl[0].Opparam[0] == '#102'){
            //     console.log('repl:',this.ExpToString(repl),'sub:',this.ExpToString(sub[0]),'src:', this.ExpToString(src))
            //     combine = this.CombineExp(rest,repl)
            // }else{
                combine= this.CombineExp(repl, rest)
            // }
            let x = begin.concat(combine)

            return x 
        }else{
            return begin.concat(repl).concat(src.slice(sub[1]+sub[0].length, src.length))
        }
    }

    CombineExp(src, tar, getback = false){
        let srcbr = this.getBr(src)
        let tarbr = this.getBr(tar)
        if(srcbr.index != -1 && tarbr.index != -1){
            let [srctop, srcbot] = this.getTopBot(src, srcbr)
            let [tartop, tarbot] = this.getTopBot(tar, tarbr)
            let begin = src.slice(0,srcbr.index+1)
            let tarbegin = tar.slice(0, tarbr.index+1)
            let range = this.getBranchEnd(src, srcbr)
            let endtrim = src.slice(range, src.length)
            
            if((srcbr.br == '#100' || srcbr.br == '#101') && (tarbr.br == '#101'|| tarbr.br == '#100')){
                let topcombine = this.CombineExp(srctop, tartop)
                let botcombine = this.CombineExp(srcbot, tarbot)
                let ret = this.updateBr(begin, topcombine, botcombine,srcbr).concat(endtrim)

                return ret
            }
            else if((srcbr.br == '#100' || srcbr.br == '#102') && (tarbr.br == '#102' || tarbr.br == '#100')){
                let topcombine = this.CombineExp(srctop, tartop, true)
                let botcombine = this.CombineExp(srcbot, tarbot, true)
                let ret =  this.updateBr(tarbegin, topcombine, botcombine,tarbr).concat(endtrim)

                return ret

            }else if(srcbr.br == '#101' && tarbr.br == '#102'){
                // throw new Error('error in CombineExp')
                // console.log(srcbr.index)

                let topcombine = this.CombineExp(srctop, tartop)
                let botcombine = this.CombineExp(srcbot, tarbot)
                let ret = this.updateBr(begin, topcombine, botcombine,srcbr).concat(endtrim)
                ret[srcbr.index].Opparam[0] = '#100'

                return ret
                
            }
            else{
                return src
            }
        }
        else{
            if(getback){
                return tar.concat(src)
            }else{
                return src.concat(tar)
            }
        }
    }

    getRest(exp, sub, getback = false){
        let subbr = this.getBr(sub)
        let expbr = this.getBr(exp)
        if(subbr.index != -1 && expbr.index != -1){
            // console.log(this.ExpToString(exp), this.ExpToString(sub),getback)
            let [subtop, subbot] = this.getTopBot(sub, subbr)
            let [exptop, expbot] = this.getTopBot(exp, expbr)
            if((expbr.br == '#101'|| expbr.br =='#100') && (subbr.br == '#101'|| subbr.br =='#100')){
                let toprest = this.getRest(exptop, subtop)
                let botrest = this.getRest(expbot, subbot)
                let range = this.getBranchEnd(exp, expbr)
                let endtrim = exp.slice(range,exp.length)
                let subbr2 = this.getBr([exp[expbr.index]])
                let ret = this.updateBr([sub[subbr.index]], toprest, botrest, subbr2).concat(endtrim)
                if(expbr.br == '#100' && subbr.br == '#101'){
                    //if exp contains #100, and subbr is #101, then the rest expression contains #102
                    ret[subbr2.index].Opparam[0] = '#102'
                    ret[subbr2.index].operator = null
                    ret[subbr2.index].operands = []
                    return ret
                }
                else if(toprest.length == 0 && botrest.length == 0) return endtrim
                else return ret
            }else if((expbr.br == '#102'|| expbr.br =='#100') && (subbr.br == '#102'|| subbr.br =='#100')){
                let toprest = this.getRest(exptop, subtop, true)
                let botrest = this.getRest(expbot, subbot, true)
                let begintrim = exp.slice(0, expbr.index+1)
                // let endtrim = this.cloneExp(exp.slice(this.getBranchEnd(exp, expbr), exp.length))
                let ret = this.updateBr(begintrim, toprest, botrest, subbr)
                let subbr2 = this.getBr([exp[expbr.index]])

                if(expbr.br == '#100' && subbr.br == '#102'){
                    //if exp contains #100, and subbr is #101, then the rest expression contains #102
                    ret[subbr2.index].Opparam[0] = '#100'
                    return ret
                }
                return ret
            }
            else{               
                console.log('exp: ', this.ExpToString(exp))
                console.log('sub: ', this.ExpToString(sub[0]))
                throw new Error('error in getRest')
                // return exp

            }
        }else{
            if(!getback) {
                return exp.slice(sub.length, exp.length)                
            }else{

                return exp.slice(0, exp.length - sub.length)                
            }
        }
    }

    addEmpty(subexps){
        let max = 0
        for(const x of subexps){
            if (x[1] > max) max = x[1]
        }
        if(subexps.length != 0) max += 1
        let i = 0
        while(i <= max){
            subexps.push([[], i])
            i += 1
        }
        return subexps
    }

    getNumOpt(exp){
        let i = 0 
        let count = 0
        while(i < exp.length){
            if(exp[i].Opparam){
                if(exp[i].Opparam[0]){
                    i += parseInt(exp[i].Opparam[1][1]) + parseInt(exp[i].Opparam[2][1])
                }
            }
            i += 1
            count += 1
        }
        return count
    }

    getBranchEnd(exp, br){
        if(br.index == -1) return 0  
        let i = br.index
        let end = br.index + 1
        while(i < end){
            if(exp[i]){
                if(exp[i].Opparam){
                    if(exp[i].Opparam[0]){
                        end += parseInt(exp[i].Opparam[1][1]) + parseInt(exp[i].Opparam[2][1])
                    }
                }
            }
            i+= 1
        }
        return end
    }

    getTopBot(exp, br){
        if(br.top == 0 && br.bot == 0 ) return [[],[]] 
        if(br.index == -1) return [[],[]] 
        let topend = br.index + br.top
        let t = br.index +1
        let top = []
        let bot =[]

        while(t <= topend){
            if(!exp[t]) break
            top.push(exp[t])
            if(exp[t].Opparam){
                if(exp[t].Opparam[0]){
                    topend += parseInt(exp[t].Opparam[1][1]) + parseInt(exp[t].Opparam[2][1])
                }
            }
            t += 1   
        }
        let botend = topend + br.bot 

        while(t <= botend){
            if(!exp[t]) break
            bot.push(exp[t])
            if(exp[t].Opparam){
                if(exp[t].Opparam[0]){
                    botend += parseInt(exp[t].Opparam[1][1]) + parseInt(exp[t].Opparam[2][1])
                }
            }
            t += 1
            
        }
        return [top,bot]
    }
    updateBr(texp, topexp, botexp, br){
        let exp = this.cloneExp(texp.slice(0,texp.length))

        if(br.index == -1) return exp
        let [top, bot] = this.getTopBot(exp, br)
        let range = top.length + bot.length
        let end = exp.slice(br.index + range + 1, exp.length)

        exp = exp.slice(0, br.index+1).concat(topexp).concat(botexp).concat(end)
        exp[br.index].Opparam[1] = '$'+ this.getNumOpt(topexp).toString()
        exp[br.index].Opparam[2] = '$'+ this.getNumOpt(botexp).toString()
        return exp
    }

    //return the longest string that is different and between two strings
    //same thing as maximizing the length of left and right 
    getBr(exp, first = true){
        let br = {index : -1, next : {}, prev:-1, bot:exp.length, top:exp.length, br: ''}
        if(exp.length == 0) return br
        let broffset = 0 
        let ti = 0
        while(ti < exp.length) {
            if(exp[ti]){
                if(exp[ti].Opparam){
                    if(exp[ti].Opparam[0]){
                        if(this.BrOperators.includes(exp[ti].Opparam[0])){
                            if(first) {
                                return {index : ti, next : {}, prev:br, top: parseInt(exp[ti].Opparam[1][1]), bot:parseInt(exp[ti].Opparam[2][1]), br: exp[ti].Opparam[0]}
                            }else{
                                if(br.index == -1 || ti > broffset + br.index+br.bot + br.top ){
                                    br = {index : ti, next : {}, prev:br, top: parseInt(exp[ti].Opparam[1][1]), bot:parseInt(exp[ti].Opparam[2][1]), br: exp[ti].Opparam[0]}
                                }
                                else{
                                    broffset += parseInt(exp[ti].Opparam[2][1]) + parseInt(exp[ti].Opparam[1][1])
                                }
                            }
                        }
                    }
                }
            }
            ti +=1
        }
        return br 
    }
    getLastBr(exp){
        let br = {index : -1, next : {}, prev:-1, bot:-1, top:-1, br: ''}
        let ti = 0
        let broffset = 0 
        while(ti < exp.length) {
            if(exp[ti].Opparam){
                if(exp[ti].Opparam[0]){
                    if(this.BrOperators.includes(exp[ti].Opparam[0])){
                        if(ti > broffset + br.index+br.bot + br.top ){
                            br = {index : ti, next : {}, prev:br, top: parseInt(exp[ti].Opparam[1][1]), bot:parseInt(exp[ti].Opparam[2][1]), br: exp[ti].Opparam[0]}
                        }
                        else{
                            broffset += parseInt(exp[ti].Opparam[2][1]) + parseInt(exp[ti].Opparam[1][1])
                        }
                    }
                }
            }
            ti +=1
        }
        return br 
    }

    getMaxOpr(exp){
        let max = 0
        for(let i = 0 ; i < exp.length ; i ++){
            if(exp[i].operands){
                for(let j = 0; j < exp[i].operands.length ; j ++){
                    let opr = parseInt(exp[i].operands[j])
                    if(opr >= max){
                        max = opr
                    }
                }
            }
        }
        return max
    }
    //this is useful for matching operands of beginning or end expression of a proof
    IncOperands(Exp, offset= 1){
        let exp = this.cloneExp(Exp)
        let max = this.getMaxOpr(exp)
        // console.log(this.ExpToString(Exp), max)
        for(let i = 0 ; i < exp.length ; i ++){
            if(exp[i].operands){
                for(let j = 0; j < exp[i].operands.length ; j ++){
                    let opr = parseInt(exp[i].operands[j])
                    if(opr+offset > max){
                        exp[i].operands[j] = (opr+offset-max).toString()

                    }else{
                        exp[i].operands[j] = (opr + offset).toString()

                    }
                }
            }
        }
        return exp
    }

    Operands_normalize_exps(srcexps, table) {
        if(!srcexps) return [srcexps, temp_table]
        let exps = this.cloneExp(srcexps)
        let temp_table = {...table}
    
        let offset = 1
        let ret = []

        for(const exp of exps){
            let ret_exp = exp

            if(ret_exp.operands){
                if(ret_exp.operands.length > 0){
                    let i = 0
                    while(i < ret_exp.operands.length){
                        let operand = ret_exp.operands[i]
                        if(operand){
                            if(!temp_table[operand]){
                                temp_table[operand] = offset 
                                offset += 1
                            }
                            ret_exp.operands[i] = String(temp_table[operand])
                        }
                        i+=1
        
                    }
                }
            }
            
            ret.push(ret_exp)
        }

        return [ret, temp_table]

    }

    getcv(cvtable, exps){
        let i = 0
        while(exps[i]){
            let srcropt = exps[i] 
            if(this.parser.cv == srcropt.operator){
                cvtable[srcropt.operands[0]] = ''
            }
            i += 1
        }
        return cvtable
    }

    ExpressionLength(exp){
        let count = 0
        for(let i = 0; i < exp.length; i ++){
            count += 1
            if(this.isBranch(exp[i])){
                let br = this.getBr(exp.slice(i, i+1))
                br.index = i
                i = this.getBranchEnd(exp, br)
                continue;
            }
        }
        return count 
    }

    replacecvexp(cvtable, expsrc){
        let exps = []
        let br = this.getBr(expsrc)
        let offset = 0
        for(let i = 0 ; i< expsrc.length ; i ++){
            if(br){
                if(br.index != -1 && i > this.getBranchEnd(expsrc, br)){
                    br = br.prev
                }
            }

            if(expsrc[i].operator == this.parser.cv){
                let subexp = []
                if( cvtable[expsrc[i].operands[0]]){
                    subexp = cvtable[expsrc[i].operands[0]]

                }
                if(br.index != -1 && i > br.index){
                    let newlen = this.ExpressionLength(subexp)-1
                    offset += subexp.length -1

                    if(i <= br.index+br.top){
                        exps[br.index].Opparam[1] = '$'+ (parseInt(exps[br.index].Opparam[1][1]) + newlen).toString()
                    }else if( i > br.index + br.top && i <= br.index + br.top + br.bot){
                        exps[br.index].Opparam[2] = '$'+ (parseInt(exps[br.index].Opparam[2][1]) + newlen).toString()
                    }
                    
                }
                exps = this.cloneExp(exps.concat(subexp))

            }else{
                exps.push(expsrc[i])

                if(this.isBranch(expsrc[i])){
                    br = this.getBr(expsrc.slice(i, expsrc.length))
                    br.index += i + offset
                }
            }
        }
        return exps
    }

    NonCvOptCount(tarexp){
        let count = 0
        for(let i =0; i<tarexp.length; i++){
            if(tarexp[i].operator != this.parser.cv){
                count += 1
            }
        }
        return count
    }

    generateCombinations(len, sum) {
        const result = [];
    
        function backtrack(current, remainingSum) {
            if (current.length === len) {
                if (remainingSum === 0) {
                    result.push([...current]);
                }
                return;
            }
    
            for (let i = 0; i <= remainingSum; i++) {
                current.push(i);
                backtrack(current, remainingSum - i);
                current.pop();
            }
        }
    
        backtrack([], sum);
        return result;
    }

    FilterExpLen(len, allsub){
        let allfiltersub = []
        for(const sub of allsub){
            if(sub[0].length <= len ){
                allfiltersub.push(sub)
            }
        }
        allfiltersub = this.sort_subexp(allfiltersub)
        return allfiltersub
    }

    ListOfLen(allfiltersub){
        let listoflen = []
        for(const lists of allfiltersub){
            listoflen.push(lists.length)
        }
        return listoflen
    }

    ObrMatchCbr(src, tar){
        // console.log(srcbr.index,tarbr.index)
        if(src.length != tar.length) return false
        let i = 0
        while(i < src.length) {
            
            if(src[i].Opparam && tar[i].Opparam && src[i].Opparam.length !=0 && tar[i].Opparam.length != 0){
                if(src[i].Opparam[1] != tar[i].Opparam[1] || tar[i].Opparam[1] != src[i].Opparam[2])
                    return false
                let srcbranch = src[i].Opparam[0]
                let tarbranch = tar[i].Opparam[0]
                if(srcbranch != tarbranch){
                    if((srcbranch != '#101' && srcbranch != '#102') && tarbranch != '#100'){
                        return false
                    }
                    if(srcbranch == '#102' && tarbranch == '#101'){
                        return false
                    }
                }
            }else{
                if(!this.Same([src[i]], [tar[i]])){
                    // console.log('   !!! Same:', this.ExpToString([src[i]], [tar[i]]))

                    return false
                }
            }
            i += 1
        }
        return true
    }

    

    generateTableCombinations(keys, lists, sum) {
        const results = [];
        const keyNames = Object.keys(keys);
        const extendedLists = [...lists];

        function helper(index, currentTable, usedIndices, totalLength) {
            if (index === keyNames.length) {
                if (totalLength === sum) {
                    results.push({ ...currentTable });
                }
                return;
            }

            const key = keyNames[index];

            for (let i = 0; i < extendedLists.length; i++) {
                if (usedIndices.has(i)) continue;

                const list = extendedLists[i][0];

                const newLength = totalLength + list.length;
                // console.log(list,newLength)

                if (newLength > sum) continue;

                if(list){
                    currentTable[key] = list;
                }
                else{
                    currentTable[key] = [];
                }
                usedIndices.add(i);

                helper(index + 1, currentTable, usedIndices, newLength);

                usedIndices.delete(i);
                delete currentTable[key];
            }
        }

        helper(0, {}, new Set(), 0);
        return results;
    }

    CheckWithTable(srcsub, tarexp, table, len, allfiltersub){

        let table_comb = this.generateTableCombinations(table, allfiltersub, len)
        // console.log(table_comb.length)
        // for(const table of table_comb){
        //     let sum = 0
        //     for(const [key, value] of Object.entries(table)){
        //         sum += value.length
        //         console.log('key: ',key, 'value: ', value.length)
        //     }
        //     // console.log('sum ', sum)

        // }
        
        for(const table of table_comb){

            let repltar = this.replacecvexp({...table}, this.cloneExp(tarexp))
            
            if(this.ObrMatchCbr(repltar, srcsub[0])){
                return table
            }     
        }
        return false
    }

    getCvPositions(exps){
        let seen = new Set();
        let ret = []
        for(let i = 0; i < exps.length; i ++){
            const char = exps[i].operator
            if(char == this.parser.cv){
                if(!seen.has(char)){
                    ret.push([exps[i].operands[0], i])
                    seen.add(char)
                }
            }
        }
        return ret 
    }

    substituteCV(srcexp, tarexp, table){

        let rettable = this.CheckWithTable(srcexp, tarexp, table)
        if(rettable) return rettable
        else{
            let repltar = this.replacecvexp(table, this.cloneExp(tarexp))
            if(this.ObrMatchCbr(repltar, srcexp)) return table
        }
        return false
    }

    checkcv(allsub, sub, tar){
        let tarexp = this.cloneExp(tar)
        let table = this.getcv({},tarexp)
        // let tablelen = Object.keys(table).length
        let nonCVlen = this.NonCvOptCount(tarexp)
        // let listofsum = this.generateCombinations(tablelen, sub[0].length - nonCVlen)
        let allfiltersub = this.FilterExpLen(sub[0].length - nonCVlen, allsub)



        let rettable = this.CheckWithTable(sub, tarexp, table, sub[0].length - nonCVlen, allfiltersub)
        // if(this.ExpToString(sub[0]).includes(', #102 $0 $0 , #100 $1 $1 #15 3 4 , #13 5 , #13 6 ,') && this.ExpToString(tarexp).includes(', #102 $0 $0 , #13 1 ,')){
        //     console.log(this.ExpToString(sub[0]),'<>',this.ExpToString(tarexp),listofsum, rettable)
        // }
        if(rettable) return rettable
        
        
        return false
    }

    Same(src,tar){
        if(!tar && !src) return true
        let i = 0

        //check length match
        if(src.length != tar.length) return false 
        else {
            while(i < src.length){
                //check operator match
                if(!src[i] || !tar[i]) return false
                if(!src[i].operator ^ !tar[i].operator) {
                    // console.log('^')
                    return false
                }
                if(src[i].operator && tar[i].operator){
                    if(src[i].operator != tar[i].operator) return false 
                }
                //check if Opparam match
                if(src[i].Opparam ^ tar[i].Opparam) return false
                if(src[i].Opparam && tar[i].Opparam){
                    if(src[i].Opparam.length != 0 ^ tar[i].Opparam.length != 0)return false
                    if(src[i].Opparam.length != 0 && tar[i].Opparam.length != 0){
                        let j = 0
                        while(j < src[i].Opparam.length){
                            if(src[i].Opparam[j] != tar[i].Opparam[j]){
                                return false 
                            } 
                            j += 1
                        }
                    }
                }
                
                //check operands match
                if(src[i].operands ^ tar[i].operands)return false
                if(src[i].operands && tar[i].operands){
                    let j = 0
                    if(tar[i].operands.length != src[i].operands.length) return false
                    while(j < src[i].operands.length){
                        if(src[i].operands[j] != tar[i].operands[j]){
                            
                            return false 
                        } 
                        j += 1
                    }
                }

                i += 1
            }
        }

        return true 
    }


    //--Tools--
    //these expression are generate by incrementing operator and generator similar looking expressions
    
    isBranch(opt){
        if(opt.Opparam){
            if(opt.Opparam[0]){
                return true
            }
        }
        return false 
    }

    cloneExp(exp){
        let ret = this.genRule('!,@,'+this.ExpToString(exp)).rightexps
        if(ret[0].operator == '#0') return []
        return ret
    }

    deepClone(arr) {
        return arr.map(innerArr => innerArr.slice());
    }

    Get_all_operator(){
        let operator_table = []
        for(const exp of this.Exps){
            let operator = ''
            if(!exp) continue
            let i = 0
            while(i < exp.length){
                if(exp[i] == '#')
                {
                    while(exp[i] != ' ' && exp[i] != ',' && exp[i] !='}' && exp[i] != '{' && i < exp.length){
                        operator += exp[i]
                        i += 1
                    }
                    operator_table.push(operator)
                    operator = ''
                }
                i += 1
            }
        }
        for(const rule of this.allrules){

            let ruleString = this.RuleToString(rule)
            let operator = ''
            if(!ruleString) continue
            let i = 0
            while(i < ruleString.length){
                if(ruleString[i] == '#')
                {
                    while(ruleString[i] != '!' && ruleString[i] != '@' && ruleString[i] != ' ' && ruleString[i] != ',' && ruleString[i] !='}' && ruleString[i] != '{' && i < ruleString.length){
                        operator += ruleString[i]
                        i += 1
                    }
                    operator_table.push(operator)
                    operator = ''
                }
                i += 1
            }
        }
        let s = new Set(operator_table)
        let sl = Array.from(s)

        return sl
    }


    listequal(src,tar){
        if(src.length != tar.length) return false 
        let i = 0
        while(i<src.length){
            if(src[i] != tar[i]){
                return false
            }
            i+=1
        }
        return true
    }

    AddSpacetoExp(){
        let line = ''
        let ret = []
        for(const exp of this.Exps){
           for(const c of exp){
                if(c == ',') line += ' '
                line += c
            } 
            ret.push(line.trim())
            line = ''
        }
        this.Exps = ret 
        
    }

    PrintAllRules(){
        for(const rule of this.allrules){
            console.log(this.RuleToString(rule))
        }
    }
    PrintAllExps(){
        for(const exp of this.Exps){
            console.log(exp)
        }
    }
    RuleToString(rule) {
        let leftexps = rule.leftexps
        let rightexps = rule.rightexps
        if(!leftexps || !rightexps) return ''

        let left = this.ExpToString(leftexps)
        let right = this.ExpToString(rightexps)

        return  left + '@ ' + right
    }
    ExpToString(exps) {
        let ret = ', '
        if(!exps) return ret
        for (const exp of exps){
            
            if(exp.Opparam && exp.Opparam.length != 0){
                ret += exp.Opparam[0] + ' ' + exp.Opparam[1] +  ' ' +  exp.Opparam[2] + ' '
            }
            if(exp.operator  && exp.operator != ''){
                if(exp.operator == '@') continue
                ret += exp.operator + ' '
            }
            if(exp.operands && exp.operands.length > 0){
                for(const opr of exp.operands){
                    if(opr !== undefined) {
                        ret += opr + ' '
                    }
                }
            }
            if(exp != '')
                ret += ', '
        }
        return ret
    }
    deepClone(arr){
        return arr.map(innerArr => innerArr.slice());
    }
    sort_subexp(lst){
        let sortedlst = this.deepClone(lst)
        let i = 0 
        while(sortedlst[i]){
            let j = 0 
            while(sortedlst[j]){
                if(sortedlst[i][1] <= sortedlst[j][1]){
                    let x = [...sortedlst[i]]
                    sortedlst[i] = [...sortedlst[j]]
                    sortedlst[j] = [...x]
                }
                j+=1
            }
            i+=1
        }
        return sortedlst
    }
    
    genRule(rule){
        return this.parser.Parse(rule)
    }
    AddRule(ret){
        this.allrules.push(ret)
    }
    getAllRules(){
        return this.allrules
    }
    
}

export default ProofAssistant