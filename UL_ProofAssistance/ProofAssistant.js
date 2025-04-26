



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
            console.log('start: ', start, 'end: ', end)
        }
        let tempv = this.genRule('!'+start+'@'+end)
        if (this.Same(tempv.leftexps, tempv.rightexps)) return 1
        if(!this.isRule(tempv)){
            // console.log('start!')
            if(this.MatchandCheck(tempv.leftexps, tempv.rightexps, debug)) {
                return 1    
            }
            else{
                return -1
            }
        }
        else{
            if(debug){
                console.log('isrule!: ', this.RuleToString(tempv))
            }
            return 1
        }
    }
    

    isBranch(opt){
        if(opt.Opparam){
            if(opt.Opparam[0]){
                return true
            }
        }
        return false 
    }


    try_match_operand_order(parsed_newrule) {
        let src = parsed_newrule.leftexps
        let tar = parsed_newrule.rightexps
        if(!tar || !src) return false
        let endmax = this.getmax(tar)
        if(endmax == 0) return [parsed_newrule]
        let endmaxcounter= 0
        let ret = []
        while(endmaxcounter < endmax){
            if(tar.length == 0) break

            let target = this.ExpToString(this.permuteOperands(tar))
            let tr = '! ' + this.ExpToString(src) + ' @ ' + target
            let parsed_tr = this.genRule(tr)
            ret.push(parsed_tr)
            
            endmaxcounter += 1
        }

        return ret
    }

    cloneExp(exp){
        let ret = this.genRule('!,@,'+this.ExpToString(exp)).rightexps
        if(ret[0].operator == '#0') return []
        return ret
    }

    deepClone(arr) {
        return arr.map(innerArr => innerArr.slice());
    }

    // does not work with branch expression
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
            let checkbr = this.getFirstBr(exp)
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
            let checkbr = this.getLastBr(exp.slice(0,i+1))

            if(checkbr.index == i){
                check = checkbr

                let range = this.getBranchEnd(exp,checkbr)
                let branchexp = this.cloneExp(exp.slice(i, range))
                let br = this.getFirstBr(branchexp)
                let [topexp, botexp] = this.getTopBot(branchexp,br)
                let trimbackt = this.trimbranchfront(topexp, k+i+1)
                let trimbackb = this.trimbranchfront(botexp, k+i+1 + topexp.length)
                let topbr = this.getFirstBr(topexp)
                let botbr = this.getFirstBr(botexp)
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
            let checkbr = this.getLastBr(exp.slice(0,i+1))
            let range = this.getBranchEnd(exp,checkbr)
            if(checkbr.index <= i && i < range && checkbr.index != -1){
                //prepare top and bototm expression, get br operation, and recursive step
                check = checkbr
                let branchexp = this.cloneExp(exp.slice(checkbr.index, range))
                let br = this.getFirstBr(branchexp)
                let [topexp, botexp] = this.getTopBot(branchexp,br)

                let trimbackt = this.trimbranchback(topexp, checkbr.index + k + 1)
                let trimbackb = this.trimbranchback(botexp, checkbr.index + k + topexp.length + 1)

                //check if this was the last branch (no next br), if we are in the last then add
                //top and bot sub, which contains trimback of the highest dimension expressions
                //if top or bot has branch, then add its branch variants as sub exp as well
                let topbr = this.getFirstBr(topexp)
                let botbr = this.getFirstBr(botexp)
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

                // console.log('exp: ', this.ExpToString(exp), 'checkbr: ', checkbr)

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
            let sub = exp.slice(i,exp.length)
            let checkbr = this.getFirstBr(sub)
            if(checkbr.index != -1){
                check = checkbr
                let bend = this.getBranchEnd(sub, checkbr)
                let front = exp.slice(i, checkbr.index)
                let brexp = sub.slice(checkbr.index, bend) 
                let subf = this.trimback(front).concat([[[],checkbr.index]])
                let brsubf = this.trimbranchfront(brexp, checkbr.index)
                for(const x of subf){
                    for(const y of brsubf[0]){
                        ret.push([x[0].concat(y[0]), x[1]])
                    }
                }

                i += bend
                let nextbr = this.getFirstBr(exp.slice(i, exp.length))
                let endi = nextbr.index == -1 ? exp.length : i + nextbr.index

                let back = exp.slice(i, endi)
                let subb = [[[],checkbr.index]].concat(this.trimfront(back))
                let brsubb = this.trimbranchback(brexp, checkbr.index)

                for(const x of brsubb[0]){
                    for (const y of subb){
                        ret.push([x[0].concat(y[0]), x[1]])
                    }
                }
               
                
                sublist = sublist.concat(brsubf[1]).concat(brsubb[1])
                sublist = sublist.concat(this.getsubnorm(front, i-bend)).concat(this.getsubnorm(back, i))
            }
            else{
                i += 1
            }
        }
        if(!check){
            ret=ret.concat(this.getsubnorm(exp))
        }
        return [ret, sublist]
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

    FilterAxioms(axioms, diff){
        let ret = []
        for(const r of axioms){
            let leftlen = r.leftexps[0].operator=='#0' ? 0 : r.leftexps.length
            let rightlen =  r.rightexps[0].operator=='#0' ? 0 : r.rightexps .length
            let rdiff = Math.abs(leftlen - rightlen)
            // console.log(rdiff)
            if(rdiff == diff) ret.push(r)
        }
        return ret
    }

    MatchandCheck(src, tar,debug =false){
        let [subexps, subexps2] = this.getsub(src)
        subexps = subexps.concat(subexps2)
        subexps = this.addEmpty(subexps)
        subexps = this.sort_subexp(subexps)
        // console.log('expsub X subexps = ', subexps.length * this.allrules.length)
        // let debugdata = subexps.length * this.allrules.length


        //too many processes!!
        //maybe create a temporary axiom list that only contains subexpressions that have the same length of the subexpression
        


        let srclen = src.lengh == 0 ? src.length: src.length
        let tarlen = tar.lengh == 0 ? tar.length: tar.length
        let lendiff = Math.abs(srclen - tarlen)
        // console.log("lendiff", lendiff)
        let revelantAxioms = this.FilterAxioms(this.allrules, lendiff)
        // console.log('!!!', revelantAxioms.length)

        //we filter the axioms by having the same difference in length as the statement
        for(const rule of revelantAxioms){
            if(this.hasCV(rule.leftexps) || this.hasCV(rule.rightexps)) {
                if(this.MatchCv(rule.leftexps, rule.rightexps, src, tar)) return true
            }
            // console.log('rule: ', this.RuleToString(rule))
            //if sublen does not have same length as expressions in rule, then dismiss it
            for(const sub of subexps){
                if(this.CheckFromRules(rule, sub, src, tar, debug)) return true
            }
        }
        return false
    }


    // sub might not be normalized
    // ex.  , #4 3 ,#7 1 2,
    // rules are normalized.

    // left normalization vs right normalization
    // ex. , #4 1 , #4 2, -> ,#4 2, #4 1,
    // ex. , #4 2 , #4 1 -> ,#4 1, #4 2,
    // is normalization semantically correct?
    // yes.

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
                // console.log('!item: ', item)
                let rmlst = lst.slice(0,i).concat(lst.slice(i+1, lst.length))
                let nextlv = this.GetAllVariance(rmlst, choice-1)
                //take all the list from the next level and concat the removed element to every list.
                //if rule expression has less unique operands than subexp then skip the first n level where n is the difference

                for(const l of nextlv) {
                    ret.push(item.concat(l))
                    // console.log('!!!', item.concat(l))
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
        // for(const x of ret){
        //     console.log('x: ', this.ExpToString(x))
        // }
        // console.log()
        return ret 
    }
    

    MatchCv(rl, rr, src, tar){
        //record sub operands, sub is not be normalized 
        let [trl,trr] = [this.cloneExp(rl), this.cloneExp(rr)]
        //check if has cv
        if(this.hasCV(trl)){     
            let table = this.checkcv2(src, rl)    
            // console.log('table: ', table)   
            if(table){
                console.log('table: ', table)   

                if(this.checkcv2(tar, rr, table)){
                    return true
                }
            }
        }
        if(this.hasCV(trr)){
            let table = this.checkcv2(src, rr) 
      
            if(table){
                console.log('table: ', table)   

                if(this.checkcv2(tar, rl, table)){
                    return true
                }
            }
        }

        // if(this.Same(trr, tsub)){
        //     let normalized =this.Operands_normalize_exps(trl, oprtable)[0]

        //     if(this.Check(normalized, sub, src, tar)){
        //         return true 
        //     }
        // }
        return false
    }

    ALlOprVarianceCheck(src, tar, sub, nrl, nrr, debug = false){
        if(sub[0].length == 0){
            let oprvariancel = this.GetAllOperandsVariance(nrl, src, tar)
            for(const x of oprvariancel){
                // console.log('!',this.ExpToString(x))
                if(this.Check(x, sub, src, tar, debug)) return true

            }
            let oprvariancr = this.GetAllOperandsVariance(nrr, src, tar)
            for(const x of oprvariancr){
                // console.log('!',this.ExpToString(x))
                if(this.Check(x, sub, src, tar, debug)) return true

            }
            
        }
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
            // console.log('GetAllOperandsVariance: ', this.ExpToString(sub[0]), oprvariancel.length, oprvariancr.length)
            if(oprvariancel.length > 40000){
                console.log('too many variance: ', this.ExpToString(rr))
            }

        }else{
            let nrl = this.Operands_normalize_exps(this.cloneExp(rl), {})[0]
            let nrr = this.Operands_normalize_exps(this.cloneExp(rr), {})[0]
            let [nsub, nsub_table] = this.Operands_normalize_exps(this.cloneExp(sub[0]), {})
            if(this.Same(nrl, nsub)){
                let convertedrr = this.MatchOperands(nrr, nsub_table)
                if(this.Check(convertedrr, sub, src, tar, debug)) return true
            }
            if(this.Same(nrr, nsub)){
                let convertedrl = this.MatchOperands(nrl, nsub_table)
                if(this.Check(convertedrl, sub, src, tar, debug)) return true
            }
        }
        return false
    }

    MatchOperands(src, table, debug = false){
        let nsub_fliptable = this.flipKeyandValue({...table})
        let norm = this.cloneExp(this.Operands_normalize_exps(this.cloneExp(src), table)[0])
        let oringinal = this.cloneExp(this.Operands_normalize_exps(this.cloneExp(norm), nsub_fliptable)[0])
        if(debug){
            console.log('MatchOperands: ',his.ExpToString(src), '--> ', this.ExpToString(oringinal))
        }
        return oringinal
    }

    Check(normalized, sub, src, tar, debug = false){
        let allnew = this.getAllCombine(normalized, sub, src)
        if(debug){
            // console.log(allnew.length)
            for(const x of allnew){
                // console.log('   getallcombine: ', this.ExpToString(x))
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
        let beginbr = this.getLastBr(begin)
        let all = []
        //go to last br 
        if(beginbr.index != -1){
            let [top, bot] = this.getTopBot(src, beginbr)
            let range = this.getBranchEnd(src, beginbr)
            let end = src.slice(range,src.length)

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
                let n = this.substitute(normalized, [sub[0], sub[1]], src)
                all.push(n)
            }
        }
        else{
            //begin starts after all branch closed
            let n = this.substitute(normalized, [sub[0], sub[1]], src)
            all.push(n)
        }
        
        return all
    }

    substitute(repl, tsub, src){
        let sub = tsub
        let srcbr = this.getFirstBr(src)
        let offset = srcbr.index
        while(offset != -1 && sub[1] > offset) offset += 1 
        
        if(offset != -1){
            srcbr.index += offset
            srcbr = this.getFirstBr(src.slice(offset, src.length))
        }

        let subbrcheck = this.getFirstBr(sub[0])
        let begin = src.slice(0, sub[1])

        //if src has branch
        if(srcbr.index != -1 && subbrcheck.index != -1){
            //if sub has branch
                let brrange = this.getBranchEnd(src, srcbr)
                let end = src.slice(brrange+1,src.length)
                let rest = this.getRest(src,sub[0])
                // console.log('   intorest: ', this.ExpToString(src.slice(srcbr.index, brrange)))
                // console.log('   begin: ', this.ExpToString(begin), 'src: ', this.ExpToString(src), 'sub[1]: ', sub[1], 'sub[0]', this.ExpToString(sub[0]), 'rest: ', this.ExpToString(rest), 'repl: ', this.ExpToString(repl), )
                let combine = this.CombineExp(repl, rest)
                // console.log('   !combine: ', this.ExpToString(combine), this.ExpToString(end))
                let x = begin.concat(combine)
                // console.log('x: ', this.ExpToString(x))
                return x 
        }else{
            return begin.concat(repl).concat(src.slice(sub[1]+sub[0].length, src.length))
        }
    }

    CombineExp(src, tar, getback = false){
        let srcbr = this.getFirstBr(src)
        let tarbr = this.getFirstBr(tar)
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
                let ret = this.updateBr(tarbegin, topcombine, botcombine,tarbr).concat(endtrim)
                ret[tarbr.index].Opparam[0] = '#100'
                ret[tarbr.index].operator = src[srcbr.index].operator
                ret[tarbr.index].operands = src[srcbr.index].operands
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
        let subbr = this.getFirstBr(sub)
        let expbr = this.getFirstBr(exp)
        if(subbr.index != -1 && expbr.index != -1){
            let [subtop, subbot] = this.getTopBot(sub, subbr)
            let [exptop, expbot] = this.getTopBot(exp, expbr)
            if((expbr.br == '#101'|| expbr.br =='#100') && (subbr.br == '#101'|| subbr.br =='#100')){
                let toprest = this.getRest(exptop, subtop)
                let botrest = this.getRest(expbot, subbot)
                let range = this.getBranchEnd(exp, expbr)
                let endtrim = exp.slice(range,exp.length)
                let subbr2 = this.getFirstBr([exp[expbr.index]])
                let ret = this.updateBr([sub[subbr.index]], toprest, botrest, subbr2).concat(endtrim)
                if(expbr.br == '#100' && subbr.br == '#101'){
                    //if exp contains #100, and subbr is #101, then the rest expression contains #102
                    ret[subbr.index].Opparam[0] = '#102'
                    ret[subbr.index].operator = null
                    ret[subbr.index].operands = []
                    return ret
                }
                else if(toprest.length == 0 && botrest.length == 0) return endtrim
                else return ret
            }else if((expbr.br == '#102'|| expbr.br =='#100') && (subbr.br == '#102'|| subbr.br =='#100')){
                let toprest = this.getRest(exptop, subtop, true)
                let botrest = this.getRest(expbot, subbot, true)
                let begintrim = exp.slice(0, expbr.index+1)
                let ret = this.updateBr(begintrim, toprest, botrest, subbr)
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
        return count.toString()
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
        exp[br.index].Opparam[1] = '$'+ this.getNumOpt(topexp)
        exp[br.index].Opparam[2] = '$'+ this.getNumOpt(botexp)
        return exp
    }

    incOperands(exps){
        let i =0
        while(i < exps.length){
            if(exps[i].operands){
                if(exps[i].operands.length>0){
                    let j = 0
                    while(j < exps[i].operands.length){
                        let temp = parseInt(exps[i].operands[j])
                        exps[i].operands[j] = String(temp+1)
                        j += 1
                    }
                }
            }
            i+=1
        }
        return exps 
    }

    permuteOperands(exps){
        let i = 0
        let max = this.getmax(exps)
        let ret = exps
        while(i < ret.length){
            let j = 0
            if(ret[i].operands.length>0){
                while(j < ret[i].operands.length)
                {
                    let temp = parseInt(ret[i].operands[j])
                    if(temp == max){
                        temp = 1
                    }
                    else{
                        temp += 1
                    }
                    ret[i].operands[j] = String(temp)
                    
                    j += 1
                }
            }
            i+=1
        }
        return ret

    }

    //return the longest string that is different and between two strings
    //same thing as maximizing the length of left and right 
    getFirstBr(exp){
        let br = {index : -1, next : {}, prev:-1, bot:exp.length, top:exp.length, br: ''}
        if(exp.length == 0) return br

        let ti = 0
        while(ti < exp.length) {
            if(exp[ti]){
                if(exp[ti].Opparam){
                    if(exp[ti].Opparam[0]){
                        if(this.BrOperators.includes(exp[ti].Opparam[0])){
                            return {index : ti, next : {}, prev:br, top: parseInt(exp[ti].Opparam[1][1]), bot:parseInt(exp[ti].Opparam[2][1]), br: exp[ti].Opparam[0]}
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
    inBranch(br, i) {
        return (br.index > -1) 
        && (i <= br.index+br.top+br.bot) 
        && (i >= br.index) 
    }

    Operands_normalize(rule) {
        let operands_table = {}
        let leftexps = this.Operands_normalize_exps(rule.leftexps, operands_table)[0]
        let rightexps = this.Operands_normalize_exps(rule.rightexps, operands_table)[0]

        return {leftexps: leftexps, rightexps:rightexps}
    
    }

    Operands_normalize_exps(exps, table) {
        if(!exps) return [exps, temp_table]
        let temp_table = table
    
        let offset = 1
        let ret = []

        for(const exp of exps){
            let ret_exp = exp

            if(ret_exp.operands){
                let operands =[]
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
                            operands.push(ret_exp.operands[i])
                        }
                        i+=1
        
                    }
                }
            }
            
            ret.push(ret_exp)
        }

        return [ret, temp_table]

    }

    genPermutation(slength, tlength){
        let i = 0
        let j = 0 
        let ret = []
        while(i < slength){
            while(j < tlength){
                let v = [i,j]
                ret.push(v)
                j+=1
            }
            i+= 1
        }
        return ret
    }

    operationlist(exps){
        let i = 0
        let ret = []
        while(exps[i]){
            let srcropt = exps[i] 
            if(srcropt.Opparam){
                if(srcropt.Opparam.length != 0){
                    i+=1
                     continue
                }else{
                    let opt = [srcropt.operator]
                    if(srcropt.operands){
                        opt = opt.concat(srcropt.operands)
                    }
                    if(!ret.includes(opt)){
                        ret.push(opt)
                    }
                }
            }else{
                let opt = [srcropt.operator]
                if(srcropt.operands){
                    opt = opt.concat(srcropt.operands)
                }
                if(!ret.includes(opt)){
                    ret.push(opt)
                }
            }
            i += 1
        }
        return ret
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
    assigncv(cvtable, optlist, perm){
        let tcvtable = {...cvtable}
        for(const p of perm){
            if(tcvtable[p[0] + 1] == ''){
                let v =''
                for(const c of optlist[p[1]]){
                    v += c + ' '
                }
                tcvtable[(p[0] + 1).toString()] = v.trim()
            }
        }
        return tcvtable
    }

    replacecvexp2(cvtable, expsrc){
        let exps = []
        let br
        let top,bot
        // console.log('replacecvexp2 --> expsrc: ', this.ExpToString(expsrc))
        for(let i = 0 ; i< expsrc.length ; i ++){
            if(br){
                if(i > this.getBranchEnd(expsrc, br)){
                    br = br.prev
                }
            }
            if(expsrc[i].operator == this.parser.cv){
                let subexp = cvtable[expsrc[i].operands[0]]
                if(br){
                    if(i < br.index+br.top+1){
                        top = subexp
                    }else if(i < br.index + br.top + br.bot +1){
                        bot = subexp
                    }
                    exps = this.updateBr(exps,top,bot,br)
                }else{
                    exps = exps.concat(subexp)
                }
            }else{
                exps.push(expsrc[i])

                if(this.isBranch(expsrc[i])){
                    br = this.getFirstBr(expsrc.slice(i, i+1))
                    br.index = i
                    let topbot = this.getTopBot(expsrc,br)
                    top = topbot[0]
                    bot = topbot[1]
                }
            }
        }
        return exps
    }

    replacecvexp(cvtable, expsrc){
        let exps = this.cloneExp(expsrc)
        for(const exp of exps){
            if(exp.operator == this.parser.cv){
                let t = cvtable[exp.operands[0]].split(' ')
                exp.operator = t[0]
                exp.operands = t.slice(1,t.length)
            }
        }
        return exps
    }
    replacecv(cvtable, rule){
        let retr = this.genRule('!'+this.ExpToString(rule.leftexps) + '@' + this.ExpToString(rule.rightexps))
        retr.leftexps = this.replacecvexp(cvtable, retr.leftexps)
        retr.rightexps = this.replacecvexp(cvtable, retr.rightexps)
        return retr 
    }

    //if true, then every constant operator appears in srcexp, which means 
    CVTest(srcexp, tarexp){
        let count = 0
        //if rule is longer, then there is no matches that can make srcexp tarexp the same
        if(tarexp.length > srcexp.length) return false 
        for(let i =0; i<tarexp.length; i++){
            if(tarexp[i].operator != this.parser.cv){
                // console.log('!',srcexp.slice(i, srcexp.length))
                if(!this.ExpToString(srcexp.slice(i, srcexp.length)).includes(' '+tarexp[i].operator.trim()+' ')){
                    return false
                }
                if(tarexp[i].Opparam && tarexp[i].Opparam.length > 0){
                    if(tarexp[i].Opparam[0] == '#101' || tarexp[i].Opparam[0] == '#102'){
                        if(!this.ExpToString(srcexp.slice(i, srcexp.length)).includes(' #100 ')){
                            return false
                        }
                    }else if(!this.ExpToString(srcexp.slice(i, srcexp.length)).includes(' '+tarexp[i].Opparam[0].trim()+' ')){
                        return false
                    }
                }
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

    generateLowerCombinations(input) {
        const result = [];
    
        function backtrack(current, index) {
            if (index === input.length) {
                result.push([...current]);
                return;
            }
    
            for (let i = 0; i < input[index]; i++) {
                current.push(i);
                backtrack(current, index + 1);
                current.pop();
            }
        }
    
        backtrack([], 0);
        return result;
    }

    FilterExpLen(listofsum, allsub){
        let allfiltersub = []
        for(const i of listofsum){
            let samelensub = []
            for(const sub of allsub){
                if(sub[0].length == i ){
                    samelensub.push(sub[0])
                }
            }
            allfiltersub.push(samelensub)
        }
        return allfiltersub
    }

    ListOfLen(allfiltersub){
        let listoflen = []
        for(const sub of allfiltersub){
            listoflen.push(sub.length)
        }
        return listoflen
    }

    CheckWithTable(srcexp, tarexp, cvtable, combs, allfiltersub){
        if(combs && allfiltersub){
            console.log('----------------')
            console.log('srcexp: ', this.ExpToString(srcexp), 'tarexp: ', this.ExpToString(tarexp))
            for(const comb of combs){
                let ttable = {...cvtable}
                Object.keys(cvtable).forEach((key, index) => {
                    ttable[key] = allfiltersub[index][comb[index]]
                })
                let replsrc = this.replacecvexp2(ttable, tarexp)
                // console.log('1replsrc: ', this.ExpToString(replsrc), ttable)
                if(this.Same(replsrc, srcexp)) return ttable
            }
        }else{ 

            // console.log(cvtable)
            let replsrc = this.replacecvexp2(cvtable, tarexp)
            console.log('2replsrc: ', this.ExpToString(replsrc))
            if(this.Same(replsrc, srcexp)) return cvtable
        }
        return false
    }

    checkcv2(srcexp, tarexp, table){
        if(!table){
            let firstcvcheck = this.CVTest(srcexp, tarexp)
            // console.log('firstcheck: ', firstcvcheck)

            if(!firstcvcheck) return false 
            else{
                let getsub = this.getsub(srcexp)
                let allsub = this.sort_subexp(getsub[0].concat(getsub[1]))
                // console.log('allsub: ', allsub)
                

                let cvtable = this.getcv({},tarexp)
                let tablelen = Object.keys(cvtable).length
                let listofsum = this.generateCombinations(tablelen, srcexp.length - firstcvcheck)
                // console.log('listofsum', listofsum, srcexp.length)
                for(const l of listofsum){
                    
                    let allfiltersub = this.FilterExpLen(l, allsub)
                    // for(const x of allfiltersub){
                    //     console.log('   ', this.ExpToString(x[0]))
                    // }
                    // console.log('allfiltersub: ', allfiltersub)
                    let listoflen = this.ListOfLen(allfiltersub)
                    // console.log('listoflen: ', listoflen)
                    let combs = this.generateLowerCombinations(listoflen)
                    // console.log('combs: ', combs)
                    let rettable = this.CheckWithTable(srcexp, tarexp, cvtable, combs, allfiltersub)
                    // console.log(check)
                    if(rettable) return rettable
                }            
            }
        }else{
            // console.log('table: ', table)
            // console.log('srcexp: ', this.ExpToString(srcexp), )
            // console.log('tarexp: ', this.ExpToString(tarexp), )
            let rettable = this.CheckWithTable(srcexp, tarexp, table)
            if(rettable) return rettable
        }
        
        return false
    }

    checkcv(srcr, tarr, getreplaced = false){
        let [sleft,sright] = [this.cloneExp(srcr.leftexps), this.cloneExp(srcr.rightexps)]
        let [tleft, tright] = [this.cloneExp(tarr.leftexps), this.cloneExp(tarr.rightexps)]
        let con = sleft.concat(sright).concat(tleft).concat(tright)
        let cvtable = {}
        cvtable = this.getcv(cvtable, con)
        let r = sleft.concat(sright)
        let optlist = this.operationlist(r)
        let perm = this.genPermutation(Object.keys(cvtable).length, optlist.length)

        for(let i = 0 ; i < perm.length ; i ++){
            let tcvtable = this.assigncv(cvtable, optlist, perm, i)
            let replacedr = this.replacecv(tcvtable, tarr)
            if(this.Same(this.cloneExp(sleft), this.cloneExp(replacedr.leftexps))||this.Same(this.cloneExp(sright), this.cloneExp(replacedr.leftexps)) &&
                (this.Same(this.cloneExp(sright), this.cloneExp(replacedr.rightexps))||this.Same(this.cloneExp(sleft), this.cloneExp(replacedr.rightexps)))) {

                    if(getreplaced){
                        return tcvtable
                    }
                    return true 
            }
            if(this.OperatorEquivalence(srcr,replacedr) && this.OperandEquivalence(srcr,replacedr)){
                if(getreplaced){
                    return tcvtable
                }
                return true
            }
        }
        return false
    }

    //--Equivalence--
    //isRule checks if rule exist or its commutative form exists in the rule table
    //code variables
    isRule(relation, debug=false){
        if(debug){
            console.log('relation: ', this.RuleToString(relation))
        }
        let left = relation.leftexps
        let right = relation.rightexps
        
        // console.log(left, right)
        let i = 0
        for(const rule of this.allrules){


            let rleft = rule.leftexps
            let rright = rule.rightexps
            if(debug){
                console.log('begincv: ', this.RuleToString(relation))
            }
            
            

            if(this.checkcv(relation, rule)) {
                return true
            }
            if(debug){
                console.log('failed cv')
            }

            //lengths dont match, next rule
            if(left.length != rleft.length && left.length != rright.length) continue
            if(right.length != rright.length && right.length != rleft.length) continue

            //if both statements have the same left and right, then check for operand equivalentce.

            if(this.Same(left, rleft) ) {
                if(this.Same(right, rright)){
                    // found rule
                    return true 
                }
            }
            // try rule commutativity
            if(this.Same(left, rright)) {
                if(this.Same(right, rleft)){
                    return true
                }
            }

            i += 1
        }       
        
        return false 
    }

    operatorlist(src, opt, brflag = true){
        let ret =[]
        for (const e of src){
            if(e.Opparam && brflag){
                if(e.Opparam.length!=0){
                    if(opt && (e.Opparam[0] == '#102' || e.Opparam[0] == '#101')){
                        ret.push('#100')
                        ret.push(e.Opparam[1])
                        ret.push(e.Opparam[2])
                        if(e.Opparam[0] == '#101') {ret.push(e.operator)}
                        else{
                            ret.push(opt)
                        }
                    }else{
                        ret.push(e.Opparam[0])
                        ret.push(e.Opparam[1])
                        ret.push(e.Opparam[2])
                        if(e.operator){
                            ret.push(e.operator)
                        }
                    }
                }
                else{
                    ret.push(e.operator)
                }
            }
            else{
                ret.push(e.operator)
            }
        }
        return ret
    }

    getBrOpt(src){
        for (const e of src){
            if(e.Opparam){
                if(e.operator.length != 0)
                    return e.operator
            }
        }
        return  
    }

    OperatorEquivalence(srcstatement, tarstatement){
        let srctablel = this.operatorlist(srcstatement.leftexps)
        let srctabler = this.operatorlist(srcstatement.rightexps)
        let opt = this.getBrOpt(srcstatement.leftexps)
        if(!opt){
            opt = this.getBrOpt(srcstatement.rightexps)
        }

        //if rule is Blb, then add operator to tartable if operator exists
        //if src has #13, then treat #12 in tar as #13

        let tartablel = this.operatorlist(tarstatement.leftexps, opt)
        let tartabler = this.operatorlist(tarstatement.rightexps, opt)

        if(tartablel.length != srctablel.length && tartablel.length != srctabler.length ) return false
        if(tartabler.length != srctablel.length && tartabler.length != srctabler.length ) return false
        if(!(this.listequal(srctablel,tartablel) && this.listequal(srctabler,tartabler)) && !(this.listequal(srctabler,tartablel) && this.listequal(srctablel,tartabler))) return false
        return true
    }

    
    operandlist(src, operands){
        let ret =[]
        for (const e of src){
            if(e.Opparam){
                if(e.Opparam.length != 0){
                    if(operands && (e.Opparam[0] == '#101' || e.Opparam[0] == '#102')){
                        ret.concat(operands)
                    }
                }
                else if(e.operands){
                    ret.concat(e.operands)
                }
            }
            else if(e.operands){
                ret.concat(e.operands)
            }
        }
        return ret
    }
    getBrOprands(src){
        for (const e of src){
            if(e.Opparam){
                if(e.operator.length != 0)
                    return e.operands
            }
        }
        return  
    }
    
    OperandEquivalence(srcstatement, tarstatement){
        let srctable = this.operandlist(srcstatement.leftexps).concat(this.operandlist(srcstatement.rightexps))

        let operands = this.getBrOprands(srcstatement.leftexps)
        if(!operands){
            operands = this.getBrOprands(srcstatement.rightexps)
        }
        let tartable = this.operandlist(tarstatement.leftexps, operands).concat(this.operandlist(tarstatement.rightexps, operands))

        if(tartable.length != srctable.length) return false 

        let sit = {}
        let srt = []
        let tit = {}
        let trt=[]
        let index = 1
        for(const opr of srctable){
            if(!sit[opr]){
                sit[opr] = index 
                index += 1
            }
            srt.push(sit[opr])
        }
        index = 1
        for(const opr of tartable){
            if(!tit[opr]){
                tit[opr] = index 
                index += 1
            }
            trt.push(tit[opr])
        }


        return this.listequal(srt,trt)
    }

    Same(src,tar){
        if(!tar && !src) return true
        // if(!tar || !src) return false
        // console.log('src: ', src, 'tar: ', tar)

        // let opr_table = {} 
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
                    // console.log(tar[i].operands, src[j].operands)
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
    getmax(exps){
        let max = 0
        let i = 0
        let ret = exps
        while(i < ret.length){
            if(!ret[i].operands){return 0}
            let j = 0
            if(ret[i].operands.length > 0){
                while(j < ret[i].operands.length)
                {
                    let x = parseInt(ret[i].operands[j])
                    if(x > max){
                        max = x
                    }
                    j += 1
                }
            }   
            
            i+=1
        }
        return max
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
    deepClone(arr) {
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