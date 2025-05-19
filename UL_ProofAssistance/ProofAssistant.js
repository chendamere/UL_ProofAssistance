



//Proof assistance handles checking if certain proof exists in the database
//or if a rule can be generated inductively
//for a proof to satisfy, there need to exist one or more equivalent expression.
//there exist one or more equivalent expression if 

import { debug, error, table } from "console"

class ProofAssistant {
    constructor (allrules, parser, Exps){
        this.allrules = allrules
        this.parser = parser
        this.Exps = Exps
        this.AllOperators =  this.Get_all_operator()
        this.unaryOperators = this.parser.unaryOperators
        this.binaryOperators = this.parser.binaryOperators
        this.BrOperators =  this.parser.branch

        this.rulestack = []
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
                    // console.log('   !',k, this.ExpToString(exp.slice(0,i)))
                    ret.push([exp.slice(0,i), k])
                    sub.push([exp.slice(0,i), k])

                }
            }
            else{                
                i += 1 
                ret.push([exp.slice(0,i), k])
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
            let sub1br = this.getBr(sub1[0])
            if(sub1br.index != -1 && sub1br.br != '#101'){
                for(const sub2 of list){
                    let sub2br = this.getBr(sub2[0])
                    if(sub2br.index != -1 && sub2br.br != '#102'){
                        if(sub2[1]+ sub2br.index > sub1[1] + sub1br.index){
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

    removeExactDuplicates(data) {
        const seen = new Set();

        const serialize = (index, list) =>
            index + '|' + JSON.stringify(list.map(dict =>
                Object.fromEntries(Object.entries(dict).sort())
            ));

        return data.filter(([dictList, index]) => {
            const key = serialize(index, dictList);
            if (seen.has(key)) return false;
            seen.add(key);
            return true;
        });
    }

    MatchandCheck(src, tar,debug =false){
        // this.PrintAllRules()
        let nsrc = src
        if(this.ExpToString(src).includes(' #0 ') && src.length == 1){
            nsrc = []
        }
        let srcsubs = this.getsub(nsrc)
        let srcexps = this.removeExactDuplicates(srcsubs[0].concat(srcsubs[1]))
        let srcexpsnonil = [...srcexps]

        srcexps = this.addEmpty(srcexps)
        srcexps = this.sort_subexp(srcexps)

        
        let cvRules = this.FilterAxioms(this.allrules, this.parser.cv)
        for(const rule of cvRules){
            // if(debug){
            //         console.log('   Proving --> MatchCV    rule: ', this.RuleToString(rule))                    
            // }
            if(this.MatchCv(this.cloneExp(rule.leftexps), this.cloneExp(rule.rightexps), nsrc, tar, [...srcexpsnonil])) 
            {
                if(debug){
                    console.log('   Proving --> MatchCV --> TRUE!    rule: ', this.RuleToString(rule))                    
                }
                return true
            }
        }

        //filter the axioms by having the same difference in length as the statement

        let rulestack = this.rulestack
        
        for(const r of rulestack){
            for(const sub of srcexps){
                
                if(this.CheckFromRules(r, sub, nsrc, tar, debug)){
                    if(debug){
                        console.log('   Proving --> CheckFromRules --> RuleStack --> TRUE!   rule: ', this.RuleToString(r), 'sub: ', this.ExpToString(sub[0]),'ncsrc: ', this.ExpToString(nsrc),)                    
                    } 
                    return true
                }
            }
        }
        let lendiff = Math.abs(nsrc.length - tar.length)
        let lenRules = this.FilterAxioms(this.allrules, lendiff)
        console.log('       CheckFromRules Operations: ',lenRules.length,' * ',srcexps.length, '=', srcexps.length*lenRules.length)
        for(const rule of lenRules){
            //filter sub based on rule
            // let fsub = ([...srcexps]).map( exp => ((exp[0].length == 0 ? 1 : exp[0].length)==rule.leftexps.length || (exp[0].length == 0 ? 1 : exp[0].length) === rule.rightexps.length) ? exp : null).filter(item => item !== null)
            // console.log(fsub, srcexps.length)
            for(const sub of srcexps){
                if(this.CheckFromRules(rule, sub, nsrc, tar, debug)){
                    if(debug){
                        console.log('   Proving --> CheckFromRules --> TRUE!   rule: ', this.RuleToString(rule), 'sub: ', this.ExpToString(sub[0]),'ncsrc: ', this.ExpToString(nsrc),)                    
                    } 
                    this.rulestack.push(rule)

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

    MatchCvHelper(rsrc, rtar, src, tar, sub){
        if(this.hasCV(rsrc)){   
            let all_tables = this.checkcv(sub[0], rsrc)                      
            if(all_tables){
                for(const ttable of all_tables){
                    let table = {...ttable}
                    let repl = this.cloneExp(this.replacecvexp({...table},this.cloneExp(rtar)))
                    if(!this.Same(repl, sub[0])){
                        if(this.Check(repl, sub, src, tar, true)){
                            return true
                        }
                        
                    }
                }
            }
        }
        return false
    }

    MatchCv(rl, rr, src, tar, srcsubs){
        //record sub operands, sub is not be normalized 
        let [trl,trr] = [this.cloneExp(rl), this.cloneExp(rr)]

        if(!this.hasCV(rl) && !this.hasCV(rr)) return false
        for(const srcsub of srcsubs){
            let sub = [this.cloneExp(srcsub[0]), srcsub[1]]
            if(this.MatchCvHelper(trl, trr, src, tar, sub)){   
                return true 
            }
            if(this.MatchCvHelper(trr, trl, src, tar, sub)){   
                return true
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

    //check replaces the new sub with the new sub and check if combining src and repl is the same as tar
    Check(normalized, sub, src, tar, debug = false){
        let allnew = this.getAllCombine(normalized, sub, src)
        if(debug){
            // for(const x of allnew){
            // }
        }
        for(const v of allnew){
            if(this.Same(v, tar)){
                return true
            }
        }
        return false
    }

    //getAllCombine takes care of all different ways of substituing when substittion happens at the end of a branch 
    //expression contains branches
    getAllCombine(normalized, ssub, src){
        let sub = [this.cloneExp(ssub[0]), ssub[1]]
        //get the first br in src, 
        let srcbr = this.getBr(src)
        while(srcbr.index != -1 && sub[1] > srcbr){
            srcbr = this.getBr(src.slice(srcbr.index+1, src.length))
        }
        if(srcbr.prev && srcbr.prev.index != -1){
            srcbr = srcbr.prev
        }
        let all = []
        //go to last br 
        if(srcbr.index != -1){
            let [top, bot] = this.getTopBot(src, srcbr)
            let range = this.getBranchEnd(src, srcbr)
            let end = src.slice(range,src.length)

            if((sub[1] > srcbr.index && sub[1] <= srcbr.index + top.length) || (sub[1] == srcbr.index+top.length+1 && sub[0].length == 0)){
                let ntops = this.getAllCombine(normalized, [sub[0], sub[1]-(srcbr.index+1)], top)
                for(const x of ntops){       
                    let n = this.updateBr(this.cloneExp(src.slice(0, srcbr.index+1)), x, bot, srcbr).concat(end)
                    all.push(n)
                }
            }
            if((sub[1] > srcbr.index + top.length  && sub[1] <= srcbr.index + top.length + bot.length) || (sub[1] == srcbr.index + bot.length + top.length+1 && sub[0].length == 0)){
                let nbots = this.getAllCombine(normalized, [sub[0], sub[1]-(srcbr.index+top.length+1)], bot)
                for(const x of nbots){
                    let n = this.updateBr(this.cloneExp(src.slice(0, srcbr.index+1)), top, x, srcbr).concat(end)
                    all.push(n)
                }                    
            }
        }
        
        let n = this.substitute(normalized, sub, src)
        all.push(n)
        
        return all
    }

    substitute(repl, tsub, src){

        let sub = tsub
        let replbr = this.getBr(repl)
        let srcbr = this.getBr(src)
        let begin = src.slice(0, sub[1])

        let subbrcheck = this.getBr(sub[0])

        //if src has branch
        if(srcbr.index != -1 && subbrcheck.index != -1){
            //if sub has branch
            let range = this.getBranchEnd(src, srcbr)
            let srcbranchexp = src.slice(srcbr.index, range)

            let rest = this.getRest(this.cloneExp(srcbranchexp),sub[0])
            let end = src.slice(range, src.length)
            
            
            let combine
            
            //rest does not have subexpression outside of branch, repl might

            let x 
            if(rest[0] && rest[0].Opparam[0] == '#101' && replbr.index!= -1 && repl[replbr.index] && repl[replbr.index].Opparam[0] == '#102'){
                combine = this.CombineExp(rest,repl)
                x = begin.concat(combine)
            }else{
                combine = this.CombineExp(repl, rest)
                x = begin.concat(combine).concat(end)
            }
            return x 
        }else{
            return begin.concat(repl).concat(src.slice(sub[1]+sub[0].length, src.length))
        }
    }

    CombineExp(ssrc, ttar, getback = false){
        let src = this.cloneExp(ssrc)
        let tar = this.cloneExp(ttar)
        let srcbr = this.getBr(src)
        let tarbr = this.getBr(tar)
        if(srcbr.index != -1 && tarbr.index != -1){
            let [srctop, srcbot] = this.getTopBot(src, srcbr)
            let [tartop, tarbot] = this.getTopBot(tar, tarbr)
            let begin = src.slice(0,srcbr.index+1)
            let tarbegin = tar.slice(0, tarbr.index+1)
            
            if((srcbr.br == '#100' || srcbr.br == '#101') && (tarbr.br == '#101'|| tarbr.br == '#100')){
                let endtrim = src.slice(this.getBranchEnd(src, srcbr), src.length)

                let topcombine = this.CombineExp(srctop, tartop)
                let botcombine = this.CombineExp(srcbot, tarbot)
                let ret = this.updateBr(begin, topcombine, botcombine,srcbr).concat(endtrim)
                // console.log(srcbr.index)

                return ret
            }
            else if((srcbr.br == '#100' || srcbr.br == '#102') && (tarbr.br == '#102' || tarbr.br == '#100')){
                let endtrim = src.slice(this.getBranchEnd(src, srcbr), src.length)
                let topcombine = this.CombineExp(srctop, tartop, true)
                let botcombine = this.CombineExp(srcbot, tarbot, true)
                let ret =  this.updateBr(tarbegin, topcombine, botcombine,tarbr).concat(endtrim)
                if(this.ExpToString(ttar).includes( ', #102 $0 $1 , #11 , ') && this.ExpToString(ssrc).includes(', #102 $0 $0 , #13 1 ,')){
                    console.log('       endtrim: ', this.ExpToString(endtrim), this.getBranchEnd(tar, tarbr), tar.length, this.ExpToString(tar))
                }
                return ret

            }else if(srcbr.br == '#101' && tarbr.br == '#102'){
                // throw new Error('error in CombineExp')
                let endtrim = tar.slice(this.getBranchEnd(tar, tarbr), tar.length)  
                let topcombine = this.CombineExp(srctop, tartop)
                let botcombine = this.CombineExp(srcbot, tarbot)
                let ret = this.updateBr(begin, topcombine, botcombine,srcbr).concat(endtrim)
                ret[srcbr.index].Opparam[0] = '#100'
                // console.log(srcbr.index)

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
                // console.log('@',this.ExpToString(src.concat(tar)))

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
                    ret[subbr2.index].Opparam[0] = '#101'
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
                    subexp = this.cloneExp(cvtable[expsrc[i].operands[0]])

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
                exps = exps.concat(this.cloneExp(subexp))

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

    removeDuplicateDicts(dictList) {
        const seen = new Set();

        const serialize = obj =>
            JSON.stringify(Object.keys(obj).sort().reduce((acc, key) => {
            acc[key] = Array.isArray(obj[key])
                ? obj[key].map(item => JSON.stringify(Object.entries(item).sort()))
                : obj[key];
            return acc;
            }, {}));

        return dictList.filter(dict => {
            const str = serialize(dict);
            if (seen.has(str)) return false;
            seen.add(str);
            return true;
        });
    }

    generateTableCombinations(listofCV, lists, max, len, srclen) {
        const results = [];
        const names = {};
        for (let i = 0; i < listofCV.length; i++) {
            names[parseInt(listofCV[i][0])] = '';
        }
        const keyNames = Object.keys(names)

        const extendedLists = [...lists];

        function findMatchingLists(num, index, list, offset) {
            let fl = list.filter(([charNum,]) => charNum === num)
            for(const f of fl){
                if(index == offset + f[1]) {
                    return fl.length
                }
            }
            return false;
        }

        function helper(index, currentTable, usedIndices, totalLength, offset=0) {
            if (index === keyNames.length) {
                
                
                if (totalLength === max ) {
                    let sum = 0
                    for(const cv of listofCV){
                        if(currentTable[cv[0]]){
                            sum += currentTable[cv[0]].length
                        }
                    }   
                    if(srclen===len+sum){
                        results.push({ ...currentTable });
                    }
                }
                return;
            }

            const key = keyNames[index];

            for (let i = 0; i < extendedLists.length; i++) {
                if (usedIndices.has(i)) continue;

                const list = extendedLists[i][0];

                const newLength = totalLength + list.length;

                if (newLength > max) continue;

                let count = findMatchingLists(key,extendedLists[i][1], [...listofCV], offset)
                // console.log('   ', extendedLists[i][0].length )
                if(!count) continue
                // console.log(offset, key, count, list.length)
                
                

                if(list){
                    currentTable[key] = list;
                }
                else{
                    currentTable[key] = [];
                }
                usedIndices.add(i);

                helper(index + 1, currentTable, usedIndices, newLength, offset + (count*(list.length-(list.length ==0? 0:1))));

                usedIndices.delete(i);
                delete currentTable[key];
            }
        }

        helper(0, {}, new Set(), 0);

        
        return this.removeDuplicateDicts(results);
    }


    genCVTable(allfiltersub, listofCVOpr, len, noncv, srclen){
        let i = len    
        let table_comb = []
        while(i > 0){
            let tables = this.generateTableCombinations([...listofCVOpr], [...allfiltersub], i, noncv, srclen)            
            table_comb = table_comb.concat(tables)
            i -= 1
        }
        return table_comb
    }

    CheckTable(srcsub, tarexp, table){
        let repltar =  this.cloneExp(this.replacecvexp({...table}, this.cloneExp(tarexp)))

        if(this.Same(repltar, srcsub)){
            return true 
        }
        return false
    }

    //high processing time
    CheckAllTables(srcsub, tarexp, table_comb, debug=false){
        let filtered_tables = []
        for(const table of table_comb){
            if(this.CheckTable(srcsub, tarexp, table)){
                filtered_tables.push({...table})
            }
        }
        return filtered_tables
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

    decreaseUntilOneReached(dict) {
        // Convert keys to numbers
        let keys = Object.keys(dict).map(key => parseInt(key));
        
        while (!keys.includes(1)) {
            // Decrease all keys by 1
            keys = keys.map(key => key - 1);
        }
        // Build a new dictionary with updated keys (as strings) and empty string values
        const result = {};
        for (let key of keys) {
            result[String(key)] = [];
        }

        return result;
    }

    getlistofCVOpr(exp){
        let ret = []
        for(let i = 0; i< exp.length; i +=1){
            const opt = exp[i]
            if(opt.operator == this.parser.cv){
                ret.push([opt.operands[0], i])
            }
        }
        return ret
    }

    checkcv(src, tar){
        let tarexp = this.cloneExp(tar)
        let listofCVOpr = this.getlistofCVOpr(tarexp)
        let nonCVlen = this.NonCvOptCount(tarexp)
        let len = src.length - nonCVlen
        let debug = false
        if(len < 0){
            return false
        }

        let allsubsub = this.getsub(src)
        let allfiltersub = this.FilterExpLen(len, this.removeDuplicateDicts(allsubsub[0].concat(allsubsub[1])))
        let filtered_tables = this.genCVTable(allfiltersub, listofCVOpr, len, nonCVlen, src.length)
        // console.log('   filtered_table', filtered_tables.length)
        let all_rettable = this.CheckAllTables(src, tarexp, filtered_tables, debug)
        if(all_rettable.length > 0) return all_rettable

        return false

    }

    Same(src,tar){
        if (!Array.isArray(src) || !Array.isArray(tar)) return false;
        if (src.length !== tar.length) return false;

        const normalize = obj =>
            JSON.stringify(Object.keys(obj).sort().reduce((acc, key) => {
            acc[key] = typeof obj[key] === 'object' && obj[key] !== null
                ? normalize(obj[key])
                : obj[key];
            return acc;
            }, {}));

        for (let i = 0; i < src.length; i++) {
            const a = normalize(src[i]);
            const b = normalize(tar[i]);
            if (a !== b) return false;
        }

        return true;
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