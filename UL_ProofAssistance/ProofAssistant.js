



//Proof assistance handles checking if certain proof exists in the database
//or if a rule can be generated inductively
//for a proof to satisfy, there need to exist one or more equivalent expression.
//there exist one or more equivalent expression if 

class ProofAssistant {
    constructor (allrules, parser, Exps){
        this.allrules = allrules
        this.parser = parser
        this.Exps = Exps
        this.AllOperators =  this.Get_all_operator()
        this.unaryOperators = this.parser.unaryOperators
        this.binaryOperators = this.parser.binaryOperators
        this.BrOperators =  this.parser.branch
        // console.log(this.BrOperators)
        this.AddSpacetoExp()
    }

    matchbr(tempv){
        let retl=tempv.leftexps
        let retr=tempv.rightexps
        let i =0
        while(i < retl.length){
            if(retl[i].Opparam.length != 0 && retr[i].Opparam.length!= 0 ){
                if(retl[i].Opparam[0] != retr[i].Opparam[0]){
                    retr[i].Opparam[0] = retl[i].Opparam[0]
                }
            }
            i += 1
        }
        return retr
    }
    //--Prove--
    Proving(start, end, debug= false) {

        //operands are not binded yet
        if(debug){
            console.log('------Proving-------')
            console.log('start: ', start, 'end: ', end)
        }
        let tempv = this.genRule('!'+start+'@'+end)
        // console.log('r:', this.RuleToString(tempv))
        if (this.Same(tempv.leftexps, tempv.rightexps)) return 1
        if(!this.isRule(tempv)){
            // console.log('!!!',this.MatchandCheck(tempv.leftexps, tempv.rightexps))
            
            // console.log(this.ExpToString(tempv.leftexps),this.ExpToString(tempv.rightexps), this.MatchandCheck(tempv.leftexps, tempv.rightexps))
            if(this.MatchandCheck(tempv.leftexps, tempv.rightexps)) {
                console.log('MatchandCheck pass')
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
    
    //--Trim and Branch--
    //return all different configuration of operands opdering 
    try_match_operand_order(parsed_newrule) {
        let tar = parsed_newrule.rightexps
        let src = parsed_newrule.leftexps
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

    isBranch(opt){
        if(opt.Opparam){
            if(opt.Opparam[0]){
                return true
            }
        }
        return false 
    }


    ///monka! so here is what we are gonna do :
    //to check if a proofstep is satisfiable via the insertion rule production process,
    //we need to achieve 2 things:
    //  1. get all subexpression
    //  2. check whether a subexpression matches any expression in allrules, if so, substitute the expression and check if matches the right side of the proofstep
      
    // ABCDE
    // outer loop:
    // A, AB, ABC,ABCD,ABCDE
    // B, BC, BCD, BCDE
    // C, CD, CDE
    // D, DE
    // E


    CombineExp(leftexp,rightexp){
        let ret = []
        let lbr = this.getFirstBr(leftexp)
        let rbr = this.getFirstBr(rightexp)

        if(lbr.index != -1 && rbr.index != -1 && lbr.br =='#100' && rbr.br =='#101'){
            let [ltop, lbot] = this.getTopBot(leftexp, lbr)
            let [rtop, rbot] = this.getTopBot(rightexp, rbr)

            let combinedtop = this.CombineExp(ltop,rtop)
            let combinedbot = this.CombineExp(lbot,rbot)
            let tempbr = leftexp[lbr.index]
            tempbr.Opparam[0] = '#102'
            ret = leftexp.slice(0, lbr.index).concat([tempbr]).concat(combinedtop).concat(combinedbot)
            ret = this.updateBr(leftexp, combinedtop, combinedbot, lbr)
            ret = ret.concat(rightexp.slice(this.getBranchEnd(rightexp, rbr), rightexp.length))
        }else{
            ret = leftexp.concat(rightexp)
        }
        return ret 
    }

    cloneExp(exp){
        let ret = this.genRule('!,@,'+this.ExpToString(exp)).rightexps
        if(ret[0].operator == '#0') return []
        
        return ret
    }
    getAlltrimedback(exp){
        let allexps = []
        let i = 0 
        while(i < exp.length){
            let subexp = [].concat(exp.slice(0,i+1))
            if(this.isBranch(exp[i]) && exp[i].Opparam[0] != '#101'){
                let br = this.getFirstBr(exp.slice(i,exp.length))
                br.index = i
                let temp = this.cloneExp(subexp)
                temp[i].Opparam[0] = '#100'
                let [top, bot] = this.getTopBot(exp,br)
                let botlist = [[]].concat(this.getAlltrimedback(bot))
                let toplist = [[]].concat(this.getAlltrimedback(top))

                for(const topexp of toplist){
                    for(const botexp of botlist){
                        const subexp2 = this.updateBr(this.cloneExp(temp), topexp, botexp, br)
                        allexps.push(subexp2)
                    }
                }
                if(br.br == '#102'){
                    let brexp = this.updateBr(this.cloneExp(subexp), toplist[toplist.length-1], botlist[botlist.length-1], br)
                    allexps.push(brexp)
                }
                i = this.getBranchEnd(exp, br)
                continue;

            }else{
                allexps.push(subexp)
            }
            i+= 1
        }
        return allexps
    }

    getAlltrimedfront(exp){
        let allexps = []
        let i = exp.length-1 
        while(0 <= i){
            let subexp = [].concat(this.cloneExp(exp).slice(i,exp.length))
            let br = this.getLastBr(exp.slice(0,i))
            if(br.index != -1 && i < this.getBranchEnd(exp,br) && i >= br.index){
                let t = this.cloneExp([exp[br.index]])
                let br2 = this.getFirstBr(t)
                t = this.updateBr(t,[],[],br2)

                t[br2.index].Opparam[0] = '#101'

                let [top, bot] = this.getTopBot(exp,br)
                let [toplist, botlist] = [[[]].concat(this.getAlltrimedfront(top)), [[]].concat(this.getAlltrimedfront(bot))] 
                for(const topexp of toplist){
                    for(const botexp of botlist){
                        let subexp2 = this.updateBr(this.cloneExp(t), topexp, botexp, br2).concat(subexp.slice(1,subexp.length))
                        allexps.push(subexp2)
                    }
                }
                if(br.br == '#102'){
                    t[br2.index].Opparam[0] = '#102'
                    let brexp = this.updateBr(this.cloneExp(t), toplist[toplist.length-1], botlist[botlist.length-1], br2).concat(subexp.slice(1,subexp.length))
                    allexps.push(brexp)
                }
                i = br.index 
            }else{
                allexps.push(subexp)
            }
            i -= 1
        }
        return allexps
    }
    getAllSubExps(exp){
        let allexps = []
        let i = 0 
        allexps.push([[],[], exp])
        while(i < exp.length){
            let beginexp = exp.slice(0, i)            
            let trimbacklist = this.getAlltrimedback(exp.slice(i, exp.length))
            let edgeb = !trimbacklist[trimbacklist.length-1] ? [] : trimbacklist[trimbacklist.length-1]
            trimbacklist = trimbacklist.slice(0,trimbacklist.length-1)

            let trimfrontlist= this.getAlltrimedfront(exp.slice(i, exp.length))
            trimfrontlist = trimfrontlist.slice(0,trimfrontlist.length-1)

            let j = 0
            let ret = []
            while(j < trimbacklist.length) {
                ret.push([beginexp, trimbacklist[j], trimfrontlist[trimbacklist.length - j -1]])
                j += 1
            }
            ret.push([beginexp, edgeb,[]])
            if(this.isBranch(exp[i])){
                let br = this.getFirstBr(exp)
                i = this.getBranchEnd(exp,br)
            }else{
                i += 1
            }
            allexps = allexps.concat(ret)
        }
        allexps.push([exp,[],[]])

        i = exp.length+1
        while(i > 0){
            let br = this.getLastBr(exp)
            if(br.index != -1 && i > br.index && i <= this.getBranchEnd(exp, br)){
                i = br.index
            }else{
                i -= 1
            }
            let endexp = exp.slice(i, exp.length)

            let trimfrontlist = this.getAlltrimedfront(exp.slice(0, i))
            let edgef = !trimfrontlist[trimfrontlist.length-1] ? []: trimfrontlist[trimfrontlist.length-1] 
            trimfrontlist = trimfrontlist.slice(0,trimfrontlist.length-1)

            let trimbacklist = this.getAlltrimedback(exp.slice(0, i))
            trimbacklist = trimbacklist.slice(0,trimbacklist.length-1)

            let ret = []
            let j = 0
            while(j < trimbacklist.length) {
                ret.push([trimbacklist[trimbacklist.length - j -1], trimfrontlist[j], endexp])
                j += 1
            }
            ret.push([[], edgef,endexp])
            allexps = allexps.concat(ret)
        }
        return allexps 
    }

    MatchandCheck(left, right){
        // console.log(this.ExpToString(left))
        // console.log(this.ExpToString(right))
        let subexps = this.getAllSubExps(left)
        // for(const a of subexps){
        //     console.log('leftlist: ', this.ExpToString(a[1]))
        // }


        // console.log('leftlist: ', subexps)
        
        for(const p of subexps){
            let begin = this.cloneExp(p[0])
            let sub = this.cloneExp(p[1])
            let end = this.cloneExp(p[2])
            for(const r of this.getAllRules()){
                // console.log(this.RuleToString(r))
                
                let rl = this.cloneExp(r.leftexps)
                let rr = this.cloneExp(r.rightexps) 
                // console.log(this.RuleToString(r))

                let rlrule = this.genRule('!'+this.ExpToString(rl)+'@'+this.ExpToString(sub))
                // if(rlrule.leftexps[0].operator == '#4' && rlrule.rightexps[0].operator == '#4'){
                //     console.log('!', this.RuleToString(rlrule))
                // }
                // console.log('rlrule: ',this.RuleToString(rlrule))

                let normalizedrl = this.Operands_normalize(rlrule)

                if(this.Same(normalizedrl.leftexps, normalizedrl.rightexps)){

                    let temprr = rr 
                    let checkCombined = this.CombineExp(this.CombineExp(begin, temprr),end)    
                    // if(rl.length == 1 && sub.length == 1) {
                    //     // console.log('!!', this.ExpToString(begin),this.ExpToString(temprr),this.ExpToString(end))
                    //     // console.log('!', this.RuleToString(normalizedrl))
                    // }                
                    let limit = this.getmax(checkCombined)
                    let i = 0
                    do{
                        // console.log('combined1:', this.ExpToString(checkCombined), limit)
                        if(this.Same(checkCombined,right)){
                            return true 
                        }
                        temprr = this.incOperands(temprr)
                        i += 1
                    }while(i <= limit)
                }

                let rrrule = this.genRule('!'+this.ExpToString(rr)+'@'+this.ExpToString(sub))
                // if(rrrule.leftexps[0].operator == '#4' && rrrule.rightexps[0].operator == '#4'){
                //     console.log('!', this.RuleToString(rrrule))
                // }

                let normalizedrr = this.Operands_normalize(rrrule)
                if(this.Same(normalizedrr.leftexps, normalizedrr.rightexps)){
                    let temprl = rl 
                    let checkCombined = this.CombineExp(this.CombineExp(begin, temprl),end)
                    let limit = this.getmax(checkCombined)
                    let i = 0 
                    do{
                        // console.log('rule: ', this.RuleToString(r), limit)
                        // console.log('combined2:', this.ExpToString(checkCombined))
                        if(this.Same(checkCombined,right)){
                            return true 
                        }
                        temprl = this.incOperands(temprl)
                        i += 1
                    }while(i <= limit)
                }
            }
        }
        return false 
        
    }

    ExpsIsRule(left,right){
        let t = this.genRule(this.ExpToString(left)+'@'+this.ExpToString(right))
        if(this.isRule(t)){
            return true
        }

        let normt = this.Operands_normalize(t)
        if(this.isRule(normt)){
            return true
        }
        
        return false
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
        let end = br.index +1
        while(i < end){
            if(exp[i]){
                if(exp[i].Opparam){
                    if(exp[i].Opparam[0]){
                        end += parseInt(exp[i].Opparam[1][1]) + parseInt(exp[i].Opparam[2][1])
                    }
                }
            }
            // console.log(exp)
            i+= 1
        }
        return end
    }

    getTopBot(exp, br){
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
        let exp = texp.slice(0,texp.length)
        if(br.index == -1) return exp
        exp[br.index].Opparam[1] = '$'+ this.getNumOpt(topexp)
        exp[br.index].Opparam[2] = '$'+ this.getNumOpt(botexp)
        let [top, bot] = this.getTopBot(exp, br)
        let range = top.length + bot.length
        let end = exp.slice(br.index + range + 1, exp.length)
        exp = exp.slice(0, br.index+1).concat(topexp).concat(botexp).concat(end)
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
    //operands of left and right exps are equivalent iff 
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
        let ti = 0
        // console.log('leftbr: ', br)
        while(ti < exp.length) {
            if(exp[ti].Opparam){
                if(exp[ti].Opparam[0]){
                    if(this.BrOperators.includes(exp[ti].Opparam[0])){
                        return {index : ti, next : {}, prev:br, top: parseInt(exp[ti].Opparam[1][1]), bot:parseInt(exp[ti].Opparam[2][1]), br: exp[ti].Opparam[0]}
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
        // console.log('leftbr: ', br)
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

    inTopBranch(br, i, offset)
    {
        let reti = i - offset
        return (br.index > -1) 
        && (reti >= br.index)
        && (reti <= br.index + br.top)
        && (br.top != 0)
    }
    inBotBranch(br, i )
    {
        return (br.index > -1) 
        && (i >= br.index + br.top)
        && (i <= br.index + br.top+br.bot)
        && (br.bot != 0)
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
                            if(temp_table[operand] == undefined){
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
            if(srcropt.Opparam){
                if(srcropt.Opparam.length == 0 ){
                    if(this.parser.cv == srcropt.operator){
                        // console.log(this.parser.cv)
                        cvtable[srcropt.operands[0]] = ''
                        
                    }
                }
            }
            i += 1
        }
        // console.log(cvtable)
        return cvtable
    }
    assigncv(cvtable, optlist, perm){
        let tcvtable = {...cvtable}
        for(const p of perm){
            if(tcvtable[p[0] + 1] == ''){
                let v =''
                // console.log(optlist, p)
                for(const c of optlist[p[1]]){
                    v += c + ' '
                    
                }

                tcvtable[(p[0] + 1).toString()] = v.trim()
            }
        }
        return tcvtable
    }
    replacecv(cvtable, rule){
        let retr = this.genRule('!'+this.ExpToString(rule.leftexps) + '@' + this.ExpToString(rule.rightexps))
        for(const exp of retr.leftexps){
            if(exp.operator == this.parser.cv){
                let t = cvtable[exp.operands[0]].split(' ')
                exp.operator = t[0]
                exp.operands = t.slice(1,t.length)
            }
        }
        for(const exp of retr.rightexps){
            if(exp.operator == this.parser.cv){
                let t = cvtable[exp.operands[0]].split(' ')
                exp.operator = t[0]
                exp.operands = t.slice(1,t.length)
            }
        }
        return retr 
    }
    checkcv(srcr, tarr){
        let sleft = srcr.leftexps
        let sright = srcr.rightexps
        let tleft = tarr.leftexps 
        let tright = tarr.rightexps 
        let con = sleft.concat(sright).concat(tleft).concat(tright)
        let cvtable = {}
        cvtable = this.getcv(cvtable, con)

        let r = sleft.concat(sright)
        let optlist = this.operationlist(r)

        let perm = this.genPermutation(Object.keys(cvtable).length, optlist.length)

        for(let i = 0 ; i < perm.length ; i ++){
            let tcvtable = this.assigncv(cvtable, optlist, perm, i)

            let replacedr = this.replacecv(tcvtable, tarr)
            
            if(this.Same(sleft, replacedr.leftexps) ) {
                if(this.Same(sright, replacedr.rightexps)){
                    return true 
                }
            }
            if(this.Same(sright, replacedr.leftexps) ) {
                if(this.Same(sleft, replacedr.rightexps)){
                    return true 
                }
            }
            if(this.OperatorEquivalence(srcr,replacedr) && this.OperandEquivalence(srcr,replacedr)){
                return true
            }
        }

        return false
        //

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


            //tocheck if a rule that contains branch exoressions on either side is a rule, we need to check if source is a big branch
            //if source is a big branch, then target can either be small right branch or small left branch
            //maybe this process requires post cv conversion, so instead return true/false in checkcv(), we convert it first, check for branch, then check as usual.

            //if src contains big bracket, then all target rule that contains small left bracket or small right bracket will be condidate

            // 
            //lengths dont match, next rule
            if(left.length != rleft.length && left.length != rright.length) continue
            if(right.length != rright.length && right.length != rleft.length) continue

            //if both statements have the same left and right, then check for operand equivalentce.

            if(this.Same(left, rleft) ) {
                if(this.Same(right, rright)){
                    // found rule
                    // console.log('1 ', left, rleft)

                    return true 
                }
            }
            // try rule commutativity
            // console.log('com:', this.ExpToString(left), this.ExpToString(rright), this.Same(left, rright))
            if(this.Same(left, rright)) {
                if(this.Same(right, rleft)){
                    // console.log('2 ', left, rleft)

                    return true
                }
            }

            // if(this.OperatorEquivalence(relation,rule) && this.OperandEquivalence(relation,rule)){
            //     console.log('equiv')
            //     return true
            // }

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
        if(!tar || !src) return false
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
                    if(src[i].operator != tar[i].operator) {
                        return false }
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

    Gen_sim(exp){
        let ret = ''
        // console.log(this.AllOperators)
        let op = ''
        let i = 0 
        let found = false
        let line = ''
        while(i < exp.length) {
            let c = exp[i]
            if(c == ' ' || c == ',' || c =='$' || c =='&') {
                found = false
                //binary
                for(const bin of this.binaryOperators){

                    if(bin == op){
                        for(const bin2 of this.binaryOperators){
                            let p = exp.replaceAll(op + ' ', bin2 + ' ')

                            line += p
                        }
                        op = ''

                    }
                }

                //unary
                for(const unary of this.unaryOperators){

                    if(unary == op){
                        for(const unary2 of this.unaryOperators){
                            let p = exp.replaceAll(op + ' ', unary2 + ' ')
                            ret.push(p)
                        }
                        op = ''

                    }
                }
                for(const brop of this.BrOperators){

                    if(brop == op){
                        for(const brop2 of this.BrOperators){
                            let p = exp.replaceAll(op + ' ', brop2 + ' ')

                            ret.push(p)
                        }
                        op = ''

                    }
                }
            }
            if(c == '#') {
                found = true
                
            }
            if(found) {
                op += c
            }
            i += 1
            
        }
        let s = new Set(ret)
        let sl = Array.from(s)
        if(sl.length == 0 ) return [exp]
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
        let i = 0
        let ret = exps
        let max = 0
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
            // console.log(rule)
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
        // console.log(exps)
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