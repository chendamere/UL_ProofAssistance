



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
                // this.PrintAllRules()
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

        if(lbr.index != -1 && rbr.index != -1){
            let [ltop, lbot] = this.getTopBot(leftexp, lbr)
            let [rtop, rbot] = this.getTopBot(rightexp, rbr)
            let combinedtop = this.CombineExp(ltop,rtop)
            let combinedbot = this.CombineExp(lbot,rbot)
            let tempbr = leftexp[lbr.index]
            if(lbr.br =='#101' && rbr.br =='#102'){
                
                tempbr.Opparam[0] = '#100'

            }else if(lbr.br == rbr.br){
                if(lbr.br == '#101'){
                    tempbr.Opparam[0] = '#101'                    
                }else if(lbr.br == '#102'){
                    tempbr.Opparam[0] = '#102'                    
                }else if(lbr.br == '#100'){
                    tempbr.Opparam[0] = '#100'                    
                }
            }
            ret = leftexp.slice(0, lbr.index).concat([tempbr]).concat(combinedtop).concat(combinedbot)
            ret = this.updateBr(leftexp, combinedtop, combinedbot, lbr)
            ret = ret.concat(rightexp.slice(this.getBranchEnd(rightexp, rbr), rightexp.length))
        }
        else{
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
            let begin = this.cloneExp(exp.slice(0,i+1))
            let br = this.getFirstBr(exp)
            let temp = this.cloneExp(exp.slice(i,exp.length))
            if(br.index != -1 && i == br.index){
                temp = this.cloneExp(exp.slice(i,this.getBranchEnd(exp, br)))
                let br2 = this.getFirstBr(temp)

                if(br2.br == '#100'){
                    temp[br2.index].Opparam[0] = '#101'
                }

                let [top, bot] = this.getTopBot(temp,br2)

                let botlist = [[]].concat(this.getAlltrimedback(bot))
                let toplist = [[]].concat(this.getAlltrimedback(top))

                for(const topexp of toplist){
                    for(const botexp of botlist){
                        const subexp2 = begin.slice(0, begin.length-1).concat(this.updateBr(this.cloneExp(temp), topexp, botexp, br2))

                        allexps.push(subexp2)
                    }
                }
                if(br.br == '#100'){
                    temp[br2.index].Opparam[0] = '#100'
                    temp[br2.index].operator = exp[br2.index].operator
                    temp[br2.index].operands = exp[br2.index].operands
                    let brexp = begin.slice(0, begin.length-1).concat(this.updateBr(this.cloneExp(temp), toplist[toplist.length-1], botlist[botlist.length-1], br2))
                    allexps.push(brexp)
                }else{
                    allexps.push(this.cloneExp(exp.slice(0 ,this.getBranchEnd(exp, br))))
                }
                i = this.getBranchEnd(exp, br)

            }else{
                allexps.push(begin)
                i+= 1
            }
        }
        return allexps
    }

    getAlltrimedfront(exp){
        let allexps = []
        let i = exp.length-1
        while(0 <= i){
            let subexp = this.cloneExp(exp.slice(i,exp.length))
            let br = this.getLastBr(exp)
            if(br.index != -1 && i < this.getBranchEnd(exp,br) && i >= br.index){
                let temp = this.cloneExp([exp[br.index]])
                let br2 = this.getFirstBr(temp)
                temp = this.updateBr(temp,[],[],br2)

                if(br.br != '#101'){
                    temp[br2.index].Opparam[0] = '#102'
                    temp[br2.index].operator = ''
                    temp[br2.index].operands = []
                }else{
                    temp[br2.index].Opparam[0] = '#101'
                }

                let [top, bot] = this.getTopBot(exp,br)
                let [toplist, botlist] = [[[]].concat(this.getAlltrimedfront(top)), [[]].concat(this.getAlltrimedfront(bot))] 
                for(const topexp of toplist){
                    for(const botexp of botlist){
                        let subexp2 = this.updateBr(this.cloneExp(temp), topexp, botexp, br2).concat(subexp.slice(1,subexp.length))
                        allexps.push(subexp2)
                    }
                }
                if(br.br == '#100'){
                    temp[br2.index].Opparam[0] = '#100'
                    temp[br2.index].operator = exp[br.index].operator
                    temp[br2.index].operands = exp[br.index].operands
                    let brexp = this.updateBr(this.cloneExp(temp), toplist[toplist.length-1], botlist[botlist.length-1], br2).concat(subexp.slice(1,subexp.length))
                    allexps.push(brexp)
                }else{
                    allexps.push(this.cloneExp(exp).slice(br.index,exp.length))
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
            let trimbacklist = [[]].concat(this.getAlltrimedback(exp.slice(i, exp.length)))
            let trimfrontlist= [[]].concat(this.getAlltrimedfront(exp.slice(i, exp.length)))

            let j = 0
            let ret = []
            while(j < trimbacklist.length) {
                ret.push([beginexp, trimbacklist[j], trimfrontlist[trimbacklist.length - j -1]])
                j += 1
            }

            if(this.isBranch(exp[i])){
                let br = this.getFirstBr(exp)
                i = this.getBranchEnd(exp,br)
            }else{
                i += 1
            }
            allexps = allexps.concat(ret)
        }
        allexps.push([exp,[],[]])

        i = exp.length
        while(i >= 0){
            let br = this.getLastBr(exp)

            let endexp = exp.slice(i, exp.length)

            let trimfrontlist = [[]].concat(this.getAlltrimedfront(exp.slice(0, i)))

            let trimbacklist = [[]].concat(this.getAlltrimedback(exp.slice(0, i)))

            let ret = []
            let j = 0
            while(j < trimbacklist.length) {
                ret.push([trimbacklist[trimbacklist.length - j -1], trimfrontlist[j], endexp])
                j += 1
            }
            if(br.index != -1 && i > br.index && i <= this.getBranchEnd(exp, br)){
                i = br.index-1
            }else{
                i -= 1
            }
            allexps = allexps.concat(ret)
        }
        return allexps 
    }

    

    getStepsFromMin(exps){
        let i = this.getmax(exps)
        for(const exp of exps){
            if(exp.operands){
                for(const opr of exp.operands){
                    if(opr){
                        // console.log('here', parseInt(opr[0]))

                        if(parseInt(opr[0]) < i){
                            i = parseInt(opr[0])
                        }
                    }
                }
            }
        }
        return i
    }
    checkCombine(tar, begin, repl, end){
        let trepl = this.cloneExp(repl)
        let limit = this.getmax(tar)
        let j = 0
        let combinedexp = this.cloneExp(this.CombineExp(this.CombineExp(begin, trepl),end))
        if(this.Same(combinedexp,tar)){
            return true 
        }
        while(j < limit){
            if(this.Same(combinedexp,tar)){
                return true 
            }
            // if(this.ExpToString(repl).includes('#3') && this.ExpToString(repl).includes('#4')){
            //     console.log('combine: ', this.ExpToString(combinedexp))
            // }
            let br = this.getLastBr(begin)
            if(br.index != -1 && this.getBranchEnd(begin, br) >= begin.length){
                
                combinedexp = this.cloneExp(this.CombineExp(this.CombineExp(begin, trepl),end))
                combinedexp[br.index].Opparam[1] = '$' + trepl.length.toString()
                if(this.Same(combinedexp,tar)){
                    return true 
                }
                combinedexp = this.cloneExp(this.CombineExp(this.CombineExp(begin, trepl),end))
                combinedexp[br.index].Opparam[2] = '$' + trepl.length.toString()
                if(this.Same(combinedexp,tar)){
                    return true 
                }
            }
            // console.log('trepl: ', this.ExpToString(trepl))
        
            trepl = this.cloneExp(this.incOperands(trepl))
            combinedexp = this.cloneExp(this.CombineExp(this.CombineExp(begin, trepl),end))
            j += 1
        }
        // console.log('combined: ', this.ExpToString(combinedexp))
        

            

        return false 
    }

    ruleInBranch(rl, rr, sub){
        // let rule = this.genRule('!' + this.ExpToString(rl) + '@' + this.ExpToString(rr))
        let s = this.cloneExp(sub)        
        let ret = []
        let br = this.getFirstBr(s)
        if(br.index != -1 && br.index == 0){
            let [top,bot] = this.getTopBot(sub, br)
            let trule = this.ruleInBranch(rl, rr, top)
            let brule = this.ruleInBranch(rl, rr, bot)
            let s2 = this.cloneExp([s[br.index]])
            let br2 = this.getFirstBr(s2)
            if(trule.length != 0){
                ret = ret.concat(this.updateBr(s2 , trule, brule ,br2))
            }
            else if (brule.length != 0){
                ret = ret.concat(this.updateBr(s2 , trule, brule ,br2))
            }
        }
        let rulel = this.genRule('!' + this.ExpToString(rl) + '@' + this.ExpToString(rl))
        let ruler = this.genRule('!' + this.ExpToString(rr) + '@' + this.ExpToString(rr))
        let srcc = this.genRule('!' + this.ExpToString(s) + '@' + this.ExpToString(s))
        // console.log(this.checkcv(x, x2), this.RuleToString(x), this.RuleToString(x2))
        let check = this.genRule('!'+this.ExpToString(rl)+'@'+this.ExpToString(s))
        if(this.Same(check.leftexps, check.rightexps)){
            // console.log('check: ', this.RuleToString(check))
            return this.cloneExp(rr)
        }
        if(this.hasCV(rr) && this.checkcv(srcc, rulel)){
            // console.log('check: ', this.RuleToString(check))
            let cvtable = this.checkcv(srcc, ruler, true)
            // console.log(cvtable, ruler)
            let subrule = this.replacecv(cvtable, rr)
            // console.log(this.RuleToString(subrule))
            return this.cloneExp(subrule.rightexps)

            // return this.checkcv(srcc, rule, true)
        }
        return ret
    }
    hasCV(exps){
        for(const a of exps){
            if(this.parser.cv.includes(a.operator)) return true
        }
        return false
    }

    getOperandSub(exp1, exp2){
        let table = {}
        let i = 0
        if(exp1.length != exp2.length) return table
        let check = this.Operands_normalize(this.genRule('!'+this.ExpToString(exp1)+ '@' + this.ExpToString(exp2)))
        console.log('check: ', this.RuleToString(check))
        if(!this.Same(check.leftexps,check.rightexps)) return table
        while(i < exp1.length){
            let j = 0
            if(exp1[i].operands){
                while( j < exp1[i].operands.length){
                    if(!check[exp1[i].operands[j][0]]){
                        table[exp1[i].operands[j][0]] = exp2[i].operands[j][0]
                    }
                    j+=1
                }
            }
            i+=1
        }
    }
    flipKeyandValue(table){
        let rettable = {}
        for(const [key, value] of Object.entries(table)){
            rettable[value] = parseInt(key)
        }
        return rettable 
    }

    MatchRule(rl, rr, begin, sub, end, tar){
        // let r1 = this.Operands_normalize(this.genRule('!'+this.ExpToString(rl)+'@'+this.ExpToString(rr)))

        let oprtable = {}
        let tsub = this.Operands_normalize_exps(this.cloneExp(sub),oprtable)[0]
        oprtable = this.flipKeyandValue(oprtable)

        let r = this.Operands_normalize(this.genRule('!'+this.ExpToString(rl)+'@'+this.ExpToString(rr)))
        let trl = r.leftexps
        let trr = r.rightexps

        let rrl = this.genRule('!'+this.ExpToString(trl) + '@' + this.ExpToString(trl))
        let rrr = this.genRule('!'+this.ExpToString(trr) + '@' + this.ExpToString(trr))
        let rtsub = this.genRule('!'+this.ExpToString(tsub) + '@' + this.ExpToString(tsub))        
        if(this.hasCV(trl) || this.hasCV(trr)){
            if(this.checkcv(rtsub,rrl)){                        
                let cvtable = this.checkcv(rtsub, rrl, true)
                trr = this.replacecv(cvtable,rrr).rightexps
                trl = this.replacecv(cvtable,rrl).leftexps
            }
            else if(this.checkcv(rtsub,rrr)){
                let cvtable = this.checkcv(rtsub, rrr, true)
                trr = this.replacecv(cvtable,rrr).rightexps
                trl = this.replacecv(cvtable,rrl).leftexps
            }
        }

        if(this.ExpToString(rl).includes('#11')&&this.ExpToString(rl).includes('#13')&&this.ExpToString(tsub).includes('#11')){
            console.log('tsub', this.ExpToString(tsub))
            console.log('rl', this.ExpToString(rl),'rr', this.ExpToString(rr))
        }

        if(this.Same(trl, tsub)){
            let ttrr = trr
            ttrr = this.Operands_normalize_exps(trr, oprtable)[0]
            if(this.checkCombine(tar, begin, ttrr, end)){
                return true 
            }
        }

        if(this.Same(trr, tsub)){
            let ttrl = trl
            ttrl = this.Operands_normalize_exps(trl, oprtable)[0]
            if(this.checkCombine(tar, begin, ttrl, end)){
                return true 
            }
        }

        let lbexp = this.cloneExp(this.ruleInBranch(trl, trr, tsub))
        let rbexp = this.cloneExp(this.ruleInBranch(trr, trl, tsub))

        if(lbexp.length != 0 && this.checkCombine(tar, begin, lbexp, end)){
            return true 
        }
        if(rbexp.length != 0 &&this.checkCombine(tar, begin, rbexp, end)){
            return true 
        }
        return false 
    }
    MatchandCheck(left, right){

        let subexps = this.getAllSubExps(left)
        
        for(const p of subexps){
            let begin = this.cloneExp(p[0])
            let sub = this.cloneExp(p[1])
            let end = this.cloneExp(p[2])
            for(const r of this.getAllRules()){
                let [rl, rr] = [this.cloneExp(r.leftexps), this.cloneExp(r.rightexps)]
                let com1 = this.MatchRule(rl, rr, begin, sub, end, right)
                if(com1) return true 
                let com2 = this.MatchRule(rr, rl, begin, sub, end, right)
                if(com2) return true
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
        let end = br.index + 1
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
        // if(exp.length == 0) return br

        let ti = 0
        // console.log('leftbr: ', br)
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
        // console.log(operands_table)
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
                        // console.log('!', ret_exp)
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
                    // console.log('replacedr.leftexps: ', this.ExpToString(replacedr.leftexps),'replacedr.rightexps: ', this.ExpToString(replacedr.rightexps))
                    // console.log('sleft: ', this.ExpToString(sleft),'sright: ', this.ExpToString(sright))
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