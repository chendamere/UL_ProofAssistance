



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
            // console.log('!!!',this.TrimAndCheck(tempv))
            if(this.TrimAndCheck(tempv)) {
                console.log('TrimAndCheck pass')
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

            let target = this.ExpToString(this.incOperands(tar))
            let tr = '! ' + this.ExpToString(src) + ' @ ' + target
            let parsed_tr = this.genRule(tr)
            ret.push(parsed_tr)
            
            endmaxcounter += 1
        }

        return ret
    }

    TrimAndCheck(r){
        if(this.MatchandCheck(r.leftexps,r.rightexps)) return true
        return false
    }

    firstIsSameBranch(exp1, exp2){
        if(!exp1 || !exp2) return false 
        if(!exp1[0] || !exp2[0]) return false 
        let leftopt = this.getBrOpt(exp1)
        let rightopt = this.getBrOpt(exp2)
        let lopl = this.getBrOprands(exp1)
        let lopr = this.getBrOprands(exp2)
        let br1 = this.getFirstBr(exp1)
        let br2 = this.getFirstBr(exp2)
        if(leftopt != rightopt) return false
        if(!this.listequal(lopl, lopr)) return false 
        if(br1.index != 0 || br2.index != 0) return false 
        return true 
    }

    StepBranch(t1,t2){ 
        if(this.firstIsSameBranch(t1,t2)){
            let t1br = this.getFirstBr(t1)
            let t2br = this.getFirstBr(t2)
            let [top1,bot1] = this.getTopBot(t1, t1br)
            let [top2,bot2] = this.getTopBot(t2, t2br)

            if(this.firstIsSameBranch(top1,top2)){
                [top1, top2] = this.StepBranch(top1, top2)
            }
            if(this.firstIsSameBranch(bot1,bot2)){
                [bot1, bot2] = this.StepBranch(bot1, bot2)
            }
            if(this.ExpsIsRule(top1, top2) && this.ExpsIsRule(bot1,bot2)){
                if(top1.length + top2.length > bot1.length + bot2.length){
                    return [top1,top2]
                }else{
                    return [bot1,bot2]
                }
            }
            let [ttop1, ttop2] = this.TrimBothWays(top1, top2)
            let [tbot1, tbot2] = this.TrimBothWays(bot1, bot2)
            if(this.ExpsIsRule(ttop1, ttop2) && this.ExpsIsRule(tbot1, tbot2)){
                if(ttop1.length + ttop2.length > tbot1.length + tbot2.length){
                    return [ttop1,ttop2]
                }else{
                    return [tbot1,tbot2]
                }
            }
        }
        return [t1,t2]
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


    cloneExp(exp){
        return this.genRule('!,@,'+this.ExpToString(exp)).rightexps
    }
    getAlltrimedback(exp){
        let allexps = []
        let i = 0 
        while(i < exp.length){
            
            
            let subexp = [].concat(exp.slice(0,i+1))
            if(this.isBranch(exp[i])){
                let br = this.getFirstBr(subexp)
                let [top, bot] = this.getTopBot(exp,br)
                let [toplist, botlist] = [[[]].concat(this.getAlltrimedback(top)), [[]].concat(this.getAlltrimedback(bot))] 
                for(const topexp of toplist){
                    for(const botexp of botlist){
                        const subexp2 = this.updateBr(this.cloneExp(subexp), topexp, botexp, br)
                        allexps.push(subexp2)
                    }
                }
                i = br.index + br.top + br.bot
            }else{
                let beg = 
                let p = [subexp, beg, end]
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
            let br = this.getLastBr(exp)
            if(br.index != -1 && i < this.getBranchEnd(exp,br) && i > br.index){
                subexp = this.cloneExp([exp[br.index]].concat(this.cloneExp(subexp)))
                let br2 = this.getLastBr(subexp)
                subexp = this.updateBr(subexp,[],[],br2)
                let [top, bot] = this.getTopBot(exp,br)
                let [toplist, botlist] = [[[]].concat(this.getAlltrimedfront(top)), [[]].concat(this.getAlltrimedfront(bot))] 
                for(const topexp of toplist){
                    for(const botexp of botlist){
                        const subexp2 = this.updateBr(this.cloneExp(subexp), topexp, botexp, br2)
                        allexps.push(subexp2)
                    }
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
        while(i < exp.length){
            if(this.isBranch(exp[i])){
                let br = this.getFirstBr(exp)
                i = br.index+br.top + br.bot
            }
            let trimbacklist = this.getAlltrimedback(exp.slice(i, exp.length))
            allexps = allexps.concat(trimbacklist)
            i += 1
        }
        let j = exp.length -1
        while(j >= 0){
            let br = this.getLastBr(exp)
            if(br.index != -1 && j > br.index && j <this.getBranchEnd(exp, br)){
                j = br.index
            }
            // console.log(exp.slice(0, j+1))
            let trimfrontlist = this.getAlltrimedfront(exp.slice(0, j+1))
            // console.log('!!!', trimfrontlist)
            allexps = allexps.concat(trimfrontlist)
            j  -= 1
        }
        return allexps 
    }
    MatchandCheck(left, right){
        let subexps = this.getAllSubExps(left)
        // console.log(subexps)
        for(const sub of subexps){
            let exp = this.genRule('!,@'+this.ExpToString(sub[0])).rightexps
            let beg = sub[1]
            let end = sub[2]
            for(const r of this.allrules){
                let rl = r.leftexps 
                let rr = r.rightexps 
                if(this.OperandEquivalence(exp, rl)){
                    let check = this.genRule('!'+this.ExpToString(right)+ '@'+ beg.concat(this.ExpToString(rl)).concat(end))
                    if(this.Same(right,check)){
                        return true 
                    }
                }
                if(this.OperandEquivalence(exp, rr)){
                    let check = this.genRule('!'+this.ExpToString(right)+ '@'+ beg.concat(this.ExpToString(rl)).concat(end))
                    if(this.Same(right,check)){
                        return true 
                    }
                }
                
            }
        }
        
    }

    TrimBothWays(left,right){
        let [tbot1, tbot2] = this.Trim1(this.genRule('!'+this.ExpToString(left) + '@'+ this.ExpToString(right)))
        if(!this.ExpsIsRule(tbot1, tbot2)){
            [tbot1, tbot2] = this.Trim2(this.genRule('!'+this.ExpToString(left) + '@'+ this.ExpToString(right)))
        }
        return [tbot1, tbot2]
    }

    Trim1(r) {
        // console.log('TRIM1')
        const t = this.genRule('!'+this.ExpToString(r.leftexps)+'@'+this.ExpToString(r.rightexps))
        let prevlefts = [t.leftexps]
        let r1 = this.TrimFrontOnce(t.leftexps, t.rightexps, true)
        let left = r1[0]
        let right = r1[1]
        if(this.ExpsIsRule(left,right)){
            return [left,right]
        }
        while(left.length < prevlefts[prevlefts.length-1].length){
            let left2 = left 
            let right2 = right
            let prevlefts2 = [left2]

            let r2 = this.TrimBackOnce(left2, right2, true)
            left2 = r2[0] 
            right2 = r2[1]
            if(this.ExpsIsRule(left2,right2)){
                return [left2,right2]
            }
            while(left2.length < prevlefts2[prevlefts2.length-1].length){
                r2 = this.TrimBackOnce(left2, right2, true)
                prevlefts2.push(left2)
                left2 = r2[0]
                right2 = r2[1]
                // console.log('!!!',this.ExpToString(left2), this.ExpToString(right2), this.ExpsIsRule(left2,right2))
                if(this.ExpsIsRule(left2,right2)){
                    return [left2,right2]
                }
            }

            r1 = this.TrimFrontOnce(left, right, true)
            prevlefts.push(left)
            left = r1[0]
            right = r1[1]
            if(this.ExpsIsRule(left,right)){
                return [left,right]
            }
        }
        return [left,right]
    }
    Trim2(r) {
        // console.log('TRIM2')
        const t = this.genRule('!'+this.ExpToString(r.leftexps)+'@'+this.ExpToString(r.rightexps))
        let prevlefts = [t.leftexps]
        let r1 = this.TrimBackOnce(t.leftexps, t.rightexps, true)
        let left = r1[0]
        let right = r1[1]
        if(this.ExpsIsRule(left,right)){
            return [left,right]
        }
        while(left.length < prevlefts[prevlefts.length-1].length){
            let left2 = left 
            let right2 = right
            let prevlefts2 = [left2]
            let r2 = this.TrimFrontOnce(left2, right2, true)
            left2 = r2[0] 
            right2 = r2[1]
            if(this.ExpsIsRule(left2,right2)){
                return [left2,right2]
            }
            while(left2.length < prevlefts2[prevlefts2.length-1].length){
                r2 = this.TrimFrontOnce(left2, right2, true)
                prevlefts2.push(left2)
                left2 = r2[0]
                right2 = r2[1]
                if(this.ExpsIsRule(left2,right2)){
                    return [left2,right2]
                }
            }
            r1 = this.TrimBackOnce(left, right, true )
            prevlefts.push(left)
            left = r1[0]
            right = r1[1]
            if(this.ExpsIsRule(left,right)){
                return [left,right]
            }
        }
        
        return [left,right]
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
    TrimFrontOnce(left,right, trimtillfail){

        if(left.length ==0  || right.length ==0) return [left,right]
        // console.log('step front', this.ExpToString(left), this.ExpToString(right))

        let [pleft, pright] = [left, right]
        let [leftbr, rightbr] = [this.getFirstBr(pleft), this.getFirstBr(pright)]

        if((leftbr.index != 0 && rightbr.index != 0)||
            (leftbr.index == 0 && rightbr.index == 0 && leftbr.top == 0 && leftbr.bot == 0 && rightbr.top == 0 && rightbr.bot == 0) 
        ){
            if(this.Same([pleft[0]], [pright[0]])){
                pleft = pleft.slice(1, pleft.length)
                pright = pright.slice(1, pright.length)
                // console.log('Same', this.ExpToString(pleft),'@', this.ExpToString(pright))
            }
        }
        else{
            let [topl, botl] = this.getTopBot(pleft, leftbr)
            let [topr, botr] = this.getTopBot(pright, rightbr)
            console.log('!!!',this.ExpToString(topl), this.ExpToString(topr), this.ExpsIsRule(topl,topr))
            console.log('!!!',this.ExpToString(botl), this.ExpToString(botr), this.ExpsIsRule(botl,botr))
            //trim the top first, if top expressions form a rule, then don't trim the bot,
            // this is to work in tandem with check branch,
            //check branch checks if top and bot contain rules.
            //if top or bot already forms a rule, then do not trim.
            if(!this.ExpsIsRule(botl, botr) || trimtillfail){
                let retb  = this.TrimFrontOnce(botl,botr)
                botl = retb[0]
                botr = retb[1]
                if(this.ExpsIsRule(botl, botr)  ){

                }
            }

            if(!this.ExpsIsRule(topl, topr) || trimtillfail){
                let rett = this.TrimFrontOnce(topl,topr)
                topl = rett[0]
                topr = rett[1]
            }
            // if(!this.ExpsIsRule(topl, topr)){
            // }
    
            pleft = this.updateBr(pleft,topl, botl,leftbr)
            pright = this.updateBr(pright,topr ,botr, rightbr)
        }
        // console.log('ret front: ', this.ExpToString(pleft), this.ExpToString(pright))
        return [pleft,pright]
    }
    TrimBackOnce(left,right, trimtillfail){
        if(left.length ==0  || right.length ==0) return [left,right]
        // console.log('step back', this.ExpToString(left), this.ExspToString(right))

        let [pleft, pright] = [left, right]
        let [leftbr, rightbr] = [this.getLastBr(pleft), this.getLastBr(pright)]

        // console.log('ret back: ',leftbr, rightbr)
        // console.log(this.getBranchEnd(pleft,leftbr),pleft.length)
        // console.log(this.getBranchEnd(pright,rightbr) , pright.length)


        if((this.getBranchEnd(pleft,leftbr) < pleft.length && this.getBranchEnd(pright,rightbr) < pright.length)
            || (leftbr.index == -1 && rightbr.index == -1)
            || (leftbr.index == pleft.length-1 && rightbr.index == pright.length-1)
        ){
            // console.log('!!!: ', this.ExpToString(pleft), this.ExpToString(pright))

            if(this.Same([pleft[pleft.length-1]],[pright[pright.length-1]])){
                pleft = pleft.slice(0,pleft.length-1)
                pright = pright.slice(0,pright.length-1)
            }
        }else{
            let [topl, botl] = this.getTopBot(pleft, leftbr)
            let [topr, botr] = this.getTopBot(pright, rightbr)
            if(!this.ExpsIsRule(topl, topr) || trimtillfail){
                let ret1  = this.TrimBackOnce(topl,topr)
                topl = ret1[0]
                topr = ret1[1]
            }
            if(!this.ExpsIsRule(botl, botr) || trimtillfail){
                let ret2 = this.TrimBackOnce(botl,botr)
                botl = ret2[0]
                botr = ret2[1]
            }
            
            pleft = this.updateBr(pleft,topl, botl, leftbr)
            pright = this.updateBr(pright,topr, botr, rightbr)
        }
        // console.log('ret back: ', this.ExpToString(pleft), this.ExpToString(pright))
        return [pleft,pright]
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

    //operands of left and right exps are equivalent iff 
    incOperands(exps){
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
                            broffset += parseInt(exp[ti].Opparam[2][1])
                            broffset += parseInt(exp[ti].Opparam[1][1])
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

            if(this.OperatorEquivalence(relation,rule) && this.OperandEquivalence(relation,rule)){
                // console.log('equiv')
                return true
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
            let j = 0
            if(ret[i].operands){
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
    
}

export default ProofAssistant