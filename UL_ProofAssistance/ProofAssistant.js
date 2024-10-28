



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
        if (this.Same(tempv.leftexps , tempv.rightexps)) return 1
        let tempv2 = this.genRule('!'+start+'@'+end)
        if(!this.isRule(tempv)){
            let rules = this.trim_and_check(tempv)      
            
            let check = -1
            let i =0
            while(i < rules.length){
                if(rules[i] != -1)
                {
                    check =rules[i]
                    // console.log(this.RuleToString(check))
                }
                i+=1
            }
            if (check != -1){
                let retr = this.matchbr(tempv)
                if(debug){
                    console.log('found proof, next exp: ', retr)
                }
                return 1
            }

            let f = this.switchtopbot(tempv2.rightexps)
            if(!this.Same(f, tempv.rightexps)){
                if(this.Same(tempv.leftexps, f)){
                    return 1
                }
                let fliprules = this.trim_and_check(this.genRule('!'+this.ExpToString(tempv.leftexps)+'@'+this.ExpToString(f) ))
                i=0
                while(i < fliprules.length){
                    if(fliprules[i] != -1) check =fliprules[i]
                    i+=1
                }
                if (check != -1){
                    return 1
                }
            }
        }
        else{
            if(debug){
                console.log('isrule!: ', this.RuleToString(tempv))
        
            }
            return 1
        }
        return -1
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
    switchtopbot(exp){
        let br
        let ret=[]
        let ti =0
        
        let tempexp = (this.genRule('!,@'+this.ExpToString(exp))).rightexps
        while(ti< exp.length){
            let e = exp[ti]
            let tempe = tempexp[ti]
            if(e){
                if(e.Opparam){
                    if(e.Opparam[0]){
                        if(this.BrOperators.includes(e.Opparam[0])){
                            
            
                            br = e.Opparam
                            let topi = parseInt(br[1][1])
                            let boti = parseInt(br[2][1])
                            e.Opparam[1] = tempe.Opparam[2]
                            e.Opparam[2] = tempe.Opparam[1]
                            ret.push(e)
            
                            // console.log('topi: ', topi)
                            let tii = boti == 0 ? exp.length : ti + topi +1
                            while(tii<= ti+topi+boti && tii < exp.length){
                                e = tempexp[tii]
                                ret.push(e)
                                tii +=1
                            }
                            tii = topi == 0 ? exp.length : ti + 1
                            while(tii <= ti+topi&& tii < exp.length){
                                e = tempexp[tii]
                                ret.push(e)
                                tii +=1
                            }
                            ti = ti + topi + boti+1
                            continue 
                        }
                    }
                }
                ret.push(e)

            }
            ti +=1
        }
        // console.log(ret)
    
        return ret
    }

    getBrandindex(exp){
        let i = 0
        for(const e of exp){
            if(e.Opparam){
                if(e.Opparam[0]){
                    return [e,i]
                }
            }
            else{
                i+= 1
            }
        }
    }

    trim_and_check(parsed_newrule) {

        const t = this.genRule('!'+this.ExpToString(parsed_newrule.leftexps)+'@'+this.ExpToString(parsed_newrule.rightexps))

        let [long, short] = this.Trim(t.leftexps, t.rightexps)

        let trimrule = '! ' + this.ExpToString(short) + ' @ ' + this.ExpToString(long)
        let parsed_trimrule = this.genRule(trimrule)
        if(!this.isRule(parsed_trimrule)){
            parsed_trimrule = this.Operands_normalize(parsed_trimrule)
        }
        
        //dont pass the original rule, pass copies of the expression
        let ret =[]
        
        if(this.isRule(parsed_trimrule)){
                ret.push(parsed_trimrule)
                return ret
        }
        
        //trim branch trim top and bot of both expressions, does not include branch
        console.log('before trimbr: ', this.RuleToString(parsed_trimrule))

        let trimbr = this.TrimBranch(parsed_trimrule)
        console.log('after trimbr: ', this.RuleToString(trimbr))
        if(this.isRule(trimbr)){

            ret.push(trimbr)
            return ret
        }
        console.log('before TrimBranchFront: ', this.RuleToString(trimbr))

        let trimbrf = this.TrimBranchFront(trimbr)
        console.log('after TrimBranchFront: ', this.RuleToString(trimbrf))

        if(this.isRule(trimbrf)){
            ret.push(trimbrf)
            return ret
        }
        if(ret.length == 0)ret.push(-1)
        // console.log('empty')
        return ret
    }

    Trimfront(left, right, flag = true){
        let li = 0
        let brl = this.getlastbr(left)
        let lend = brl.index == -1 ? left.length: brl.index
        let brr = this.getlastbr(right)
        let rend = brr.index == -1 ? right.length: brr.index
        while(li < lend && li < rend){
            if(this.Same([left[li]], [right[li]])){
                let rule = this.genRule('!' + this.ExpToString(left.slice(li, left.length))+'@'+this.ExpToString(right.slice(li, right.length)))
                if(this.isRule(rule) && flag){
                    break
                }
                li += 1                
            }
            else{
                break
            }
        }
        return [left.slice(li, left.length), right.slice(li, right.length)] 
    }

    Trimback(left, right){
        let [long, short] = [left.length < right.length ? right : left, left.length < right.length ? left:right]
        let li = left.length < right.length ? right.length-1 : left.length-1 
        let lj = left.length < right.length ? left.length-1 : right.length-1
        let brl = this.getlastbr(long)
        let brs = this.getlastbr(short)
        let lend = brl.index == -1 ? -1 : brl.index + brl.top + brl.bot
        let send = brs.index == -1 ? -1 : brs.index + brs.top + brs.bot

        while(li >= 0 && li > lend && lj > send){
            if(this.Same([long[li]], [short[lj]])){
                let rule = this.genRule('!' + this.ExpToString(long.slice(0, li+1))+'@'+this.ExpToString(short.slice(0, lj+1)))
                if(this.isRule(rule)){
                    break
                }
                li -= 1
                lj -= 1                
            
            }
            else{
                break
            }
        }
        return [long.slice(0, li+1), short.slice(0, lj+1)]
    }

    Trim(left, right){

        let [ftl, ftr] = this.Trimfront(left,right) 
        // console.log('ftl: ', this.ExpToString(ftl), 'ftr: ', this.ExpToString(ftr))
        let [etl, ets] = this.Trimback(ftl,ftr) 
        return [etl, ets]
    }
    TrimBranchFront(pr){
        let [pleft, pright] = [pr.leftexps, pr.rightexps]
        let [leftbr, rightbr] = [this.getlastbr(pleft), this.getlastbr(pright)]
        if (leftbr.index == -1 || rightbr.index == -1) return pr

        if(leftbr.br && rightbr.br){
            let topr= pright.slice( (rightbr.top == 0 ? rightbr.index+rightbr.top +1: rightbr.index+1) , rightbr.index+rightbr.top+1)    
            let botr= pright.slice((rightbr.bot == 0? rightbr.index+1+rightbr.top+rightbr.bot: rightbr.index+rightbr.top+1) , rightbr.index+rightbr.top+rightbr.bot+1)

            let topl= pleft.slice( (leftbr.top == 0 ? leftbr.index+leftbr.top +1: leftbr.index+1) , leftbr.index+leftbr.top+1)
            let botl= pleft.slice((leftbr.bot == 0 ? leftbr.index+1+leftbr.top+leftbr.bot: leftbr.index+leftbr.top+1) , leftbr.index+leftbr.top+leftbr.bot+1)
        
            let [ttl, ttr] = this.Trimfront(topl, topr, false)
            let [tbl, tbr] = this.Trimfront(botl, botr, false)
            
            pleft[leftbr.index].Opparam[1] = '$'+ttl.length.toString()
            pleft[leftbr.index].Opparam[2] = '$'+tbl.length.toString()
            pright[rightbr.index].Opparam[1] = '$'+ttr.length.toString()
            pright[rightbr.index].Opparam[2]= '$'+tbr.length .toString()
    
            let plend = pleft.slice(leftbr.index + leftbr.top + leftbr.bot + 1, pleft.length)
            pleft= pleft.slice(0, leftbr.index+1).concat(ttl).concat(tbl).concat(plend)
            let prend = pright.slice(rightbr.index + rightbr.top + rightbr.bot + 1, pright.length)
            pright= pright.slice(0, rightbr.index+1).concat(ttr).concat(tbr).concat(prend)
        }
        return this.genRule('!'+this.ExpToString(pleft)+ '@' +this.ExpToString(pright))
    }

    TrimBranch(pr){
        let [pleft, pright] = [pr.leftexps, pr.rightexps]
        let [leftbr, rightbr] = [this.getlastbr(pleft), this.getlastbr(pright)]
        if (leftbr.index == -1 || rightbr.index == -1) return pr
        let topr= pright.slice( (rightbr.top == 0 ? rightbr.index+rightbr.top +1: rightbr.index+1) , rightbr.index+rightbr.top+1)
        let topl= pleft.slice( (leftbr.top == 0 ? leftbr.index+leftbr.top +1: leftbr.index+1) , leftbr.index+leftbr.top+1)

        let botr= pright.slice((rightbr.bot == 0? rightbr.index+1+rightbr.top+rightbr.bot: rightbr.index+rightbr.top+1) , rightbr.index+rightbr.top+rightbr.bot+1)
        let botl= pleft.slice((leftbr.bot == 0 ? leftbr.index+1+leftbr.top+leftbr.bot: leftbr.index+leftbr.top+1) , leftbr.index+leftbr.top+leftbr.bot+1)

        let [ttl, ttr] = this.Trim(topl, topr)
        if(topl.length < topr.length){
            let temp = ttr 
            ttr = ttl 
            ttl = temp
        }

        let [tbl, tbr] = this.Trim(botl, botr)
        if(botl.length < botr.length){
            let temp = tbr 
            tbr = tbl 
            tbl = temp
        }

        pleft[leftbr.index].Opparam[1] = '$'+ttl.length.toString()
        pleft[leftbr.index].Opparam[2] = '$'+tbl.length.toString()
        pright[rightbr.index].Opparam[1] = '$'+ttr.length.toString()
        pright[rightbr.index].Opparam[2]= '$'+tbr.length .toString()

        let tr = this.genRule('!'+this.ExpToString(ttl)+ '@' + this.ExpToString(ttr))
        let br = this.genRule('!'+this.ExpToString(tbl)+ '@' + this.ExpToString(tbr))

        
        if(this.isRule(tr) && this.isRule(br)) return tr

        let plend = pleft.slice(leftbr.index + leftbr.top + leftbr.bot + 1, pleft.length)
        pleft= pleft.slice(0, leftbr.index+1).concat(ttl).concat(tbl).concat(plend)
        let prend = pright.slice(rightbr.index + rightbr.top + rightbr.bot + 1, pright.length)
        pright= pright.slice(0, rightbr.index+1).concat(ttr).concat(tbr).concat(prend)

        return this.genRule('!'+this.ExpToString(pleft)+ '@' +this.ExpToString(pright))
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
    getlastbr(exp){
        let br = {index : -1, next : {}, prev:-1, bot:exp.length, top:exp.length, br: ''}
        let bri = exp.length
        let ti = 0
        // console.log('leftbr: ', br)
        while(ti < exp.length) {
            if(exp[ti].Opparam){
                if(exp[ti].Opparam[0]){
                    if(this.BrOperators.includes(exp[ti].Opparam[0])){
                        if(ti > bri){
                            if(br.prev != -1){
                                bri = br.prev.index
                                br = br.prev
                            }
                        }
                        else{
                            // console.log('here')
                            br.next = {index : ti, next : {}, prev:br, top: parseInt(exp[ti].Opparam[1][1]), bot:parseInt(exp[ti].Opparam[2][1]), br: exp[ti].Opparam[0]}
                            let temp = br 
                            bri = br.next.bot + br.next.top
                            br = br.next
                            br.prev = temp  
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
                ret.push([(i,j)])
                j+=1
            }
            i+= 1
        }
        return ret
    }

    operationlist(cvtable, exps, flag = true){
        let i = 0
        let ret = []
        while(exps[i]){
            let srcropt = exps[i] 
            if(srcropt.Opparam.length == 0){
                let opt = srcropt.operator + srcropt.operands
                if(ret.includes(opt)){
                    ret.push(opt)
                }
            }
            i += 1
        }
        return cvtable
    }
    
    getcv(cvtable, exps){
        let i = 0
        while(exps[i]){
            let srcropt = exps[i] 
            if(srcropt.Opparam){
                if(srcropt.Opparam.length == 0 ){
                    if(this.parser.cv == srcropt.operator){
                        cvtable[srcropt.operands[0]] = ''
                    }
                }
            }
            i += 1
        }
        return cvtable
    }
    assigncv(cvtable, optlist, perm){
        let tcvtable = {...cvtable}
        for(const p of perm){
            if(tcvtable[p[0] + 1] == ''){
                tcvtable[(p[0] + 1).toString()] = optlist[p[1]].split(' ')
            }
        }
        return tcvtable
    }
    replacecv(cvtable, rule){
        let retr = this.genRule('!'+this.ExpToString(rule.leftexps) + '@' + this.ExpToString(rule.rightexps))
        for(const exp of retr.leftexps){
            if(exp.operator == this.parser.cv){
                let t = cvtable[exp.operands[0]]
                exp.operator = t[0]
                exp.operands = t.slice(1,t.length)
            }
        }
        for(const exp of retr.rightexps){
            if(exp.operator == this.parser.cv){
                let t = cvtable[exp.operands[0]]
                exp.operator = t[0]
                exp.operands = t.slice(1,t.length)
            }
        }
        return retr 
    }
    checkcv2(srcr, tarr){
        let sleft = srcr.leftexps
        let sright = srcr.rightexps
        let tleft = tarr.leftexps 
        let tright = tarr. rightexps 
        let con = sleft.concat(sright).concat(tleft).concat(tright)
        let cvtable = {}
        cvtable = this.getcv(cvtable, con)
        let optlist = this.operationlist( cvtable, srcr, false)
        let perm = this.genPermutation(Object.keys(cvtable).length, optlist.length)
        for(let i = 0 ; i < perm.length ; i ++){
            let tcvtable = this.assigncv(cvtable, optlist, perm, i)
            let replacedr = this.replacecv(tcvtable, tarr)
            if(this.isRule(replacedr)){
                console.log('!!!!')
            }
        }

        return true
        //

    }

    checkcv(l,r,rl,rr){
        let srcstatement = this.genRule('!'+this.ExpToString(l) + '@' + this.ExpToString(r))
        let left= srcstatement.leftexps
        let right = srcstatement.rightexps

        let tarstatement = this.genRule('!'+this.ExpToString(rl) + '@' + this.ExpToString(rr))
        let rleft = tarstatement.leftexps
        let rright = tarstatement.rightexps
        let cvtable = {}
        //check if expressions contain code variables
        
        let i = 0
        let found = false 
        let temp
        let ti = 0
        //retl should have same operations as l after iterating through rleft
        let retl= []
        // console.log(rleft)
        while (i < rleft.length){
            let t1 = rleft[i]
            let t2 = left[i]
            if(t1.operator && t1.Opparam == ''){
                if (t1.operator == this.parser.cv){
                    //set up code var in table
                    if(!cvtable[t1.operands[ti]]){
                        cvtable[t1.operands[ti]] = []
                        temp = t1.operands[ti]
                    }
                    else{
                        ti += 1
                    }
                    found = true                     
                }
                else{
                    if(t2){
                        if(!this.Same([t1],[t2])) return false
                        retl.push(t1)
                    }
                }
            }
            if(found){
                let j = i 
                //push every operation to retl until same
                while(j < left.length ){
                    t2 = left[j]
                    if(t2 && t1){
                        // console.log(t1,t2)
                        if(!this.Same([t1],[t2])){
                            // console.log(cvtable[temp])
                            
                            cvtable[temp].push(t2)
                            
                            retl.push(t2)
                        }
                    }
                    else{
                        found = false
                        break
                    }
                    j +=1
                }
            }
            i += 1
        }


        if(Object.keys(cvtable).length == 0) {
            return false
        }

        let x = 0
        let retr =[]
        while(x < rright.length){
            let t1 = rright[x]
            if(t1.operator){
                if(t1.operator == this.parser.cv)
                {
                    if(cvtable[t1.operands[0]]){
                        for(const e of cvtable[t1.operands[0]]){
                            retr.push(e)
                        }
                    }
                    
                }
                else{
                    retr.push(t1)
                }
            }
            x+=1
        }            

        if(this.Same(right,retr) && this.Same(left,retl)) {
            return true 
        }
        // let srcr = this.genRule('!'+this.ExpToString(left)+'@'+this.ExpToString(right))
        // let tarr = this.genRule('!'+this.ExpToString(retl)+'@'+this.ExpToString(retr))
        // if(this.OperatorEquivalence(srcr,tarr) && this.OperandEquivalence(srcr,tarr)){
        //     // console.log('equiv')
        //     return true
        // }
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
            // console.log(left,right, '|',rleft,rright)
            if(debug){
                console.log('begincv: ', this.RuleToString(relation))
            }
            
            // if(this.checkcv(left,right, rleft,rright)) return true
            // if(this.checkcv(left,right, rright,rleft)) return true
            // if(this.checkcv(right,left, rleft,rright)) return true
            // if(this.checkcv(right,left, rright,rleft)) return true
            if(this.checkcv2(relation, rule)) {
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
            // if(this.RuleToString(relation).includes('#100')){
            //     console.log(this.RuleToString(relation))
            //     console.log(this.RuleToString(rule))
            //     console.log(this.OperatorEquivalence(relation,rule))
            //     console.log(this.OperandEquivalence(relation,rule))
                
            // }
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
            if(e.Opparamb && brflag){
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

        if(this.ExpToString(srcstatement.leftexps).includes('#100') && this.ExpToString(tarstatement.rightexps).includes('#102')) {
            console.log('!!!', this.RuleToString(srcstatement), this.RuleToString(tarstatement))
            console.log('-----')
            console.log(srctablel)
            console.log(srctabler)
            console.log(tartablel)
            console.log(tartabler)
            console.log('-----')
        }
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
                    for(const opr of e.operands) {
                        ret.push(opr)
                    }
                }
            }
            else if(e.operands){
                for(const opr of e.operands) {
                    ret.push(opr)
                }
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
        // if(this.getBrOpt(tarstatement.leftexps) == '#102'){
        //     console.log('___')
        //     console.log('srctable: ', srctable)
        //     console.log('tartable: ', tartable)
        //     console.log('___')
        // }
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
                if(src[i].Opparam){
                    if(!tar[i].Opparam)return false
                    let j = 0
                    while(j < src[i].Opparam.length){
                        if(src[i].Opparam[j] != tar[i].Opparam[j]){
                            return false 
                        } 
                        j += 1
                    }
                }
                
                //check operands match
                if(src[i].operands){
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

    //--ML data--
    rule_to_mldata(r){
        let rr = r.rightexps
        let rl = r.leftexps
        // console.log(rr, rl)
        const ret = []

        ret.push('')
        for(const e of rr){
            if(!e.operator) continue

            let d = e.operator.trim()
            if(!ret.includes(d))
                ret.push(d)
        }
        for(const e of rl){
            if(!e.operator) continue

            let d = e.operator.trim()
            if(!ret.includes(d))
                ret.push(d)
        }
        return ret
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

    //will have operations that are not semantically correct, but all the right ones are in there lol
    Generate_sim_exps(exp){
        let ret = []
        // console.log(this.AllOperators)
        let op = ''
        let i = 0 
        let found = false
        while(i < exp.length) {
            let c = exp[i]
            if(c == ' ' || c == ',' || c =='$' || c =='&') {
                found = false
                //binary
                for(const bin of this.binaryOperators){

                    if(bin == op){
                        for(const bin2 of this.binaryOperators){
                            let p = exp.replaceAll(op + ' ', bin2 + ' ')

                            ret.push(p)
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