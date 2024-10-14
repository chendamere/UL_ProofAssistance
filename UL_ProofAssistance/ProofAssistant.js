



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
        // if(debug){
        //     console.log('------Proving-------')
        //     console.log('start: ', start, 'end: ', end)
        // }
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
                            let tii = ti + topi +1
                            while(tii<= ti+topi+boti && tii < exp.length){
                                e = tempexp[tii]
                                ret.push(e)
                                tii +=1
                            }
                            tii = ti + 1
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
    TrimBranchFront(left, right){
        const l = []
        const retl = []
        const retr = []
        for(const e of left){
            l.push(e)
            retl.push(e)
        }
        const r= []
        for(const e of right){
            r.push(e)
            retr.push(e)

        }
        let i = 0
        let lbr = 0 
        let lbrtop = retl.length - 1 
        let lbrbot= retr.length - 1

        let rbr = 0 
        let rbrtop = retl.length - 1 
        let rbrbot= retr.length - 1


        let foundbr = false

        let lnewtop = 0
        let lnewbot = 0
        let rnewtop = 0
        let rnewbot = 0
        let trimfront = true
        let topend = false 
        let botend = false 

        while(i < l.length) {
            if(i < lbr + lbrtop + lbrbot ){
                
                //trim like normal
                if(r[i] && r[i]){
                    if(!foundbr){
                        //if br dont trim
                        if(!l[i].Opparam || !r[i].Opparam) break

                        if(!l[i].Opparam[0] || !r[i].Opparam[0]) break
                        // console.log(left[i].Opparam[0], i)
                        if(l[i].Opparam[0] != ''){

                            if(this.parser.branch.includes(l[i].Opparam[0])){
                                // console.log('here')

                                lbr = i
                                lbrtop = parseInt(l[i].Opparam[1][1]) 
                                lbrbot = parseInt(l[i].Opparam[2][1])
                                // console.log('here1',lbrtop)

                                rbr = i
                                rbrtop = parseInt(r[i].Opparam[1][1]) 
                                rbrbot = parseInt(r[i].Opparam[2][1])
                                lnewtop = lbrtop
                                lnewbot = lbrbot
                                rnewtop = rbrtop
                                rnewbot = rbrbot
                                foundbr = true 
                            }
                        }
                        if(this.Same([l[i]] ,[r[i]]) && trimfront)
                        {
                                //slice if not branch opr
                                retl.splice(0, 1)
                                retr.splice(0, 1)
                        }
                        else{
                            trimfront = false
                        }
                    }
                    else{
                        //found br skip the first operation because it is br 
                        //trim top expression

                        if(topend && botend ) break
                        if(lnewtop > 0 && rnewtop > 0)
                        {                            
                            // console.log('left1.5:', this.ExpToString(retl),  this.ExpToString(left))
                            if(this.Same([l[i]] ,[r[i]]) && !topend){
                                // console.log('before1: ', this.ExpToString(retl), this.ExpToString(retr))
                                retl.splice(1, 1)
                                lnewtop -=1
                                let v = retl[0].Opparam[1]
                                v='$'+ lnewtop
                                retl[0].Opparam[1]=v

                                retr.splice(1, 1)
                                rnewtop -=1
                                v = retr[0].Opparam[1]
                                v='$'+ rnewtop
                                retr[0].Opparam[1]=v

                                // console.log('after1: ', this.ExpToString(retl), this.ExpToString(retr))
                                // console.log('left2:', this.ExpToString(retl),  this.ExpToString(left))

                                const ret = this.genRule('!'+this.ExpToString(retl)+'@'+this.ExpToString(retr))
                                if(this.isRule(ret)) return ret 
                            }
                            else{topend = true}
                        }
                        if(lnewbot > 0 && rnewbot > 0){
                            //if bot is same trim bot, else break
                            if(this.Same([l[i+lbrtop]] ,[r[i + rbrtop]]) &&!botend){
                                                        

                                // console.log('before2: ', this.ExpToString(retl), this.ExpToString(retr))

                                retl.splice(i+lbrtop, 1)
                                lnewbot -=1
                                let v = retl[0].Opparam[2]
                                v = '$'+ lnewbot
                                retl[0].Opparam[2]=v

                                retr.splice(i+rbrtop, 1)
                                rnewbot -=1
                                v = retr[0].Opparam[2]
                                v = '$'+ rnewbot
                                retr[0].Opparam[2]=v
                                // console.log('after2: ', this.ExpToString(retl), this.ExpToString(retr))

                                const ret = this.genRule('!'+this.ExpToString(retl)+'@'+this.ExpToString(retr))
                                if(this.isRule(ret)) return ret 
                            // console.log('trim2: ', this.ExpToString(retl), this.ExpToString(retr))

                            }
                            else{
                                botend = true
                            }
                        }
                    }
                }
                i += 1
            }
            else{
                // console.log('break')
                break
            }
        }
        // console.log('start trimming end: ', this.ExpToString(retl), this.ExpToString(retr))
        let endi = retl.length -1 
        let endj = retr.length -1
        while(endi >= 0 && endj >= 0 && endi > lbr+lbrtop+lbrbot && endj > rbr + rbrtop+rbrbot){
            if(this.Same(retl[endi], retr[endj]))
            {
                retl.splice(retl.length-1, 1)
                retr.splice(retr.length-1, 1)
            }else{
                // console.log('break')

                break
            }
            endi -= 1 
            endj -= 1
        }
        // console.log('left3:', this.ExpToString(left))

        let finr = this.genRule('!'+this.ExpToString(retl)+'@'+this.ExpToString(retr))
        // console.log('fail',this.RuleToString(finr))
        // console.log()
        return finr
    }

    trim_and_check(parsed_newrule) {

        //when trimming rule we need to record the branch Opparam is trimmed, any
        //after production, we need to go to the last branch operation and revise the end offsets 
        //end offsets are length of new expression.
        //need to keep track of bottom of top offset

        //alternatively, trim like normal, and trim twice again for bottom and top expressions.

        //need to trim #14 to left branch and right branch
        // console.log('before:    ', this.RuleToString(parsed_newrule))

        //hard copy 

        //copying like this doesnt work for fields, have to specify all fields... we can gen a new rule from strings
        const t = this.genRule('!'+this.ExpToString(parsed_newrule.leftexps)+'@'+this.ExpToString(parsed_newrule.rightexps))

        //trimming will allow any rule that have same left and right to return true
        // console.log('parsed_newrule: ', this.RuleToString(parsed_newrule))

        let [trimleft, trimright] = this.Trim(t)
        let long = trimleft
        let short = trimright
        if(long.length < short.length){
            long= trimright
            short = trimleft
        }

        let trimrule = '! ' + this.ExpToString(short) + ' @ ' + this.ExpToString(long)
        let parsed_trimrule = this.Operands_normalize(this.genRule(trimrule))
        // console.log('parsed_trimrule1: ', trimrule)

        // console.log('parsed_trimrule2: ', this.RuleToString(parsed_trimrule), this.isRule(parsed_trimrule))

        // throw new Error('here')

        //dont pass the original rule, pass copies of the expression
        let ret =[]

        if(this.isRule(parsed_trimrule)){
            // if(parsed_trimrule.leftexps[0].operator && parsed_trimrule.rightexps[0].operator){
                ret.push(parsed_trimrule)
                // console.log('parsed_trim is a rule: ', this.RuleToString(ret[0]))
                return ret
            // }
        }
        
        //trim branch trim top and bot of both expressions, does not include branch
        // console.log('before trim: ',this.RuleToString(parsed_newrule))
        const r = this.genRule('!'+this.ExpToString(parsed_newrule.leftexps)+'@'+this.ExpToString(parsed_newrule.rightexps))

        let trimbr = this.TrimBranch(r)
        // console.log('after trimbr: ', this.RuleToString(trimbr[0]), this.RuleToString(trimbr[1]))

        // console.log('trimbr0:', this.RuleToString(trimbr[0]),'trimbr1:',  this.RuleToString(trimbr[1]))
        if(trimbr[0] != -1){
            let trimagain1 = this.genRule('!'+this.RuleToString(trimbr[0]))
            if(this.isRule(trimagain1)){
                // if(trimagain1.leftexps[0].operator && trimagain1.rightexps[0].operator){
                    console.log(this.RuleToString(trimagain1), this.isRule(trimagain1))
                    ret.push(trimbr[0])
                    return ret

                    // console.log('trimbranch found rule at top expression: ', this.RuleToString(ret[0]))

                // }
            }
        }
        if(trimbr[1] != -1){

            let trimagain2 = this.genRule('!'+this.RuleToString(trimbr[1]))
            
            if(this.isRule(trimagain2)){
                // if(trimagain2.leftexps.operator && trimagain2.rightexps.operator){
                    console.log(this.RuleToString(trimagain2), this.isRule(trimagain2))

                    ret.push(trimbr[1])
                    return ret

                    // console.log('trimbranch found rule at bot expression: ', this.RuleToString(ret))

                // }
            }
            
                   
        }

        if(ret.length == 0){

            const t3 = this.genRule('!'+this.ExpToString(parsed_newrule.leftexps)+'@'+this.ExpToString(parsed_newrule.rightexps))

            let t3left = t3.leftexps
            let t3right= t3.rightexps
            // console.log('before trim: ',this.RuleToString(parsed_newrule))
            let trimbrfront = this.TrimBranchFront(t3left,t3right)
            // console.log('after trim: ', this.RuleToString(parsed_newrule))
            if(this.isRule(trimbrfront)){
                if(trimbrfront.leftexps[0].operator && trimbrfront.rightexps[0].operator){
                    ret.push(trimbrfront)
                    return ret

                    // console.log('trimfront found rule: ', this.RuleToString(ret[0]))

                }
            }
        }
        if(ret.length == 0)ret.push(-1)
        // console.log('empty')
        return ret
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
        let br = {index : -1, next : {}, prev:-1, bot:exp.length, top:exp.length}
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
                            br.next = {index : ti, next : {}, prev:br, bot: parseInt(exp[ti].Opparam[1][1]), top:parseInt(exp[ti].Opparam[2][1])}
                            bri = br.next.bot + br.next.top
                            br = br.next 
                        }
                    }
                }
            }
            ti +=1
        }
        return br 
    }
    Trim(parsed_newrule) {

        let pleft = parsed_newrule.leftexps.slice()
        let lefti =0
        let leftendi = pleft.length-1

        let pright = parsed_newrule.rightexps.slice()
        let righti =0
        let rightendi = pright.length-1

        const retl = []
        const retr = []
        for(const e of pleft){
            retl.push(e)
        }
        for(const e of pright){
            retr.push(e)

        }
        let frontstop = false
        let endstop = false
        let leftbr = this.getlastbr(pleft)
        let rightbr = this.getlastbr(pright)
        let lretindex = leftbr.index
        let rretindex = rightbr.index
        let topstop = true
        let botstop = true
        let lbotoffset=0
        let rbotoffset=0
        if(leftbr.index != -1){
            topstop = false
            lbotoffset = leftbr.bot
        }
        if(rightbr.index != -1){
            botstop = false
            rbotoffset = rightbr.bot
        }
        console.log('start trimming: ', this.RuleToString(parsed_newrule))
        while(true) {
            console.log(this.ExpToString(retl), this.ExpToString(retr))
            //exit condition

            if(lretindex > -1 && lefti >= lretindex){
                frontstop = true
            }
            if(rretindex > -1 && righti >= rretindex){
                frontstop = true
            }

            if(frontstop && endstop) break

            //trim front once
            if(!frontstop && this.Same([pleft[lefti]],[pright[righti]])){
                retl.splice(0, 1)
                retr.splice(0, 1)
                let prule = this.genRule('!'+this.ExpToString(retl) + '@'+this.ExpToString(retr))
                // console.log('prule: ', this.RuleToString(prule))

                if(this.isRule(this.Operands_normalize(prule))) {
                    // console.log('0')
                    
                    return [retl, retr]
            
                }    
                lefti += 1
                righti += 1
                if(rretindex!=0 && lretindex!=0){
                    rretindex -=1
                    lretindex -=1
                }
                
            }else{frontstop = true }
            
            //trim back once
            if(!endstop){


                if(!botstop){
                    console.log('botcheck: ', this.inBotBranch(leftbr,leftendi) , (this.inBotBranch(rightbr, rightendi)) , this.Same([pleft[leftendi]],[pright[rightendi]]))
                    if(this.inBotBranch(leftbr,leftendi) && (this.inBotBranch(rightbr, rightendi)) && this.Same([pleft[leftendi]],[pright[rightendi]])){
                        if(leftendi-(leftbr.bot)- lefti != lretindex){
                            retl.splice(leftendi- lefti, 1)
                            retl[lretindex].Opparam[1] = '$' + (parseInt(retl[lretindex].Opparam[2][1])- 1).toString()
                            leftbr.bot -= 1
                        }
                        if(rightendi-(rightbr.bot)- righti != rretindex){
                            retr.splice(rightendi- righti, 1)
                            retr[rretindex].Opparam[1] = '$' + (parseInt(retr[rretindex].Opparam[2][1])- 1).toString()
                            rightbr.bot -= 1
                        }       
                        let pruleb = this.Operands_normalize(this.genRule('!'+this.ExpToString(retl) + '@'+this.ExpToString(retr)))
                        if(this.isRule(pruleb)) {
                            return [retl, retr]
                        } 
                    }
                    else{
                        botstop = true
                    }                   
                } 
                
                if(!topstop){
                    console.log('topcheck: ', this.inTopBranch(leftbr,leftendi, lbotoffset), (this.inTopBranch(rightbr, rightendi, rbotoffset)), this.Same([pleft[leftendi-lbotoffset]],[pright[rightendi - rbotoffset]]))
                    // console.log(this.ExpToString([pleft[leftendi-lbotoffset]]), this.ExpToString([pright[rightendi-rbotoffset]]))
                    // console.log(this.inTopBranch(leftbr,leftendi, lbotoffset), leftbr, leftendi, lbotoffset)
                    // console.log(this.inTopBranch(rightbr,rightendi, rbotoffset), rightbr, rightendi, rbotoffset)
                    if(this.inTopBranch(leftbr,leftendi, lbotoffset) && (this.inTopBranch(rightbr, rightendi, rbotoffset) && this.Same([pleft[leftendi-lbotoffset]],[pright[rightendi- rbotoffset]]))){
                        if(leftendi - lefti != lretindex){
                            retl.splice(leftendi- lefti, 1)
                            retl[lretindex].Opparam[1] = '$' + (parseInt(retl[lretindex].Opparam[1][1])- 1).toString()
                            leftbr.top -= 1
                        }
                        if(rightendi - righti != rretindex){
                            retr.splice(rightendi- righti, 1)
                            retr[rretindex].Opparam[1] = '$' + (parseInt(retr[rretindex].Opparam[1][1])- 1).toString()
                            rightbr.top -= 1
                        }
                        let pruleb = this.Operands_normalize(this.genRule('!'+this.ExpToString(retl) + '@'+this.ExpToString(retr)))
                        if(this.isRule(pruleb)) {
                            return [retl, retr]
                        }   
                    }
                    else{
                        topstop = true
                    }                 
                }         
                if(!topstop && !botstop){
                    leftendi -= 2
                    rightendi -= 2
                }                               
                if(topstop && botstop){
                    //trim end like usual
                    if(this.Same([pleft[leftendi]],[pright[rightendi]])){
                        retl.splice(retl.length-1,1)
                        retr.splice(retr.length-1,1)

                        let prule = this.Operands_normalize(this.genRule('!'+this.ExpToString(retl) + '@'+this.ExpToString(retr)))
                        leftendi -= 1
                        rightendi -= 1
                        if(this.isRule(prule)) {
                            // console.log('3', this.RuleToString(prule))
                        
                            return [retl, retr]
                        }
                    }
                    else{
                        endstop = true
                    }
                    
                }
            }
        }
        // console.log('4')

        return [retl, retr]
    }

    inBranch(br, i) {
        return (br.index > -1) 
        && (i <= br.index+br.top+br.bot) 
        && (i >= br.index+ br.top) 
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

    //trim branch takes the last br operation found from left to right 
    //and trim top and bottom expressions individuality
    TrimBranch(parsed_newrule){
        // console.log(this.RuleToString(parsed_newrule))
        let pleft = parsed_newrule.leftexps
        let pright = parsed_newrule.rightexps
        let longer = pleft 
        let shorter = pright 
        if(shorter.length > longer.length){
            shorter = pleft 
            longer = pright
        }
        let i = 0
        let j = 0
        let topi = i
        let boti = i
        let bri = {index : -1, next : {}, prev:-1, bot:longer.length, top:longer.length}
        let brendi = longer.length
        let topj = j
        let botj = j
        let brj = {index : -1, next : {}, prev:-1, bot:shorter.length, top:shorter.length}
        let brendj = shorter.length
        let checkbegin = false

        while(i < longer.length ) {
                if(i > brendi && bri.prev !=-1){
                    //we are at the last branch level
                    bri = bri.prev  
                }
                if(longer[i].Opparam && longer[i].Opparam != '')
                {
                    topi = parseInt(longer[i].Opparam[1].slice(1))
                    boti = parseInt(longer[i].Opparam[2].slice(1))
                    brendi = brendi.index+topi + boti
                    bri.next = {index : i, next : {}, prev:bri , bot: boti, top:topi} 
                    bri = bri.next
                    checkbegin = true
                }
                else{
                    if(!shorter[i] || !longer[i]|| (!checkbegin && !this.Same(shorter[i],longer[i])) ){
                        break
                    }
                }
                i = i + 1
        }
        while(j < shorter.length ) {
            if(j > brendj&& brj.prev && brj.prev != -1){
                //we are at the last branch level
                brj = brj.prev  
            }

            if(shorter[j].Opparam && shorter[j].Opparam != '')
            {
                topj = parseInt(shorter[j].Opparam[1].slice(1))
                botj = parseInt(shorter[j].Opparam[2].slice(1))
                brendj = brendj.index+ topj + botj
                brj.next = {index : j, next : {}, prev:brj , bot: botj, top:topj} 
                brj = brj.next
                // console.log('opparam2: ',topi,boti)
            }
            j = j + 1
        }

        //checking
        while(j < shorter.length && j > brj.index+brj.top+brj.bot){
            if(!this.Same(shorter[j],longer[j])) return[-1,-1]
            j += 1
        }

        if(bri.index == -1 || brj.index == -1) return [-1,-1]
        // console.log('ere: ',longer[bri.index].Opparam,longer[brj.index].Opparam)
        if(longer[bri.index].Opparam != longer[brj.index].Opparam) return[-1,-1]

        let topl=[], botl=[], topr=[], botr=[]
        if(topi <= longer.length && topi != 0){
            topl = longer.slice(bri.index+1, bri.index+topi+1)
        }
        if(boti <= longer.length&& boti != 0){
            botl = longer.slice(bri.index+topi+1, bri.index+topi+boti+1)
        }

        if(topj <= shorter.length&& topj != 0){
            topr = shorter.slice(brj.index+1, brj.index+topj+1)
        }
        if(botj <= shorter.length&& botj != 0){
            botr = shorter.slice(brj.index+topj+1, brj.index+topj+botj+1)
        }
        // console.log('topj: ', topj, 'topi: ', topi)
        // console.log('longer: ', this.ExpToString(longer))
        // console.log('shorter: ', this.ExpToString(shorter))

        let toprule = this.Operands_normalize(this.genRule('!'+this.ExpToString(topl)+'@'+this.ExpToString(topr)))
        let botrule = this.Operands_normalize(this.genRule('!'+this.ExpToString(botl)+'@'+this.ExpToString(botr)))

        return [toprule,botrule]
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
            if(t1.operator){
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

        // console.log('rleft: ',this.ExpToString(rleft), 'retl: ',this.ExpToString(retl),'rright: ',this.ExpToString(rright), 'retr: ',this.ExpToString(retr))
        if(this.Same(right,retr) && this.Same(left,retl)) {
            // console.log('left: ',this.ExpToString(left), 'retl: ',this.ExpToString(retl),'r: ',this.ExpToString(r), 'retr: ',this.ExpToString(retr))
            return true 
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
            // console.log(left,right, '|',rleft,rright)
            if(debug){
                console.log('begincv: ', this.RuleToString(relation))
            }
            if(this.checkcv(left,right, rleft,rright)) return true
            if(this.checkcv(left,right, rright,rleft)) return true
            if(this.checkcv(right,left, rleft,rright)) return true
            if(this.checkcv(right,left, rright,rleft)) return true

            
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
            if(this.Same(left, rright)) {
                if(this.Same(right, rleft)){
                    // console.log('2 ', left, rleft)

                    return true
                }
            }
            // console.log('match: ', this.RuleToString(relation), 'not applicable: ', this.RuleToString(rule), 'oprequiv: ', this.OperatorEquivalence(relation,rule), 'oprndsequiv: ', this.OperandEquivalence(relation,rule))
            if(this.OperatorEquivalence(relation,rule) && this.OperandEquivalence(relation,rule)){
                // console.log('equiv')
                return true
            }

            i += 1
        }       
        
        return false 
    }

    operatorlist(src, opt){
        let ret =[]
        for (const e of src){
            if(e.Opparam){
                if(e.Opparam.length!=0){
                    // console.log(e.Opparam)
                    // if(opt && e.Opparam[0] == '#12'){
                    //     ret.push('#13')
                    // }else{
                    //     ret.push(e.Opparam[0])
                    // }
                    ret.push(e.Opparam[0])
                    ret.push(e.Opparam[1])
                    ret.push(e.Opparam[2])
                }
            }
            if(e.operator){
                // if(e.Opparam){
                //     if(e.Opparam.length!=0){
                //         if(opt && e.Opparam[0] == '#12'){
                //             ret.push(opt)
                //         }
                //         else{
                //             ret.push(e.operator)
                //         }
                //     }
                //     else{
                //         ret.push(e.operator)
                //     }
                // }
                // else{
                    ret.push(e.operator)
                // }
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
        // if(opt == '#17' && tartablel[0] == '#102'){
        //     console.log('!!!!! l', tartablel )
        //     console.log('!!!!! r', tartabler )
        // }
        // if(opt){
        //     console.log('!!!!!!!!!!!!!!!!!!!!!!', opt, )
        //     console.log('!!!!! l', tartablel )
        //     console.log('!!!!! r', tartabler )
        // }
        //checking
        if(tartablel.length != srctablel.length && tartablel.length != srctabler.length ) return false
        if(tartabler.length != srctablel.length && tartabler.length != srctabler.length ) return false
        if(!(this.listequal(srctablel,tartablel) && this.listequal(srctabler,tartabler)) && !(this.listequal(srctabler,tartablel) && this.listequal(srctablel,tartabler))) return false
        // console.log(srctablel,'@',srctabler,'|', tartablel,'@',tartabler)
        return true
    }

    
    operandlist(src){
        let ret =[]
        for (const e of src){
            if(e.operands){
                for(const opr of e.operands) {
                    ret.push(opr)
                }
            }
        }
        return ret
    }
    OperandEquivalence(srcstatement, tarstatement){
        let srctable = this.operandlist(srcstatement.leftexps).concat(this.operandlist(srcstatement.rightexps))
        let tartable = this.operandlist(tarstatement.leftexps).concat(this.operandlist(tarstatement.rightexps))
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