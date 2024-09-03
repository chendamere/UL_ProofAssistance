



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
        this.unaryOperators = ['#1','#2','#3','#4','#5','#9']
        this.binaryOperators = ['#8','#6','#7','#10']
        this.BrOperators = ['#12', '#13']
        this.AddSpacetoExp()

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

    genRule(rule){
        return this.parser(rule)
    }
    
    //proof is complete if used rules exists and deduction steps provided
    Prove_From_Exps(rule) {
        // console.log(rule.leftexps)
        console.log()
        console.log('   ---------Prove From Exps----------')
        console.log('| Proving: ' ,this.RuleToString(rule))
        console.log()
        let leftexps = rule.leftexps
        let rightexps = rule.rightexps

        // let newrule = {type:"Equivalence rule", leftexps:[], rightexps:[]} 
        console.log('   | Start |: ', this.ExpToString(leftexps), ' | Goal |: ', this.ExpToString(rightexps))
        console.log('   | Enter equivalence exps: \n')
        // console.log('@')
        if(this.Proving(leftexps, rightexps))
            return true
        else{
            return false
        }
    }

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

        
        // console.log(ret)
        // console.log(ret.length, this.Exps.length)
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

        
        // console.log(ret)
        // console.log(ret.length, this.Exps.length)
        let s = new Set(ret)
        let sl = Array.from(s)
        if(sl.length == 0 ) return [exp]
        return sl
    }

    Proving(start, e) {

        //operands are not binded yet
        // console.log('start: ', start, 'end: ', e)
        let r = (this.genRule('!'+start+'@'+e+'\n')[0])

        //bind operands to one of the variant
        let rvariant = this.try_match_operand_order(r)        
        for( const v of rvariant){
            let [tempv] = [v].map((x)=>x)
            // console.log('variant:' , this.RuleToString(v))

            if(!this.isRule(tempv)){
                // console.log('next1', this.RuleToString(tempv))
                // let x = this.trim_and_check(tempv)
                let rules = this.trim_and_check(v)
                // console.log('next2', this.RuleToString(tempv))

                let check = -1
                let i =0
                while(i < rules.length){
                    if(rules[i] != -1)
                    {
                        // console.log('fds',this.RuleToString(rules[i]))
                        check =rules[i]
                    }
                    i+=1
                }

                // console.log('rules: ', rules)
                if (check != -1){

                    console.log('next', this.ExpToString(tempv.rightexps))
                    return [this.ExpToString(tempv.rightexps), this.rule_to_mldata(check)]
                }
            }
        }
        // console.log('no matching production')

        return -1
    }


    rule_to_mldata(r){
        let rr = r.rightexps
        let rl = r.leftexps
        // console.log(rr, rl)
        const ret = []

        ret.push('')
        for(const e of rr){
            if(!e.operator) continue

            let d = e.operator.value.trim()
            if(!ret.includes(d))
                ret.push(d)
        }
        for(const e of rl){
            if(!e.operator) continue

            let d = e.operator.value.trim()
            if(!ret.includes(d))
                ret.push(d)
        }
        return ret
    } 
    

    //return all different configuration of operands opdering 
    try_match_operand_order(parsed_newrule) {

        // if(!parsed_newrule) return false
        let tar = parsed_newrule.rightexps
        let src = parsed_newrule.leftexps
        if(!tar || !src) return false

        let endmax = this.getmax(tar)
        let endmaxcounter= 0
        let ret = []
        ret.push(parsed_newrule)
        while(endmaxcounter < endmax){
            if(tar.length == 0) break

            let target = this.ExpToString(this.incOperands(tar))

            let tr = '! ' + this.ExpToString(src) + ' @ ' + target + '\n'
            let parsed_tr = this.genRule(tr)[0]

            // console.log('t:  ',parsed_tr)

            // console.log('incr operands: ', this.RuleToString(parsed_tr))
            ret.push(parsed_tr)
            
            endmaxcounter += 1
        }
        // console.log(ret)
        return ret
    }

    TrimBranchFront(left, right){
        // const test = left.slice()
        // test.push('s')
        // console.log('left:', this.ExpToString(left))

        // const test = left.slice()
        // test.splice(0,1)
        // console.log('test:', this.ExpToString(left))
        // console.log('begin: ', this.ExpToString(l), '@', this.ExpToString(r))
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

        while(i < l.length) {
            if(i < lbr + lbrtop + lbrbot ){
                
                //trim like normal
                if(r[i] && r[i]){
                    if(!foundbr){
                        if(this.Same([l[i]] ,[r[i]]))
                        {
                            // console.log('same?: ', this.ExpToString([left[i]]), this.ExpToString([right[i]]))

                            //if br dont trim
                            if(!l[i].Opparam[0] || !r[i].Opparam[0]) break
                            // console.log(left[i].Opparam[0], i)
                            if(l[i].Opparam && r[i].Opparam && l[i].Opparam[0].value != ''){

                                if(l[i].Opparam[0].value == '#12' || l[i].Opparam[0].value == '#13'){
                                    // console.log('here')

                                    lbr = i
                                    lbrtop = parseInt(l[i].Opparam[1].value[1]) 
                                    lbrbot = parseInt(l[i].Opparam[2].value[1])
                                    // console.log('here1',lbrtop)

                                    rbr = i
                                    rbrtop = parseInt(r[i].Opparam[1].value[1]) 
                                    rbrbot = parseInt(r[i].Opparam[2].value[1])
                                    lnewtop = lbrtop
                                    lnewbot = lbrbot
                                    rnewtop = rbrtop
                                    rnewbot = rbrbot
                                    foundbr = true 
                                    
                                }
                            }else{
                                //slice if not branch opr
                                retl.splice(0, 1)
                                retr.splice(0, 1)
                            }
                        }
                        else{
                            // console.log('break: ', this.ExpToString(retl), this.ExpToString(retr))

                            break
                        }
                    }
                    else{
                        //found br skip the first operation because it is br 
                        //trim top expression
                        if(lnewtop > 0 && rnewtop > 0)
                        {
                            // console.log('before1: ', this.ExpToString(retl), this.ExpToString(retr))
                            // console.log('left1.5:', this.ExpToString(retl),  this.ExpToString(left))

                            retl.splice(1, 1)
                            lnewtop -=1
                            // retl[0].Opparam[1].value = '$'+ lnewtop
                            let v = retl[0].Opparam[1].value
                            v='$'+ lnewtop
                            retr.splice(1, 1)
                            rnewtop -=1
                            v = retr[0].Opparam[1].value
                            v='$'+ rnewtop
                            // console.log('after1: ', this.ExpToString(retl), this.ExpToString(retr))
                            // console.log('left2:', this.ExpToString(retl),  this.ExpToString(left))

                            const ret = this.genRule('!'+this.ExpToString(retl)+'@'+this.ExpToString(retr)+'\n')[0]
                            if(this.isRule(ret)) return ret 

                        }
                        if(lnewbot > 0 && rnewbot > 0){
                            //if bot is same trim bot, else break
                            if(this.Same([l[i+lbrtop]] ,[r[i + rbrtop]])){
                                                        

                                // console.log('before2: ', this.ExpToString(retl), this.ExpToString(retr))

                                retl.splice(i+lbrbot, 1)
                                lnewbot -=1
                                let v = retl[0].Opparam[2].value
                                v = '$'+ lnewbot
                                // retl[0].Opparam[2].value = '$'+ lnewbot
                                // if(this.isRule(ret)) return ret 
                                
                                retr.splice(i+rbrbot, 1)
                                rnewbot -=1
                                v = retr[0].Opparam[2].value
                                v = '$'+ rnewbot
                                // retr[0].Opparam[2].value = '$'+ rnewbot
                                // console.log('after2: ', this.ExpToString(retl), this.ExpToString(retr))
                                // console.log('left:', this.ExpToString(left))

                                const ret = this.genRule('!'+this.ExpToString(retl)+'@'+this.ExpToString(retr)+'\n')[0]
                                if(this.isRule(ret)) return ret 
                            // console.log('trim2: ', this.ExpToString(retl), this.ExpToString(retr))

                            }
                            else{break}
                        }
                        else{
                            // console.log('break: ', this.ExpToString(retl), this.ExpToString(retr))
                            break
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

        let finr = this.genRule('!'+this.ExpToString(retl)+'@'+this.ExpToString(retr)+'\n')[0]
        // console.log('fail',this.RuleToString(finr))
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
        let [t] = [parsed_newrule].map((x) => x);


        let left = t.leftexps.map((x) => x)
        let right= t.rightexps.map((x) => x)
        //trimming will allow any rule that have same left and right to return true
        let [trimleft, trimright] = this.Trim(t)
        let long = trimleft
        let short = trimright
        if(long.length < short.length){
            long= trimright
            short = trimleft
        }
        // console.log('after:    ', this.RuleToString(parsed_newrule))

        // console.log(this.RuleToString(parsed_newrule), bri, brj)

        // console.log('trim: ',this.ExpToString(trimShort), this.ExpToString(trimLong))
        let trimrule = '! ' + this.ExpToString(short) + ' @ ' + this.ExpToString(long) + '\n'
        let parsed_trimrule = this.Operands_normalize(this.genRule(trimrule)[0])

        // console.log('parsed_newrule: ', this.RuleToString(parsed_newrule))

        // console.log('parsed_trimrule: ', this.RuleToString(parsed_trimrule))

        //dont pass the original rule, pass copies of the expression
        // console.log('t: ', this.RuleToString(t), this.ExpToString(trimbrfront[0]), this.ExpToString(trimbrfront[1]))
        // console.log('trimfront: ', this.ExpToString(trimbrfront.leftexps), this.ExpToString(trimbrfront.rightexps))
        let ret =[]

        if(this.isRule(parsed_trimrule)){
            // if(parsed_trimrule.leftexps[0].operator && parsed_trimrule.rightexps[0].operator){
                ret.push(parsed_trimrule)
                console.log('wow1: ', this.RuleToString(ret[0]))

            // }
        }
        
        //trim branch trim top and bot of both expressions, does not include branch
        // console.log('before trim: ',this.RuleToString(parsed_newrule))

        let trimbr = this.TrimBranch(t)
        // console.log('after trim: ', this.RuleToString(parsed_newrule))

        // console.log('trimbr0:', this.RuleToString(trimbr[0]),'trimbr1:',  this.RuleToString(trimbr[1]))
        if(trimbr[0] != -1){
            let trimagain1 = this.genRule('!'+this.RuleToString(trimbr[0])+'\n')[0]
            if(this.isRule(trimagain1)){
                // if(trimagain1.leftexps[0].operator && trimagain1.rightexps[0].operator){
                    ret.push(trimbr[0])
                    console.log('wow2: ', this.RuleToString(ret[0]))

                // }
            }
            
        }
        if(trimbr[1] != -1){

            let trimagain2 = this.genRule('!'+this.RuleToString(trimbr[1])+'\n')[0]
            
            if(this.isRule(trimagain2)){
                // if(trimagain2.leftexps[0].operator && trimagain2.rightexps[0].operator){
                    ret.push(trimbr[1])
                    console.log('wow3: ', this.RuleToString(ret[0]))

                // }
            }
            
                   
        }

        // console.log('before trim: ',this.RuleToString(parsed_newrule))
        let trimbrfront = this.TrimBranchFront(left,right)
        // console.log('after trim: ', this.RuleToString(parsed_newrule))

        if(this.isRule(trimbrfront)){
            if(trimbrfront.leftexps[0].operator && trimbrfront.rightexps[0].operator){
                ret.push(trimbrfront)
                console.log('wow4: ', this.RuleToString(ret[0]))

            }
        }

        if(ret.length == 0)ret.push(-1)


        // console.log('empty')
        return ret
    }

    getmax(exps){
        let i = 0
        let ret = exps
        let max = 0
        while(i < ret.length){
            let j = 0

            if(ret[i].operands){
                while(j < ret[i].operands.length)
                {
                    if(parseInt(ret[i].operands[j].value) > max){
                        max = parseInt(ret[i].operands[j].value)
                    }
                    j += 1
                }
            }
                

            i+=1
        }
        return max
    }

    //operands of left and right exps are equivalent iff 
    incOperands(exps){
        let i = 0
        let ret = exps
        let max = this.getmax(ret)
        // console.log(max)

        while(i < ret.length){
            let j = 0
            // console.log(ret[i])

            if(ret[i].operands){

                // console.log(ret[i])
                while(j < ret[i].operands.length)
                {
                    if(ret[i].operands[j].type != 'optional'){
                        let temp = parseInt(ret[i].operands[j].value)
                        if(temp == max){
                            temp = 1
                        }
                        else{
                            temp += 1
                        }
                        ret[i].operands[j].value = String(temp)
                    }
                    
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
                    if(exp[ti].Opparam[0].value === '#13' || exp[ti].Opparam[0].value === '#12'){
                        if(ti > bri){
                            if(br.prev != -1){
                                bri = br.prev.index
                                br = br.prev
                            }
                        }
                        else{
                            // console.log('here')
                            br.next = {index : ti, next : {}, prev:br, bot: parseInt(exp[ti].Opparam[1].value[1]), top:parseInt(exp[ti].Opparam[2].value[1])}
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

        let retl = pleft
        let retr = pright
        let frontstop = false
        let endstop = false
        let leftbr = this.getlastbr(pleft)
        let rightbr = this.getlastbr(pright)
        // console.log(leftbr, rightbr)
        let lretindex = leftbr.index
        let rretindex = rightbr.index
        // console.log(leftbr,rightbr)

        while(true) {

            //exit condition
            if(frontstop && endstop) break

            //trim front once
            if(!frontstop && this.Same([pleft[lefti]],[pright[righti]])){
                retl = retl.slice(1, retl.length)
                retr = retr.slice(1, retr.length)
                let prule = this.genRule('!'+this.ExpToString(retl) + '@'+this.ExpToString(retr)+ '\n')[0]
                if(this.isRule(prule)) return [retl, retr]
                lefti += 1
                righti += 1
                rretindex -=1
                lretindex -=1
                
            }else{frontstop = true }
            


            //trim back once
            if(!endstop && this.Same([pleft[leftendi]],[pright[rightendi]])){

                //we have enter end of a branch, we are in bot expression by default, if same check last top exp
                if(leftbr.index != -1 || rightbr.index != -1){
                    // console.log(' leftbr.index', leftbr.index,'leftendi', leftendi,'leftbr.top',leftbr.top,'leftbr.bot',leftbr.bot)
                    // console.log(' rightbr.index', rightbr.index,'rightendi', rightendi,'rightbr.top',rightbr.top,'rightbr.bot',rightbr.bot)
                    // console.log('retl: ',this.ExpToString(retl),leftbr, leftendi)
                    // console.log('retr: ',this.ExpToString(retr),rightbr, rightendi)
                    if((leftendi <= leftbr.index+leftbr.top+leftbr.bot)
                        && (rightendi<= rightbr.index+rightbr.top+rightbr.bot)
                            &&(leftendi >= leftbr.index+ leftbr.top)
                                &&(rightendi >= rightbr.index+ rightbr.top)
                                    &&(this.Same([pleft[leftendi]],[pright[rightendi]]))){


                                        //go to the top expression 
                                        if(this.Same([pleft[leftendi - leftbr.bot]], [pright[rightendi - rightbr.bot]])){
                                            // console.log('pass4')

                                            //splice last top expression
                                            //if we slice bot first there should be no issue with indexing, because bot exps are the last exps
                                            // console.log('-------')

                                            // console.log('beforetrim br: ',this.ExpToString(retr))
                                            if(rightendi - righti != rretindex){
                                                retr.splice(rightendi- righti, 1)
                                                // console.log('trim bot')

                                            }
                                            // console.log('trim bot end : ',this.ExpToString(retr),rightendi- righti,rretindex)


                                            if(rightendi-(rightbr.bot)- righti != rretindex){
                                                // console.log('trim top')
                                                retr.splice(rightendi-(rightbr.bot)- righti, 1)
                                            }
                                            // console.log('trim top end : ',rightendi-(rightbr.bot)- righti,this.ExpToString(retr), rightendi-(rightbr.bot)-1, rretindex)
                                            
                                            rightbr.bot -= 1
                                            rightbr.top -= 1

                                            // console.log('beforetrim br: ',this.ExpToString(retl))

                                            if(leftendi-lefti != rretindex){
                                                retl.splice(leftendi-lefti, 1)

                                            }
                                            // console.log('trim bot end : ',this.ExpToString(retl))
                                            if(leftendi-(leftbr.bot)- lefti != rretindex){

                                                retl.splice(leftendi-(leftbr.bot)-lefti, 1)
                                            }
                                            // console.log('trim top end : ',leftendi-(leftbr.bot),this.ExpToString(retl))
                                            leftbr.bot -= 1
                                            leftbr.top -= 1

                                            //fix top bot index
                                            // console.log(retr[rretindex],rretindex)

                                            // let t = toString(rightbr.top) ? toString(rightbr.top) : 0
                                            // console.log(t)

                                            // retr[rretindex].Opparam[1].value = '$'+rightbr.top.toString()
                                            // retr[rretindex].Opparam[2].value = '$'+rightbr.bot.toString()

                                            // retl[lretindex].Opparam[1].value = '$'+leftbr.top.toString()
                                            // retl[lretindex].Opparam[2].value = '$'+leftbr.bot.toString()
                                            // console.log(this.ExpToString(retl), '@'+this.ExpToString(retr))
                                            if(leftbr.bot == 0 && leftbr.top == 0 && rightbr.bot == 0 && rightbr.top == 0 )
                                            {
                                                retl.splice(retl.length-1, 1)
                                                retr.splice(retr.length-1, 1)
                                            }
                                            let prule = this.genRule('!'+this.ExpToString(retl) + '@'+this.ExpToString(retr)+ '\n')[0]

                                            if(this.isRule(prule)) {
                                                // console.log('-------')
                                                // console.log(this.RuleToString(prule))
                                                return [retl, retr]
                                            }
                                        
                                    
                                
                            }
                            leftendi -= 2
                            rightendi -= 2                       
                        }
                        //top bot dont match, dont slice
                        else{endstop = true}
                        //slice two on each expressions    
                    
                }
            
                else{
                    //trim end like usual
                    retl = retl.slice(0, retl.length-1)
                    retr = retr.slice(0, retr.length-1)
                    let prule = this.genRule('!'+this.ExpToString(retl) + '@'+this.ExpToString(retr)+ '\n')[0]
                    leftendi -= 1
                    rightendi -= 1
    
                    if(this.isRule(prule)) return [retl, retr]
                }
            }
            else{endstop = true}
        }
        
        // console.log('here')
        return [retl, retr]
    }


    //trim branch takes the last br operation found from left to right 
    //and trim top and bottom expressions individuality
    TrimBranch(parsed_newrule){
        // console.log('here: ', parse)
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

                if(longer[i].Opparam && longer[i].Opparam.value != '')
                {
                    topi = parseInt(longer[i].Opparam[1].value.slice(1))
                    boti = parseInt(longer[i].Opparam[2].value.slice(1))
                    brendi = brendi.index+topi + boti
                    bri.next = {index : i, next : {}, prev:bri , bot: boti, top:topi} 
                    bri = bri.next
                    checkbegin = true
                    
                    // console.log('opparam: ', lastbr,topi,boti)
                }
                else{
                    // console.log(this.Same(shorter[i],longer[i]), shorter[i], longer[i])
                    if(!shorter[i] || !longer[i]|| (!checkbegin && !this.Same(shorter[i],longer[i])) ){
                        // console.log('here')

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

            if(shorter[j].Opparam && shorter[j].Opparam.value != '')
            {
                topj = parseInt(shorter[j].Opparam[1].value.slice(1))
                botj = parseInt(shorter[j].Opparam[2].value.slice(1))
                brendj = brendj.index+ topj + botj
                brj.next = {index : j, next : {}, prev:brj , bot: botj, top:topj} 
                brj = brj.next
                // console.log('opparam: ', lastbr,topi,boti)
            }
            j = j + 1
        }

        //checking
        // while(j < shorter.length){
        //     if(!this.Same(shorter[j],longer[j])) return[-1,-1]
        //     j += 1
        // }

        if(bri.index == -1 || brj.index == -1) return [-1,-1]
        // console.log('ere: ',longer[bri.index].Opparam.value,longer[brj.index].Opparam.value)
        if(longer[bri.index].Opparam.value != longer[brj.index].Opparam.value) return[-1,-1]

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
            botr = shorter.slice(brj.index+topi+1, brj.index+topj+botj+1)
        }
        // console.log('branch: ', this.ExpToString(topl), topi, bri.index ,' =? ',this.ExpToString(topr), topj,brj.index)
        // console.log('branch: ', this.ExpToString(botl), boti, ' =? ',this.ExpToString(botr), botj)
        // console.log()
        let toprule = this.genRule('!'+this.ExpToString(topl)+'@'+this.ExpToString(topr)+'\n')[0]
        let botrule = this.genRule('!'+this.ExpToString(botl)+'@'+this.ExpToString(botr)+'\n')[0]
        // let rett = this.isRule(toprule) ? ( toprule.leftexps[0].operator ? toprule : -1) : -1
        // let retb = this.isRule(botrule) ? ( botrule.leftexps[0].operator ? botrule : -1) : -1
        return [toprule,botrule]
    }

    Operands_normalize(rule) {
        let operands_table = {}
        let leftexps = this.Operands_normalize_exps(rule.leftexps, operands_table)[0]
        let rightexps = this.Operands_normalize_exps(rule.rightexps, operands_table)[0]

        return {type:'Equivalence Rule', leftexps: leftexps, rightexps:rightexps}
    
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
                        let operand = ret_exp.operands[i].value
                        if(operand){
                            if(temp_table[operand] == undefined){
                                temp_table[operand] = offset 
    
                                offset += 1
                            }
                            ret_exp.operands[i].value = String(temp_table[operand])
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
            
            if(exp.Opparam && exp.Opparam.value != ''){
                ret += exp.Opparam[0].value + ' ' + exp.Opparam[1].value +  ' ' +  exp.Opparam[2].value + ' '
            }
            if(exp.operator  && exp.operator.value != ''){
                if(exp.operator.value == '@') continue
                ret += exp.operator.value + ' '
            }
            if(exp.operands && exp.operands.length > 0){
                for(const opr of exp.operands){
                    if(opr.value !== undefined) {
                        ret += opr.value + ' '
                    }
                }
            }
            if(exp.value != '')
                ret += ', '
        }
        return ret
    }

    IndIns(exps, inr, offset){
        let i = 0
        let ret = {type:"Equivalence rule", leftexps:[], rightexps:[]} 
        while (i < exps.length) {
            ret.leftexps.push(exps[i])
            ret.rightexps.push(exps[i])
            if(i == offset){
                for (const op of inr.leftexps){
                    ret.leftexps.push(op)
                }
                for (const op of inr.rightexps){
                    ret.rightexps.push(op)
                }
                
            }
            
            i += 1
        }
        return ret
    }

    AddRule(ret){
        this.allrules.push(ret)
    }

    IndComm(rA){
        let ret = {type: 'Equivalence Rule', leftexps: rA.rightexps, rightexps: rA.leftexps}
        if(ret) this.AddRule(ret)
        return ret
    }
    //add proof to all proof table if found, return false if new proof does not match input
    IndTrans(rA, rB){
        let Aleftexps = rA.leftexps
        let Arightexps = rA.rightexps
        let Bleftexps = rB.leftexps
        let Brightexps = rB.rightexps

        // console.log(rA, rB, Aleftexps, Arightexps ,Bleftexps, Brightexps)
        if(this.Same(Aleftexps, Bleftexps))
        {
            if(this.Same(Arightexps,Brightexps)){
                return [true, null]
            }
            else {
                ret = {type :'Equivalence Rule', leftexps : Arightexps, rightexps: Brightexps}
            }
        }else if(this.Same(Aleftexps, Brightexps)){
            if(this.Same(Arightexps, Bleftexps)){
                return [true, null]
            }
            else {
                ret = {type :'Equivalence Rule', leftexps : Arightexps, rightexps: Bleftexps} 
            }
        }
        else if(this.Same(Arightexps, Bleftexps)){
            if(this.Same(Aleftexps,Brightexps)){
                return [true, null]
            }
            else {
                ret = {type :'Equivalence Rule', leftexps : Aleftexps, rightexps: Brightexps}
            }
        }else if(this.Same(Arightexps, Brightexps)){
            if(this.Same(Aleftexps, Bleftexps)){
                return [true, null]
            }
            else {
                ret = {type :'Equivalence Rule', leftexps : Aleftexps, rightexps: Bleftexps}
            }
        }

        if(!ret) {
            return [false, null]
        }
   
        else {
            this.AddRule(ret)
            return [true, ret]
        }
    }

    checkcv(l,r,rl,rr){
        let left=l
        let right = r
        let rleft = rl
        let rright = rr
        let cvtable = {}
        // console.log(this.ExpToString(rright))
        // console.log(this.ExpToString(rleft),this.ExpToString(rright))

        //check if expressions contain code variables
        
        let i = 0
        let found = false 
        let temp
        let ti = 0
        let retl= []
        while (i < rleft.length){
            let t1 = rleft[i]
            let t2 = left[i]
            if(t1.operator){
                if (t1.operator.value == '#15' ){
                    // console.log(rl,rr)
                    if(!cvtable[t1.operands[ti].value]){
                        cvtable[t1.operands[ti].value] = []
                        temp = t1.operands[ti].value
                    }
                    else{
                        ti += 1
                    }
                    found = true 
                    i += 1
                    
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
                let t2 = left[j]
                while(j < left.length ){
                    t2 = left[j]
                    // console.log(t1,t2)

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
        // console.log(this.ExpToString(retl))
        if(Object.keys(cvtable).length == 0) {
            // console.log('back')
            return false
        }
        // console.log(cvtable)
        // for(var v in cvtable){
        //     if (cvtable[v].length == 0) return false
        // }

        let x = 0
        let retr =[]
        while(x < rright.length){
            
            let t1 = rright[x]
            // console.log(t1)

            if(t1.operator){
                if(t1.operator.value =='#15')
                {
                    // console.log(t1)
                    if(cvtable[t1.operands[0].value]){
                        // console.log(cvtable[t1.operands[0].value])
                        for(const e of cvtable[t1.operands[0].value]){
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
        // console.log(this.ExpToString(left),this.ExpToString(right))
        // console.log(this.ExpToString(rleft),this.ExpToString(rright))
        // console.log(this.ExpToString(right),this.ExpToString(retr))
        if(this.Same(right,retr)) {
            // console.log(this.ExpToString(right), '|',this.ExpToString(retr))
            return true 
        }
        return false
    }

    //isRule checks if rule exist or its commutative form exists in the rule table
    //code variables
    isRule(relation){
        // console.log('relation: ', this.RuleToString(relation))
        let left = relation.leftexps
        let right = relation.rightexps
        // console.log(left, right)


        let i = 0
        for(const rule of this.allrules){


            let rleft = rule.leftexps
            let rright = rule.rightexps
            if(this.checkcv(left,right, rleft,rright)) return true
            if(this.checkcv(left,right, rright,rleft)) return true
            if(this.checkcv(right,left, rleft,rright)) return true
            if(this.checkcv(right,left, rright,rleft)) return true

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
            // console.log('match: ', this.RuleToString(relation), 'not applicable: ', this.RuleToString(rule), 'oprequiv: ', this.OperatorEquivalence(relation,rule), 'oprndsequiv: ', this.OperandEquivalence(relation,rule))
            if(this.OperatorEquivalence(relation,rule) && this.OperandEquivalence(relation,rule)){
                return true
            }

            i += 1
        }       
        
        return false 
    }

    OperatorEquivalence(srcstatement, tarstatement){
        let srctablel = []
        let srctabler = []

        for (const e of srcstatement.leftexps){
            // console.log(e)
            if(e.operator){
                if(e.Opparam){
                    if(e.Opparam.value != '')
                        {
                        for(const v of e.Opparam){
                            srctablel.push(v)
                        }
                    }
                }
                srctablel.push(e.operator.value)

            }
        }
        for (const e of srcstatement.rightexps){
            if(e.operator){
                if(e.Opparam){
                    if(e.Opparam.value != '')
                    {
                        for(const v of e.Opparam){
                            srctablel.push(v)
                        }
                    }
                }
                srctabler.push(e.operator.value)

            }
        }

        let tartablel = []
        let tartabler = []

        for (const e of tarstatement.leftexps){
            if(e.operator){
                if(e.Opparam){
                    if(e.Opparam.value != '')
                        {
                        for(const v of e.Opparam){
                            srctablel.push(v)
                        }
                    }
                }
                tartablel.push(e.operator.value)

            }
        }
        for (const e of tarstatement.rightexps){
            if(e.operator){
                if(e.Opparam){
                    if(e.Opparam.value != '')
                        {
                        for(const v of e.Opparam){
                            srctablel.push(v)
                        }
                    }
                }
                tartabler.push(e.operator.value)

            }
        }
        //checking

        if(tartablel.length != srctablel.length && tartablel.length != srctabler.length ) return false
        if(tartabler.length != srctablel.length && tartabler.length != srctabler.length ) return false

        if(!(this.listequal(srctablel,tartablel) && this.listequal(srctabler,tartabler)) && !(this.listequal(srctabler,tartablel) && this.listequal(srctablel,tartabler))) return false

        // console.log(srctablel,'@',srctabler,'|', tartablel,'@',tartabler)
        return true
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
    OperandEquivalence(srcstatement, tarstatement){
        let srctable = []
        for (const e of srcstatement.leftexps){
            if(e.operands){
                for(const opr of e.operands) {
                    srctable.push(opr.value)
                }
            }
        }
        for (const e of srcstatement.rightexps){
            if(e.operands){
                for(const opr of e.operands) {
                    srctable.push(opr.value)
                }
            }
        }

        let tartable = []
        for (const e of tarstatement.leftexps){
            if(e.operands){
                for(const opr of e.operands) {
                    tartable.push(opr.value)
                }
            }
        }
        for (const e of tarstatement.rightexps){
            if(e.operands){
                for(const opr of e.operands) {
                    tartable.push(opr.value)
                }
            }
        }

        // console.log(srctable,tartable)
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
                if(!src[i].operator|| !tar[i].operator) {
                    if(src[i].value){
                        if(tar[i].value){
                            return src.value == tar[i].value
                        }
                    }
                    return false
                }
                if(src[i].operator && tar[i].operator){
                    if(src[i].operator.value != tar[i].operator.value) {
                        // console.log(src[i].operator,tar[i].operator)
                        //code variable
                        return false }
                }
                //check if Opparam match
                if(src[i].Opparam || tar[i].Opparam){
                    if(!src[i].Opparam || !tar[i].Opparam) return false 

                    if(src[i].Opparam.value == '' || src[i].Opparam.value == ''){
                        if(src[i].Opparam.value != '' || src[i].Opparam.value != '')
                            return false
                    }
                    
                    if(src[i].Opparam[0]){
                        if(tar[i].Opparam[0]){
                            if(src[i].Opparam[0].value != tar[i].Opparam[0].value) return false
                        }
                    }

                }
                //edge case when exp has no type 
                if(src[i].type || tar[i].type)
                {
                    if(!src[i].type || !tar[i].type) return false
                }
                
                //check operands match
                if(src[i].operands){
                    let j = 0
                    if(tar[i].operands.length != src[i].operands.length) return false
                    // console.log(tar[i].operands, src[j].operands)
                    while(j < src[i].operands.length){
                        if(src[i].operands[j].value != tar[i].operands[j].value){
                            
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
}

export default ProofAssistant