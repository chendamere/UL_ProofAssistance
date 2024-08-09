



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

    Proving(start, end) {
        let prev = this.ExpToString(start)
        let maxStep = 100
        let count = 0
        let input = ''
        let parsed_newrule = {rightexps:[]} 
        let ProofComplete = false

        let ret = 0
        //try all exps
        while(!this.Same(parsed_newrule.rightexps, end) & count < maxStep){
            // console.log('next: ', this.RuleToString(parsed_newrule))

            console.log('----------------------')
            let matchExp = false
            let proof_inc = ret
            ret += 1

            
            //convert current expression operand order to match the end expression
            console.log('next: ', this.ExpToString(parsed_newrule.rightexps))

            if(this.try_match_operand_order(parsed_newrule)){
                console.log('done: ', this.RuleToString(parsed_newrule))
                return true
            }
            

            if(ProofComplete){
                return true
            }

            // console.log('next: ', this.ExpToString(parsed_newrule.rightexps))


            //search for proofs
            let foundExp = false
            // console.log(this.Exps.length)
            while(proof_inc < this.Exps.length)
            {
                let Exp = this.Exps[proof_inc]

                //loop through all similar expressions
                let relatedExps = this.Generate_sim_exps(Exp)
                proof_inc += 1

                console.log(relatedExps, Exp)

                let ri = 0
                if(foundExp) {
                    console.log('6')

                    break
                }
                while(ri < relatedExps.length) {
                    let exp = relatedExps[ri]

                    // console.log(exp)
                    if(matchExp) {
                        console.log('4')

                        foundExp = true
                        break
                    }

                    if(this.Same(parsed_newrule.rightexps, end)){
                        foundExp = true
                        console.log('5')

                        break
                    }

                    input = exp
                    // console.log(input)
                    let newrule = '! ' + prev + ' @ ' + input + '\n'
                    // console.log(newrule, proof_inc, this.MoreExps.length, input)


                    parsed_newrule = this.genRule(newrule)[0]

                    console.log(this.RuleToString(parsed_newrule))

                    //done
                    if(this.Same(parsed_newrule.leftexps, parsed_newrule.rightexps) && this.Same(parsed_newrule.leftexps, end)){
                        if(this.Same(parsed_newrule.rightexps, end)){
                            console.log('end')
                            ProofComplete = true
                            foundExp = true

                            break
                        }
                        else{
                            console.log('skip used exps: ', prev)
                            ri += 1
                            continue
                        }
                    }

                    // console.log('first try: ', this.RuleToString(parsed_newrule))

                    if(this.isRule(parsed_newrule)){
                        prev = input
                        console.log('1')
                        foundExp = true

                        break
                    }

                    if(this.trim_and_check(parsed_newrule)){
                        prev = input
                        foundExp = true
                        console.log('2')

                        break
                        
                    }
                    else{


                        let max = this.getmax(parsed_newrule.leftexps)
                        let opcounter = 0
                        let found_next = false
                        //try different operands
                        while(opcounter < max){
                            opcounter += 1
                            let tempexp = this.ExpToString(this.incOperands((parsed_newrule.rightexps)))
                            let tr = '! ' + prev + ' @ ' + tempexp + '\n'
                            let parsed_tr = this.genRule(tr)[0]
                            // console.log('incr operands: ', this.RuleToString(parsed_tr))
                            if(this.Same(parsed_tr.leftexps, parsed_tr.rightexps) && this.Same(parsed_tr.leftexps, end)){
                                console.log('done: ', this.RuleToString(parsed_newrule))

                                return true
                            }
                            
                            if( this.Same(parsed_tr.left, parsed_tr.right) && ! this.Same(parsed_trimrule, end)) {
                                ri += 1
                                console.log('7')

                                continue
                            }
                            // console.log('try: ', this.RuleToString(parsed_tr))

                            //trim
                            if(this.trim_and_check(parsed_tr)){
                                prev = tempexp
                                parsed_newrule = parsed_tr
                                console.log('valid construction: ', this.RuleToString(parsed_newrule))
                                found_next = true
                                foundExp = true

                                break
                            }
                        }
                        if(found_next){
                            // console.log(found_next)
                            foundExp = true
                            console.log('8')

                            break
                        }
                    }

                    ri += 1
                }
            }
            console.log('outer loop')
            count += 1
            
        }


        
        if(count > maxStep) console.log('reached max step!')
        else{
            console.log('-----------')
            console.log('proof complete!')
        }
        return true
    }

    //right matching left
    try_match_operand_order(parsed_newrule) {

        // if(!parsed_newrule) return false
        let tar = parsed_newrule.rightexps
        let src = parsed_newrule.leftexps
        if(!tar || !src) return false

        let endmax = this.getmax(tar)
        let endmaxcounter= 0

        while(endmaxcounter < endmax){
            if(tar.length == 0) break

            let target = this.ExpToString(this.incOperands(tar))

            let tr = '! ' + this.ExpToString(src) + ' @ ' + target + '\n'
            let parsed_tr = this.genRule(tr)[0]

            // console.log('t:  ',parsed_tr)

            // console.log('incr operands: ', this.RuleToString(parsed_tr))
            if(this.Same(parsed_tr.leftexps, parsed_tr.rightexps)){
                
                return true
            }
            
            endmaxcounter += 1
        }

        return false
    }

    trim_and_check(parsed_newrule) {
        //trimming will allow any rule that have same left and right to return true
        let [trimLong, trimShort] = this.Trim(parsed_newrule)
        let trimrule = '! ' + this.ExpToString(trimShort) + ' @ ' + this.ExpToString(trimLong) + '\n'
        let parsed_trimrule = this.Operands_normalize(this.genRule(trimrule)[0])

        if(this.isRule(parsed_trimrule) ) {            
            return true  
        }
        return false
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

    InteractiveProving(start, end) {
        let prompt = require("prompt-sync")({ sigint: true });
        let prev = this.ExpToString(start)
        let maxStep = 1000
        let count = 0
        let input = ''
        let parsed_newrule = {rightexps:[]} 
        while(!this.Same(parsed_newrule.rightexps, end) && (count < maxStep))
        {
            input = prompt("enter a expression: ");

            let newrule = '! ' + prev + ' @ ' + input + '\n'
            parsed_newrule = this.genRule(newrule)[0]

            //trim
            let [trimLong, trimShort] = this.Trim(parsed_newrule)
            let trimrule = '! ' + this.ExpToString(trimShort) + ' @ ' + this.ExpToString(trimLong) + '\n'
            let parsed_trimrule = this.Operands_normalize(this.genRule(trimrule)[0])

            // console.log('parsed_trimrule: ', parsed_trimrule)
            console.log('string_trimrule: ', this.RuleToString(parsed_trimrule) )

            if(!this.isRule(parsed_trimrule)) {
                console.log("not in database: ", this.RuleToString(parsed_trimrule))
            }
            prev = input
            console.log('newrule: ', this.RuleToString(parsed_newrule))
            count += 1
        }
        console.log('proof complete!')
        if(count> maxStep) console.log('reached max step!')
        return true
    }


    //return the longest string that is different and between two strings
    //same thing as maximizing the length of left and right 

    Trim(parsed_newrule) {
        //old exps
        let pleft = parsed_newrule.leftexps

        //new exps
        let pright = parsed_newrule.rightexps

        let longer = pleft 
        let shorter = pright 
        if(shorter.length > longer.length){
            shorter = pleft 
            longer = pright
        }

        let i = longer.length - 1
        let j = shorter.length - 1
        // console.log(shorter)
        while(i > 0 && j >= 0){
            
            if(this.Same([longer[i]], [shorter[j]] )){
                i = i - 1
                if(j > 0)
                    j = j - 1
            }
            else{
                break
            }
        }

        //edge case for evaluating when i=0

        let endi = i + 1

        //edge case when end
        let endj = j + 1
        i = 0
        j = 0

        while(i < endi && j < endj) {
            if(this.Same([longer[i]],[shorter[j]])){

                i = i + 1
                j = j + 1
            }
            else{
                break
            }
        }

        //edge case
        if(j == 0 && endj == 1) endj = 0

        let trimLong = longer.slice(i, endi)
        let trimShort = shorter.slice(j, endj)
        if(trimLong.length == 0) trimLong = [{value:''}]
        if(trimShort.length == 0) trimShort = [{value:''}]


        return [trimLong, trimShort]
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

                        if(temp_table[operand] == undefined){
                            temp_table[operand] = offset 

                            offset += 1
                        }
                        ret_exp.operands[i].value = String(temp_table[operand])
                        operands.push(ret_exp.operands[i])
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

    ExpToString(rule) {
        let ret = ', '
        if(!rule) return ret
        for (const exp of rule){
            
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

    //isRule checks if rule exist or its commutative form exists in the rule table
    isRule(relation){

        let left = relation.leftexps
        let right = relation.rightexps
        // console.log(left, right)


        let i = 0
        for(const rule of this.allrules){

            let rleft = rule.leftexps
            let rright = rule.rightexps
            // console.log('rleft: ', rleft, 'left: ', left)
            // console.log('rright:', rright, 'right: ', right)
            //lengths dont match, next rule
            if(left.length != rleft.length && left.length != rright.length) continue
            if(right.length != rright.length && right.length != rleft.length) continue
            
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
                if(src[i].operator && tar[i].operator){
                    if(src[i].operator.value != tar[i].operator.value) {
                        // console.log(src[i].operator,tar[i].operator)
                        
                        return false }
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