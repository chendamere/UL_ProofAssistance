class Parser {
    constructor() {
        this.variables = {};
        this.tokens = {}
        this.endc = [' ', ',', '(', ')', '{', '}']
        this.branch =[]
        this.tokeni = 0
        this.unaryOperators = []
        this.binaryOperators = []
        this.cv = ''
        this.tv = ''
    }


    Parse(expression) {
        const tokens = expression.split(',').filter(token => token !== ' ');
        let exps = []
        let rule = {leftexps:[], rightexps:[]}

        for (let token of tokens) {
            
            let pexp =  {operator:'', operands: [], Opparam: []}
            let exp = token.trim()

            if(exp =='!' || exp == '')continue
            if(exp == '@'){
                if(exps.length == 0){
                    rule.leftexps = [{operator:'#0'}]
                    exps = []
                }
                else{
                    rule.leftexps = exps
                    exps = []
                    // console.log('exp', exp)
                }          
                continue
            }

            let operands = []
            let Opparam =[]
            let i =0
            let operator = ''
            while(exp[i]){
                if(exp[i]==' ') {i +=1; continue}

                if(exp[i] == '$'){
                    Opparam.push(exp[i] + exp[i+1])
                    i += 2
                    continue
                }
                //look for operator
                if(exp[i] == '#'){
                    while(exp[i] && !this.GetEndc().includes(exp[i])){
                        operator += exp[i]
                        i += 1
                    }

                    //check if its branch
                    if(this.GetBranch().includes(operator)){
                        Opparam.push(operator)
                        operator = ''
                    }                 
                }
                else if(!isNaN(exp[i])){
                    operands.push(exp[i])
                }
                i += 1
            }
            // console.log(operator,operands)
            pexp.operator = operator
            pexp.operands = operands
            pexp.Opparam = Opparam
            // console.log(pexp, operands,operator)
            exps.push(pexp)
            // console.log(exps)
        }
        if(exps.length == 0) exps = [{operator:'#0'}]
        rule.rightexps = exps
        return rule
    }
    GetEndc(){
        return this.endc
    }
    GetBranch(){
        return this.branch
    }
}

class LatexParser extends Parser {

    ParseFile = (folder, Filereader, file, flag) => {
        const source = Filereader(folder + '/'+file, {encoding: "utf8"})
        //parse characters into array of lines
        let lines = []
        let line = ''
        for(const char of source){
            if(char === '\n'){
                if(line.length > 1){lines.push(line)}
                line = ''
            }
            else{line += char}
        }
        // console.log(lines)
        let ret
        if(!flag){
            ret = this.Parse_rules_and_titles(lines)
        }else{
            ret = this.Parse_exps(lines)
        }
        // console.log(chapter)
        return ret
    }
    trimExps = (exps) => {
        let ret = []
        for (const expss of exps) {
            let l1 =[]
            for (const c of expss) {
                let pcode = c.slice(2,c.length)
                l1.push(pcode)
            }            
            ret.push(l1)
        }
    
        return ret;
    }
    Parse_rules_and_titles = (lines) => {
        //extract title and rules
        let all_rules = []
        let title = ''
        let nline;
        let rule = '';
        let parse = true
    
        for (const line of lines){
            
            if(line.includes('\\Ri')) continue
            if(line.includes('\\begin{math}')) {parse = false 
                continue
            }
            if(line.includes('\\end{math}'))   {parse = true 
                continue
            }
            
    
            //ignore %
            if(line.includes("%")){
                continue 
            }
    
            //get title 
            if(!title){
                title = this.extract(line,'\\chapter{','}')
                continue;
            }
    
            if(!parse) continue;
    
            //line in the file 
            nline = this.LineNormalize(line,false)
            if(nline.trim() == '') continue
    
            //normalize rule
            
            rule = this.RuleNormalize(nline)
            
            if(rule.trim() == '')
            {
                continue
            } 
    
            if(rule) {
                //if last line ends with \\Rq then join last rule with current rule
                if((!rule.includes('@'))) {     
                }
                else if(rule[rule.length-1] !== ','){
                    throw new Error('invalid string to rule format')
                }
                else{
                    all_rules.push(rule)
                }
            }
        }
    
        return {title: title , rules : all_rules}
    }

    Parse_exps= (lines) => {
        //extract title and rules
        let all_exps = []
        let nline;

        let r = false
        let exps = []
        let parse = false
    
        for (const line of lines){
            
            // console.log(line,r)

            if(line.includes('\\Ri')) continue


            if(line.includes('\\begin{math}')) {parse = true;
                r=false
                continue
            }
            if(line.includes('\\end{math}')) {
                parse = false;
                all_exps.push(exps)
                exps=[]
                r=false
                continue
            }

            if(line.includes('\[') && r){
                all_exps.push([])
                exps=[]
                continue
            }

            if(line.includes('\[')){
                r=true
                // console.log('here', r)
                continue
            }

            //ignore %
            if(line.includes("%")){
                continue 
            }

            if(!parse) continue;

            if(line.includes('\[') && r){
                all_exps.push([])
            }
            //line in the file 
            nline = this.LineNormalize(line,true)
            if(nline.trim() == '')
            {
                continue
            }
    
            //normalize rule
            let exp = this.expsNormalize(nline)

            if(exp.trim() == '') continue
            else{
                //if last line ends with \\Rq then join last rule with current rule
                if((!exp.includes('@'))) {     
                }
                else if(exp[exp.length-1] !== ','){
    
                }
                else{
                    exps.push(exp)
                }
            }
        }
        if(all_exps[all_exps.length-1].length==0) all_exps.push([])
        return all_exps
    }
    LineNormalize = (line, flag) => {
        let nline = line.trim()
    
        nline = this.simp_branch_expressions(nline)
        nline = this.Convert_operators(nline)
        nline = nline.trim()
        if(!flag){nline = this.extract(nline,'\\[','\\]')}
        
        nline = this.Add_comma_to_open_branch(nline)
        return nline
    }
    //second order normalize
    RuleNormalize = (line) => {
        let ret = line 
        // console.log('0',ret)
        ret = this.Convert_branch_expressions(ret)
        // console.log('1',ret)
        ret = this.Reorder_operations(ret)
        // console.log('2',ret)
        ret = this.Operands_numbering(ret)
        // console.log('3',ret)

        ret = '!' + ret.trim()

        return ret
    }
    expsNormalize = (line) => {
        let ret = line
        
        if(!ret.includes('@')){
            return '' 
        }
        else if(ret.trim()[0] == '@'){
            ret = ret.replace('@', '')
        }
        ret = this.Convert_branch_expressions(ret)
        ret = this.Reorder_operations(ret).trim()
        ret = this.Operands_numbering(ret)
        ret = ret.trim()
        return ret
    }
    //Operation, Operands and Operators
    extract = (line,begin,end) => {
        //trim beginning and end white spaces
        let detect = ''
        let found = false
        let endLine = 0
        let startLine = 0
        while(endLine < line.length) {
            detect += line[endLine]
            if (detect.includes(begin) && !found) {
                startLine = endLine
                found = true
            }

            if(found && detect.includes(end)){
                detect = detect.slice(startLine + 1, endLine - (end.length) + 1)
                return detect.trimEnd()
            }
            endLine += 1
        }

        // throw new Error("error in extracting from latex line ")
        return '';
    }

    Operands_numbering = (line) => {

        //look for char and & start
        const start = /[a-zA-Z&]/;
        let opr = ''
        let operand = {}
        let order = 1
        let i = 0
        let ret = line
        while(i<line.length) {

            //go to next delimeter if these character
            if(line[i] == '#' || line [i] == '@' || line[i] == '!' || line[i] == ','){
                i += 1
                while((line[i] != ' ' && line[i] != ',' && line[i] != '}' && line[i] != '{' ) && i < line.length-1){
                    i += 1
                }
                
            }

            //match start
            if (line[i].match(start)){
                while((line[i] != ' ' && line[i] != ',' && line[i] != '}' && line[i] != '{' && line[i] != '#' && line [i] != '@') && i < line.length-1){
                    opr += line[i]
                    i += 1
                }
            }

            //assign ordering to opr
            if(opr.trim() != '') {
                if(!operand[opr] && operand[opr] != 0){
                    operand[opr] = order
                    order += 1
                }
                opr = ''
            }

            i += 1
            
        }
        if(opr.trim() != '') {
            if(!operand[opr]){}
                operand[opr] = order
            order += 1
            opr = ''
        }

        //order the table from longest to shortest string to replace

        let srcoprlist = []
        for(const a of Object.keys(operand)){
            srcoprlist.push(a)
        }
        srcoprlist.sort((a, b) => b.length - a.length);

        for(const a of srcoprlist){
            ret = ret.replaceAll(a, operand[a])
        }
        return ret 
    }

    Reorder_operations = (line) => {

        let ret = ','
        let c = ''
        let operation = ''
        let i = 0
        let replace = ''
        // console.log('l',line)
        while(i < line.length){
            c = line[i]

            if(c == ',' || c == '{' || c  == '}'){

                replace = this.Reorder(operation, line.slice(i))
                if (replace.trim() != '') {
                    // console.log('replace: ', replace, 'operation: ', operation)

                    i+=1
                    ret += replace + ','
                    for(const br of this.branch){
                        if(replace.includes(br) && br != '#102'){
                            while(line[i] != '}') i+=1
                            break
                        }
                    }
                    operation = ''
                    continue;
                }     
            }
            else{
                operation += c 
            }
            i+=1

        }
        // console.log('r',ret)
        return ret.trim()
    }

    Reorder = (operation, rest) => {

        // if (operation.includes('j_1')) console.log( operation, rest)
        if (operation.trim() == '') return ''


        let operators = this.FindOperators( operation, rest).trim()
        let operands = this.FindOperands(operation, rest).trim()

        let ret = ''
        
        if(operands != ''){
            ret = operators + ' ' + operands 
        }
        else {
            ret = operators
        }

        if(ret.trim() === '') return operators
        else return ret.trim()
    }

    FindOperands = (operation, rest) => {
        if(operation.trim().includes('@'))
            return ''

        let ret = ''
        let operand = ''
        let i = 0
        let found = false
        for(const br of this.branch){
            if(operation.includes(br) && operation.includes('\\Brs')){
                while(i < rest.length && rest[i] != '}'){  
                    if(!found && (rest[i] == '&' || rest[i].toLowerCase().match(/[a-z]/i))){
                        found = true
                    }
                    if(found) {
                        operand += rest[i]
                    
                        if(rest[i] == '#' || rest[i] == ' '){
                            if(operand != ''){
                                found = false 
                                ret += operand.trim() + ' '
                                operand = ''
                            }
                        }
                    }
                    i+= 1
                }
                if(operand != ''){
                    ret += operand.trim()
                }
                break
            }
        }
        //no br
        if(!found){
            while(i < operation.length){
                //skip operators
                if(operation[i] == '#'){
                    if(operand.trim() != ''){
                        ret += ' ' + operand
                        operand = ''
                    }
                    while(operation[i] != ' ' && (i < operation.length)){
                        i += 1 
                    }
                }
    
                //add until white space 
                if(operation[i] != ' ' && i < operation.length){        
                    operand += operation[i]
                }
                else{
                    if(operand.trim() != ''){
                        ret += operand + ' '
                        operand = ''
                    }
                }
    
                i+=1
            }
        
            // edge cases
            if(operand.trim() != ''){
                ret += operand + ' '
                operand = ''
            }
        }
        return ret.trim()
    }

    FindOperators = (operation, rest) => {
        if(operation.trim().includes('@'))
            return operation

        let ret = ''
        let i = 0
        let operator = ''
        let Broperator = ''
        let found = false
        while (i < operation.length) {
            if (operation[i] == '#' ){
                operator += operation[i]
                i += 1 
                found = true
                continue
            }

            if(found && operation[i] == ' ')
            {
                break
            }
            if(found)
            {
                operator += operation[i]
            }
            i+=1
        }

        //branch operators
        //if #12 or #13 then look for optional additional operator
        if(this.branch.includes(operator)) {
            Broperator = operator
            operator = ''
        }

        let j = 0 

        if(Broperator != '')
        {
            found = false
            //find the first operation 
            if(Broperator != '#102'){
                while (j < rest.length) {
                    if (rest[j] == '#'){
                        operator += rest[j]
                        j += 1 
                        found = true
                        continue
                    }
            
                    if(rest[j] == '}' || (found && rest[j] == ' '))
                    {            
                        break
                    }
                    if(found){
                        operator += rest[j]
    
                    }
                    j += 1
            
                }
                while (j < rest.length-1 && rest[j] != '}'){
                    j += 1
                }
                j += 1
            }

            //get number of operations before the first two } 
            let topInt = 0 
            let botInt = 0
            let Switch = false
            // console.log('rest: ', rest,rest[j])
            while (j < rest.length){
                if(rest[j] == '}')
                {
                    if (Switch){
                        break
                    }
                    Switch = true
                }
                if(rest[j] == ','){
                    if(Switch===false){
                        topInt += 1
                    }
                    else{
                        botInt += 1
                    }
                }
                j += 1
            }
            ret = Broperator + ' $' + String(topInt - 1) + ' $' + String(botInt - 1) 
            if(operator != '')
            {
                ret += ' ' + operator
            }

        }
        else {
            ret = operator
        }

        if(!ret) console.log('operation: ', operation)
                

        return ret.trim()

    }


    AddBr(ret,src){
        let tok = '#'+this.tokeni.toString()
        this.branch.indexOf(tok) === -1 ? this.branch.push(tok) : -1
        return this.AddToken(ret, src)
    }
    AddUnary(ret,src){
        let tok = '#'+this.tokeni.toString()
        this.unaryOperators.indexOf(tok) === -1 ? this.unaryOperators.push(tok) : -1
        return this.AddToken(ret, src)
    }
    AddBin(ret,src){
        let tok = '#'+this.tokeni.toString()
        this.binaryOperators.indexOf(tok) === -1 ? this.binaryOperators.push(tok) : -1
        return this.AddToken(ret, src)
    }
    AddToken(ret, src){
        // console.log('#'+this.tokeni.toString())
        let x = ret.replaceAll(src, '#'+this.tokeni.toString())
        this.tokeni += 1
        return x
    }
    Convert_operators = (line) =>  {
        let ret = line
        this.tokeni = 1

        //longer name are replaced first

        //hardcode replace 
        ret = ret.replaceAll ('_{10}'  , '10' )
        ret = ret.replaceAll ('_{20}'  , '20' )

        ret = this.AddUnary(ret,'\\Og')
        ret = this.AddUnary(ret,'\\Ot')
        ret = this.AddUnary(ret,'\\On')
        ret = this.AddUnary(ret,'\\Op')
        ret = this.AddUnary(ret,'\\Os')
        ret = this.AddBin(ret,'\\Oc')
        ret = this.AddBin(ret,'\\Od')
        ret = this.AddBin(ret,'\\Ob')
        ret = this.AddBin(ret,'\\Oa')
        ret = this.AddBin(ret,'\\Oe')
        ret = this.AddToken(ret,'\\Or')

        ret = this.AddBin(ret,'\\Ps')

        // 
        this.cv = '#'+this.tokeni
        ret = this.AddUnary(ret,'\\Tc')
        this.tv = '#'+this.tokeni

        ret = this.AddUnary(ret,'\\Tt')

        ret = this.AddBin(ret,'\\Pe')
        ret = this.AddBin(ret,'\\Pp')

        ret = this.AddBin(ret,'\\Pu' )
        
        ret = this.AddUnary(ret,'\\Pn' )
        ret = this.AddBin(ret,'\\Pc' )
        ret = this.AddBin(ret,'\\Pb' )

        ret = ret.replaceAll('\\It', '&It')

        ret = this.AddUnary (ret,'&Fam' )
        ret = this.AddUnary (ret,'Rd_i')
        ret = this.AddUnary (ret,'Rd_j'  )
        ret = this.AddUnary (ret,'Rcpo' )

        ret = this.AddToken (ret,'IsCpo'  )
        ret = this.AddToken (ret,'IsCpm' )
        ret = this.AddToken (ret,'Rcpm'  )

        ret = this.AddToken (ret,'Ins')
        ret = this.AddToken (ret,'Del')
        ret = this.AddToken (ret,'&Tm')
        ret = this.AddToken (ret,'Cpo')
        ret = ret.replaceAll('\\Ip', '&Ip')
        ret = this.AddToken(ret,'In')
        ret = ret.replaceAll('\\&In', '&In')

        ret = this.AddBin(ret,'\\nPnm')
        ret = this.AddToken (ret,'\\nPdx')
        ret = this.AddBin(ret,'\\nPne')
        ret = this.AddBin(ret,'\\nPnl')

        ret = this.AddBin(ret,'\\Pnl')
        ret = this.AddBin(ret,'\\Pne')
        ret = this.AddBin(ret,'\\nPb')
        ret = this.AddBin(ret,'\\nPp')
        ret = this.AddBin(ret,'\\nPn')
        ret = this.AddBin(ret,'\\nPe')

        ret = this.AddToken(ret,'\\nPu')
        ret = this.AddToken(ret,'\\nPs')
        ret = this.AddToken(ret,'\\nPc')
        ret = this.AddToken(ret,'\\Pnm')
        ret = this.AddToken (ret,'\\sim' )
        ret = this.AddToken (ret,'\\Pdx' ) 
        ret = this.AddToken (ret,'Pdx') 

        ret = ret.replaceAll ('!Pdx' , 'nPdx' ) 
        ret = this.AddBin (ret,'+'  )
        ret = this.AddBin (ret,'-'  )
        ret = this.AddBin (ret,'\\times')


        ret = this.AddToken (ret,'\\Ri' )
        
        ret = this.AddToken (ret,'Rd'  )
        ret = this.AddToken (ret,'Rc'  )

        ret = this.Convert_equiv(ret)
        ret = this.AddToken (ret,'R\\_'  )
        ret = this.AddToken (ret,'R'  )
        
        ret = ret.replaceAll (')'  ,' ' )
        ret = ret.replaceAll ('('  ,' ' )
        ret = ret.replaceAll (':'  , ' ' )
        ret = ret.replaceAll (';'  , ' ' )

        return ret
    }

    // -- !
    Convert_equiv = (line) => {
        let ret = line.replaceAll('\\Rq', '@')
        return ret
    }
    //branch
    Add_comma_to_open_branch = (line) =>{
        if(!line) return line
        let i = line.length-1;
        let found = false
        let check =''
        let ret = ''
        let c = ''

        if(line[i] == '}'){
            ret = ret + ','
        }

        while(i >= 0){
            c = line[i]
            
            check = c + check
            ret = c + ret

            if(check.includes('\\Rq')&& !found){
                found = true
                check = ''
                i -= 1
                continue
            }
            if(found){
                if(c ==','){
                    found = false
                }
                if(c !=' ' && c != ',' && c == '}'){
                    ret = '},' + ret.slice(2, ret.length)
                    found = false 
                }
            }
            i -= 1
        }

        if(ret.trim()[0] !== ',') {
            ret = ',' + ret
        }
        i = ret.length-1
        found = false
        check = ''
        let s = ''
        while(i >= 0){
            c = ret[i]
            check = c + check
            s = c + s
            if(check.includes('\\Brs')&&!found){
                found = true
                i -= 1
                check = ''
                continue
            }
            if(found){
                if(c != ' ' && c != ',' && c){
                    s = s.slice(1,s.length)
                    i += 1
                    s = ',' + s
                    found = false
                }

            }
            
            i -= 1
        }
        
        return s
    } 
    simp_branch_expressions = (line) => {
        //return string
        let ret = line      
        ret = ret.replaceAll('if(', '')
        ret = ret.replaceAll(')}', '}')

        return ret
    }
    Convert_branch_expressions = (line) => {
        //return string
        let ret = line 
        this.tokeni = 100     
        ret = this.AddBr(ret,'\\Bs')
        this.tokeni -=1
        ret = this.AddBr(ret,'\\Bb')

        ret = this.AddBr(ret,'\\Blb')
        this.tokeni -=1
        ret = this.AddBr(ret,'\\Bls')


        ret = ret.replaceAll('\\Brs', '\\Br')
        ret = this.AddBr(ret,'\\Br')
        this.tokeni -=1
        ret = this.AddBr(ret,'\\Brb')

        this.tokeni =1

        // console.log('2', ret)
        return ret
    }
}

export default LatexParser