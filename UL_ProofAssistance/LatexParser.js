class Parser {
    constructor() {
        this.variables = {};
        this.tokens = {}
        this.endc = [' ', ',', '(', ')', '{', '}']
        this.branch = ['#12', '#13']
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
        ret = this.Convert_branch_expressions(ret)
        ret = this.Reorder_operations(ret)
        ret = this.Operands_numbering(ret)
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
        while(i < line.length){
            c = line[i]
            if(c != ',' && c!= '{' && c != '}') {
                operation += c 
            }
            else if(c == ',' || c == '{' || c  == '}'){

                replace = this.Reorder( operation, line.slice(i))
                
                if (replace.trim() != '') {
                    i+=1
                    ret += replace + ','
                    if(replace.includes('#13') || replace.includes('#12')){
                        while(line[i] != '}') i+=1
                    }
                    
                    operation = ''
                    continue;
                }     
            }
            i+=1

        }
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
        if(!operation.includes('#13') && !operation.includes('#12'))
        {

            while(i < operation.length)
            {
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
        else if(operation.trim() == '#13' || operation.trim() == '#12')
        {
            // if (i!=0) console.log('parsing twice')
            while(i < rest.length && rest[i] != '}')
            {  
                if(!found && (rest[i] == '&' || rest[i].toLowerCase().match(/[a-z]/i))){
                    found = true
                }
        
                if (found) {
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
        if(operator == '#12' || operator == '#13') {
            Broperator = operator
            operator = ''
        }

        let j = 0 

        if(Broperator != '')
        {
            found = false
            //find the first operation 
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

    Convert_operators = (line) =>  {
        let ret = line 

        //longer name are replaced first

        //hardcode replace 
        ret = ret.replaceAll ('_{10}'  , '10' )
        ret = ret.replaceAll ('_{20}'  , '20' )


        ret = ret.replaceAll ('+'  , ' #200 ' )
        ret = ret.replaceAll ('-'  , ' #201 ' )
        ret = ret.replaceAll ('\\times'  , ' #202 ' )

        ret = ret.replaceAll (')'  ,' ' )
        ret = ret.replaceAll ('('  ,' ' )
        ret = ret.replaceAll (':'  , ' ' )
        ret = ret.replaceAll (';'  , ' ' )

        ret = ret.replaceAll('\\It', '&It')

        ret = ret.replaceAll ('&Fam'  , '#100' )
        ret = ret.replaceAll ('Rd_i'  , '#101' )
        ret = ret.replaceAll ('Rd_j'  , '#102' )
        ret = ret.replaceAll ('Rcpo'  , '#103' )

        ret = ret.replaceAll ('IsCpo'  , '#104' )
        ret = ret.replaceAll ('IsCpm'  , '#105' )
        ret = ret.replaceAll ('Rcpm'  , '#105' )

        ret = ret.replaceAll ('Ins'  , '#106' )
        ret = ret.replaceAll ('Del'  , '#107' )
        ret = ret.replaceAll ('&Tm'  , '#108' )
        ret = ret.replaceAll ('Cpo'  , '#109' )
        ret = ret.replaceAll('\\Ip', '&Ip')
        ret = ret.replaceAll('In', '#41')
        ret = ret.replaceAll('\\&In', '&In')

        ret = ret.replaceAll('\\nPnm',"#35")
        ret = ret.replaceAll ('\\nPdx', '#40' )
        ret = ret.replaceAll('\\nPne',"#29")
        ret = ret.replaceAll('\\nPnl',"#30")

        ret = ret.replaceAll('\\Pnl', '#23' )
        ret = ret.replaceAll('\\Pne', '#24' )
        ret = ret.replaceAll('\\nPb','#25')
        ret = ret.replaceAll('\\nPp','#26')
        ret = ret.replaceAll('\\nPn','#27')
        ret = ret.replaceAll('\\nPe',"#28")

        ret = ret.replaceAll('\\nPu',"#31")
        ret = ret.replaceAll('\\nPs',"#32")
        ret = ret.replaceAll('\\nPc','#33')
        ret = ret.replaceAll('\\Pnm',"#34")
        ret = ret.replaceAll ('\\sim' , '#36' )
        ret = ret.replaceAll ('\\Pdx' , '#39' ) 
        ret = ret.replaceAll ('Pdx' , '#39' ) 

        ret = ret.replaceAll ('!Pdx' , 'nPdx' ) 


        ret = ret.replaceAll('\\Og', '#1')
        ret = ret.replaceAll('\\Ot', '#2')
        ret = ret.replaceAll('\\On', '#3')
        ret = ret.replaceAll('\\Op', '#4')
        ret = ret.replaceAll('\\Os', '#5')
        ret = ret.replaceAll('\\Oc', '#6')
        ret = ret.replaceAll('\\Od', '#7')
        ret = ret.replaceAll('\\Ob', '#8')
        ret = ret.replaceAll('\\Oa', '#9')
        ret = ret.replaceAll('\\Oe', '#10')
        ret = ret.replaceAll('\\Or', '#11')

        ret = ret.replaceAll('\\Ps' , '#14')
        ret = ret.replaceAll('\\Tc' , '#15')
        ret = ret.replaceAll('\\Tt' , '#16')
        ret = ret.replaceAll('\\Pe' , '#17')
        ret = ret.replaceAll('\\Pp' , '#18')

        ret = ret.replaceAll('\\Pu' , '#19')
        
        ret = ret.replaceAll('\\Pn' , '#20')
        ret = ret.replaceAll('\\Pc' , '#21')
        ret = ret.replaceAll('\\Pb' , '#22')


        ret = ret.replaceAll ('\\Ri'  , '#37' )
        
        ret = ret.replaceAll ('Rd'  , '#38' )
        ret = ret.replaceAll ('Rc'  , '#43' )

        ret = this.Convert_equiv(ret)
        ret = ret.replaceAll ('R\\_'  , '#44' )
        ret = ret.replaceAll ('R'  , '#42' )

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
        ret = ret.replaceAll('\\Bs', '#13')

        ret = ret.replaceAll('\\Bb', '#13')
        ret = ret.replaceAll('\\Blb', '#13')
        ret = ret.replaceAll('\\Bls', '#13')

        ret = ret.replaceAll('\\Brs', '#12{}')
        ret = ret.replaceAll('\\Br', '#12')
        ret = ret.replaceAll('\\Brb', '#12')

        return ret
    }
}

export default LatexParser