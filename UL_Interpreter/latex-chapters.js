


export const LatexChapters = (ReadFiles,  folder, parser) =>{
    let chapters = ReadFiles(folder, false)
    return ParseRules(chapters,parser)
}

export const LatexExps = (ReadFiles, folder) => {
    let chapters = ReadFiles(folder, true)
    return ParseExps(chapters)
}
export const Parser = (AnalyseCode, ParseTokens) => pcode => {
    // console.log(pcode)

    let tokens = AnalyseCode(pcode)

    if(!tokens) return null

    let [rule] = ParseTokens(tokens)
    if(!rule) return null 
    
    return [rule]
}

//second order normalize
export const RuleNormalize = (line) => {

    let ret = line 
    ret = Convert_branch_expressions(ret)
    // console.log(ret)
    ret = Reorder_operations(ret)
    // console.log('after reordering: ', ret)

    ret = Operands_numbering(ret)

    // console.log('after numbering: ', ret)

    ret = '!' + ret.trim()

    return ret
}

export const expsNormalize = (line) => {
    let ret = line
     
    if(!ret.includes('@')){
        return '' 
    }
    else if(ret.trim()[0] == '@'){
        ret = ret.replace('@', '')
    }
    ret = Convert_branch_expressions(ret)
    ret = Reorder_operations(ret).trim()
    ret = Operands_numbering(ret)
    ret = ret.trim()
    return ret
}
// parse string to rules
const ParseRules = (chapters, parser) => {
    let AllRules = []
    let i=0

    for (const chapter of chapters) {
        let code = chapter.rules
        for (const c of code) {
            i += 1
            let pcode = c + '\n'
            let [rule] = parser(pcode)

            AllRules.push(rule)

        }
    }

    return AllRules;
}

const ParseExps = (chapters) => {
    let AllRules = []
    let i=0

    for (const chapter of chapters) {
        let code = chapter.rules
        for (const c of code) {
            i += 1
            let pcode = c.slice(2,c.length)
            
            AllRules.push(pcode)

        }
    }

    return AllRules;
}

export const Parse_rules_and_titles = (lines, flag) => {

    //extract title and rules
    let all_rules = []
    let title = ''
    let nline;
    let rule = '';
    let lastrule=' ';
    let parse = true

    if(flag) parse = false

    for (const line of lines){
        if(line.includes('\\Ri')) continue
        if(flag){
            if(line.includes('\\begin{math}')) {parse = true 
                continue
            }
            if(line.includes('\\end{math}'))   {parse = false
                continue
            }
        }else {
            if(line.includes('\\begin{math}')) {parse = false 
                continue
            }
            if(line.includes('\\end{math}'))   {parse = true 
                continue
            }
        }
            

        //ignore %
        if(line.includes("%")){
            continue 
        }

        //get title 
        if(!title){
            title = Extract(line,'\\chapter{','}')
            continue;
        }

        if(!parse) continue;

        //line in the file 
        nline = LineNormalize(line,flag)
        if(nline.trim() == '')
        {
            continue
        } 

        //normalize rule
        if(flag){
            rule = expsNormalize(nline)
        }else{
            rule = RuleNormalize(nline)
        }
        if(rule.trim() == '')
        {
            continue
        } 

        if(rule) {
            //if last line ends with \\Rq then join last rule with current rule
            if((!rule.includes('@'))) {     
            }
            else if(rule[rule.length-1] !== ','){

            }
            else{
                
                all_rules.push(rule)
                
            }
        }

        lastrule = rule
    }

    return {title: title , rules : all_rules}
}
const LineNormalize = (line, flag) => {
    let nline = line.trim()

    nline = simp_branch_expressions(nline)
    nline = Convert_operators(nline)
    nline = nline.trim()
    if(!flag){nline = Extract(nline,'\\[','\\]')}
    
    nline = Add_comma_to_open_branch(nline)
    return nline
}

const Operands_numbering = (line) => {

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

    for(const a of Object.keys(operand)){
        ret = ret.replaceAll(a, operand[a])
    }
    return ret 
}

const Reorder_operations = (line) => {

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

            replace = Reorder( operation, line.slice(i))
            
            if (replace.trim() != '') {
                i+=1
                ret += replace + ','
                if(replace.includes('#13')){
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

const Reorder = (operation, rest) => {
    if (operation.trim() == '') return ''


    let operators = FindOperators( operation, rest).trim()
    let operands = FindOperands(operation, rest).trim()

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

const FindOperands = (operation, rest) => {
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
        if (i!=0) console.log('parsing twice')
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

const FindOperators = (operation, rest) => {
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
        while (j < rest.length) {
            if (rest[j] == '#'){
                operator += rest[j]
                j += 1 
                found = true
                continue
            }
    
            if(rest[j] == '}' || (found && rest[j] == ' '))
            {       
                j += 1
     
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

const Add_comma_to_open_branch = (line) =>{
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


const Convert_operators = (line) =>  {
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

    ret = Convert_equiv(ret)
    ret = ret.replaceAll ('R\\_'  , '#44' )
    ret = ret.replaceAll ('R'  , '#42' )

    return ret
}

const Convert_equiv = (line) => {
    let ret = line.replaceAll('\\Rq', '@')
    return ret
}

const simp_branch_expressions = (line) => {
    //return string
    let ret = line      
    ret = ret.replaceAll('if(', '')
    ret = ret.replaceAll(')}', '}')

    return ret
}


const Convert_branch_expressions = (line) => {
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

//remove extra charater before and after the line
const Extract = (line,begin,end) => {
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

export default {LatexChapters, Parser, LatexExps, RuleNormalize,expsNormalize, Parse_rules_and_titles}