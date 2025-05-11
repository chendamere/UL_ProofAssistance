import fs from 'fs'

class Fileparser{

    constructor(parser){
        this.parser = parser
    }
    ParseRulesFromFile(filename){
        let allrules = []
        fs.readdirSync(filename).forEach(file => {
            const chapter = this.parser.ParseFile( './axiom/', fs.readFileSync, file, false)
            for(const c of chapter.rules){
                let ret = this.parser.Parse(c)
                allrules.push(ret)
            }
        })
        return allrules
    }

    ParseExpressionsFromFile(filename){
        let allexps = [];
        let tstatements = []
        fs.readdirSync(filename).forEach(file => {
            let texps=[]
            let tts =[]
            let chapter = this.parser.ParseFile( './theorems/', fs.readFileSync, file, false)
            let exps = this.parser.trimExps(this.parser.ParseFile( './theorems/', fs.readFileSync, file, true))
            for(const e of exps){
                let temp =[]
                for(const exp of e) {
                    temp.push(exp.trim())
                }
                texps.push(temp)
            }
            for(const e of chapter.rules){
                tts.push(this.parser.Parse(e))
            }
            tstatements.push(tts)
            allexps.push(texps)
        })
        return [tstatements, allexps]

    }
}
export default Fileparser