

import fs from 'fs'
export const ReadFiles = Parse_rules_and_titles =>( folder, flag) => {
    // Create character reader for our code.
    let chapters = [];
    fs.readdirSync(folder).forEach(file => {
        const chapter = ParseFile(Parse_rules_and_titles, folder, fs.readFileSync, file, flag)
        chapters.push(chapter)
    })
    return chapters
}

const ParseFile = (Parse_rules_and_titles , folder, Filereader, file, flag) => {
    const s = Filereader(folder + '/' + file, {encoding: "utf8"})
    //parse characters into array of lines
    let lines = Files_to_lines(s)
    let chapter = Parse_rules_and_titles(lines, flag)
    return chapter
}

const Files_to_lines = (source) => {
    let lines = []
    let line = ''
    for(const char of source){
        if(char === '\n'){
            if(line.length > 1){lines.push(line)}
            line = ''
        }
        else{line += char}
    }
    return lines
}

export default ReadFiles