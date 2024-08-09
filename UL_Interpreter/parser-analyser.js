// We include the the grammar here.
// Grammar exports the very first rule: LineStatement
// That means that parseGrammar is actually same as LineStatement constant.
import parseGrammar  from  './grammar.js'
import TokenReader from  './token-reader.js'

const parseTokens = tokens => {
    // Create a reader for our tokens.
    const reader = new TokenReader(tokens);
    // console.log(tokens)

    const statements = [];

    while (reader.hasNext()) {
        // We parse grammar until we have a next token.

        const statement = parseGrammar(reader);

        if (statement) {
            // Our statement was parsed successfully,
            // so we add it to the list of statements.
            if(statement.type == 'endOfLine') {continue};
            statements.push(statement);
            continue;
        }

        // Something went wrong here, we couldn't parse our statement here
        // so our language needs to throw a syntax error.
        let token = reader.hasNext() ? reader.get() : reader.getLastToken();
        
        throw new Error(`Syntax error on`, token);
    }
    // console.log(statements)
    // console.log(statements[0].operations[0].operands)

    // Return the parsed statements
    return statements;
};

export default parseTokens;