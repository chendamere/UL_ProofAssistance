export const readleftBegin = reader => { 
    let value;
    if (reader.peek().match('!')) 
        {
            value = reader.peek()
            reader.next();
            return {type:'leftBegin',value}
        }
    else return null 
}
export const readEquiv = reader => { 
    let value;
    if (reader.peek().match('@')) 
        {
            value = reader.peek()
            reader.next();
            return {type:'equiv',value}
        }
    return null 
}

export const readInt = reader => {
    // Regex for operator characters we want to detect.
    const dilimeter = /[,; \n\t({})]/;
    
    //all operator start with \\ and end with dilemeter
    if (reader.peek() != '$') return null

    let value= '';

    // index for reading operators 
    while (reader.hasNext()){
        if (reader.peek().match(dilimeter)){
            break;
        }
        
        value += reader.peek();
        reader.next();

    }

    if (value) {
        // Operator is found, we return the token.
        return { type: 'int', value };
    }

    // Nothing was found so we return null that the token was not found.
    return null;
}

export const readOperator = reader => {
    // Regex for operator characters we want to detect.
    const dilimeter = /[,; \n\t({})]/;
    
    //all operator start with \\ and end with dilemeter
    if (reader.peek() != '#') return null

    let value= '';

    // index for reading operators 
    while (reader.hasNext()){
        if (reader.peek().match(dilimeter)){
            break;
        }
        
        value += reader.peek();
        reader.next();

    }

    if (value) {
        // Operator is found, we return the token.
        return { type: 'operator', value };
    }

    // Nothing was found so we return null that the token was not found.
    return null;
}

export const readOperand = reader => {
    let value = '';
    const startOfVariableMatch = /[a-za-zA-Z0-9&]/;
    const restOfVariableMatch = /[_a-zA-Z0-9]/;

    // If we did not match variable, do not return a token.
    if (!reader.peek().match(startOfVariableMatch)) {
        return null;
    }

    value = reader.peek();
    reader.next();

    while (reader.hasNext() && reader.peek().match(restOfVariableMatch)) {
        // add a character to value as long as we match the variable name.
        value += reader.peek();
        reader.next();
    }
    if(value === 'if') return null
    // we return a variable token
    return { type: 'operand', value };
}

export const readEndOfLine = reader => {
    if (reader.peek(reader.position) == '\n') {
        // Semicolon is detected
        reader.next();
        return { type: 'endOfLine', value: '\n' };
    }

    // Semicolon is not detected
    return null;
}

export const readDelimeter = reader => {
    if (reader.peek() == ',') {
        // Comma was detected
        reader.next();
        return { type: 'comma', value: ',' };
    }

    // Token was not detected.
    return null;
}

export const readWhitespace = reader => {
    const whitespaceRegex = /[\t\r ]/; // Regex for detecting whitespace.
    let value = '';
    while (reader.hasNext() && reader.peek().match(whitespaceRegex)) {
        // add detected whitespace to the value
        value += reader.peek();
        reader.next();
    }

    if (value.length > 0) {
        // Return detected whitespace.
        return { type: 'whitespace', value };
    }

    // No whitespace token was detected.
    return null;
}
