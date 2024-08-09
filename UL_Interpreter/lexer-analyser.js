// Character reader we implemented
import CharacterReader from './character-reader.js'

// List of token detector functions we will implement.
import {
    readOperator,
    readOperand,
    readleftBegin,
    readEquiv,
    readInt,
    readEndOfLine,
    readDelimeter,
    readWhitespace,
 } from './tokens.js'

const detectTokens = code => {

    let tokenDetectors = [
        readOperator,
        readOperand,
        readleftBegin,
        readEquiv,
        readInt,
        readEndOfLine,
        readDelimeter,
        readWhitespace,
    ]
    // Create character reader for our code.
    const reader = new CharacterReader(code);

    // List of tokens we found in the code.
    const foundTokens = [];

    // We loop until we go through all of the characters.
    while (reader.hasNext()) {
        // console.log(reader)
        let token = null;

        // Store the positions in case we detect the token
        let startPosition = reader.position;
        let linePosition = reader.getLinePosition();
        let characterPosition = reader.getCharacterPosition();

        // We go through each of the token detectors
        // and call the function for detecting each token.
        for (const detectToken of tokenDetectors) {
            token = detectToken(reader);

            if (token) {
                // console.log(token)
                // Token is detected so we do not
                // continue detection.
                break;
            }
        }

        // If no token could detect the character at this
        // position means that we have a syntax error in our
        // language so we should not continue.
        if (!token) {
            throw new Error(`Invalid character '${reader.peek()}' at ${linePosition}:${characterPosition}`);
        }

        // If a token is found we store the token data
        // together with the position information.
        foundTokens.push({
            ...token,
            start: startPosition,
            end: reader.position,
            line: linePosition,
            character: characterPosition
        });
    }
    // console.log(foundTokens)
    // After we found all of the tokens we remove the whitespace
    // tokens because we will not use them.
    return foundTokens.filter(i => i.type !== 'whitespace');
};

export default detectTokens