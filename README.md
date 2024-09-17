## UL Proof Assistance

This file contains parser, proof assistance, and proof strategies*. 

Parser turns strings to rules/expressions, and it's extended to latexParser class, which parses from latex files.
Proof assistance checks if a statement is a proof, or if it's provable given existing rules. A statement is provable if production(s) exists, user can provide 
expressions as production steps, or proof assistance can construct similar looking expressions from previous proofs.
Proof strategy takes automation to another level, potentially using machine learning.(in progress)
