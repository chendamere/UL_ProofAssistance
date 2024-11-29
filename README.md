## Parser
Parser converts strings into data, or rules. A rule consists a left expression and a right expression. An expression consists operator, operands, and additional branch parameters There is an extended class that parses latex files following the format used to compile the book. 

## UL Proof Assistance
Proof Assistance checks whether a rule is in the database. It also checks if a rule is constructable in one of three ways: 
  P1. Expression Commutativity
  P2. Expression Transitivity
  P3. Equivalent Insertion of Expression

P1 is trivial: flip a rule's left and right expression and produce a new rule. 
P2 is the main tool for forming chain of reasoning. 
P3 is the bulk of the work when building the proof assistance. It says this: Given rule 'A=B', where A and B are expressions with arbiturary length, we are able to produce rule 'MAN=MBN', where MAN and MBN are concatenated expressions.

The construct all possible construction from P3, we need to get all the subexpression from a expression, check if a expression match with any expression in any existing rule, if it does, replace the subexpression from the other expression of the matched rule, and check whether the replaced expression is the same as the target expression.
