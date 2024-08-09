import { rule, either, exactly, optional, minOf, token } from './grammar-helper.js';

const LineExpression = rule(
    () => exactly(RuleEquivalence,Eol),
    ([expression ,]) => expression
);

const RuleEquivalence = rule(
    () => exactly(leftBegin, operations, equiv, operations),
    ([, leftexps, , rightexps, ]) => ({
        type:'Equivalence Rule',
        leftexps,
        rightexps
    })
)

const operations = rule(
    () => exactly(Comma, optional( exactly(operation, Comma), [{value: '',}]), minOf(0, exactly(operation, Comma))),
    ([, [first,], rest,]) => [first, ...rest.map(([operations,]) => operations)]
)

// operation can be primitive operators, branch operators
// primitive operators are paired with 0 or more operands
// branch operators are paired with optional two int and optional operator
const operation = rule(
    () => exactly(optional(exactly(operator, int, int), {value: ''}), optional(operator, {value: ''}), optional(exactly(operands),{value: ''})),
    ([Opparam, operator, [operands]]) => ({type:'operation', operator : operator, operands : operands, Opparam : Opparam})
);


const operator = rule(
    () => either(Oa, Oe, Od, Oc, Os, Ob, Op, On, Ot, Og, Os, Or, Br, Bl, Tc),
    operator => operator
)

const operands = rule (
    () => exactly(optional(Operand, ), minOf(0, exactly(Operand))),
    ([first, rest]) => [first, ...rest.map(([expression]) => expression)]
);

const Operand = token('operand');
const int = token('int')


// Tokens

const Comma = token('comma', ',');

const Eol = token('endOfLine');

//Insert a new node or delete a non-empty node
const Oa = token('operator','#9')

//Create a new operand j. j points to a child of the node pointed to by
const Ob = token('operator','#8')

//Create a new operand j. i and $j$ point to the same node.
const Oc = token('operator','#6')

//Create a new operand pointing to a temporary newly allocated data structure. The data value of the node pointed to is the id
const Od = token('operator','#7')

//Compare the value of the node pointed to by $i$ with the value of the node pointed to by $j$. If equal code A runs, otherwise code B runs
const Oe = token('operator','#10')

//  Create a new operand i, pointing to a unique global data structure.
const Og = token('operator','#1')

//Create a new operand, pointing to a temporary newly allocated data structure.
const Ot = token('operator','#2')

//point to next node
const On = token('operator','#3')

//point to previous node
const Op = token('operator','#4')

//logical error
const Or = token('operator','#11')

const Br = token('operator','#12')

const Bl = token('operator','#13')

const Tc = token('operator','#15')

//Release operand $i$. If $i$ is the last operand that points to a temporary data structure, free the temporary data structure.
const Os = token('operator','#5')

const leftBegin = token('leftBegin', '!')

const equiv = token('equiv', '@')

//Propositions
// const Pu = token('operator','\\Pu')
// const Ps = token('operator','\\Ps')
// const Tc = token('operator','\\Tc')
// const Tt = token('operator','\\Tt')
// const Pe = token('operator','\\Pe')
// const Pp = token('operator','\\Pp')
// const Pn = token('operator','\\Pn')
// const Pc = token('operator','\\Pc')
// const Pb = token('operator','\\Pb')
// const Pnl = token('operator','\\Pnl')
// const Pne = token('operator','\\Pne')

// const nPb = token('operator','\\nPb')
// const nPp = token('operator','\\nPp')
// const nPn = token('operator','\\nPn')
// const nPc = token('operator','\\nPc')
// const nPe = token('operator','\\nPe')
// const nPne = token('operator','\\nPne')
// const nPnl = token('operator','\\nPnl')
// const nPu = token('operator','\\nPu')
// const nPs = token('operator','\\nPs')
// const Pnm = token('operator','\\Pnm')
// const nPnm = token('operator','\\nPnm')

// const Sim = token('operator', '\\sim')
// const Ri = token('operator', '\\Ri')
// const Pdx = token('operator', '\\Pdx') 
// const nPdx = token('operator', '\\nPdx') 

export default LineExpression;