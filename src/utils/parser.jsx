import * as pegjs from "pegjs"

// Define the grammar for our mini-language
const grammar = `
{
  function makeNode(type, props) {
    return Object.assign({ type }, props);
  }
}

Program
  = statements:Statement* {
      return { type: 'Program', statements };
    }

Statement
  = AssignmentStatement
  / IfStatement
  / WhileStatement
  / ForStatement
  / AssertStatement
  / _ ";" _ { return { type: "EmptyStatement" }; }

AssignmentStatement
  = _ variable:(ArrayAccess / Identifier) _ op:AssignmentOperator _ expression:Expression _ ";" _
    { return makeNode('AssignmentStatement', { variable, expression }); }

AssignmentOperator
  = ":="
  / "="

IfStatement
  = "if" _ "(" _ condition:Expression _ ")" _ "{" _ thenBlock:Statement* _ "}" _ elseBlock:(ElseBlock)? {
      return makeNode('IfStatement', { condition, thenBlock, elseBlock: elseBlock || [] });
    }

ElseBlock
  = "else" _ "{" _ statements:Statement* _ "}" _ {
      return statements;
    }

WhileStatement
  = "while" _ "(" _ condition:Expression _ ")" _ "{" _ body:Statement* _ "}" _ {
      return makeNode('WhileStatement', { condition, body });
    }

ForStatement
  = "for" _ "(" _ init:ForInit _ condition:Expression _ ";" _ update:ForUpdate _ ")" _ "{" _ body:Statement* _ "}" _ {
      return makeNode('ForStatement', { init, condition, update, body });
    }

ForInit
  = variable:Identifier _ op:AssignmentOperator _ expression:Expression _ ";"
    { return makeNode('AssignmentStatement', { variable, expression }); }

ForUpdate
  = variable:Identifier _ op:AssignmentOperator _ expression:Expression
    { return makeNode('AssignmentStatement', { variable, expression }); }

AssertStatement
  = "assert" _ "(" _ condition:(QuantifiedExpression / Expression) _ ")" _ ";" _ {
      return makeNode('AssertStatement', { condition });
    }

QuantifiedExpression
  = "forall" _ variable:Identifier _ "in" _ "range" _ "(" _ end:Expression _ ")" _ ":" _ body:Expression {
      return makeNode('QuantifiedExpression', { quantifier: 'forall', variable, end, body });
    }
  / "exists" _ variable:Identifier _ "in" _ "range" _ "(" _ end:Expression _ ")" _ ":" _ body:Expression {
      return makeNode('QuantifiedExpression', { quantifier: 'exists', variable, end, body });
    }
  / "for" _ "(" _ variable:Identifier _ "in" _ "range" _ "(" _ end:Expression _ ")" _ ")" _ ":" _ body:Expression {
      return makeNode('QuantifiedExpression', { quantifier: 'forall', variable, end, body });
    }
  / "for" _ variable:Identifier _ "in" _ "range" _ "(" _ end:Expression _ ")" _ ":" _ body:Expression {
      return makeNode('QuantifiedExpression', { quantifier: 'forall', variable, end, body });
    }

Expression
  = LogicalExpression

LogicalExpression
  = left:ComparisonExpression _ operator:LogicalOperator _ right:LogicalExpression {
      return makeNode('BinaryExpression', { left, operator, right });
    }
  / ComparisonExpression

ComparisonExpression
  = left:AdditiveExpression _ operator:ComparisonOperator _ right:ComparisonExpression {
      return makeNode('BinaryExpression', { left, operator, right });
    }
  / AdditiveExpression

AdditiveExpression
  = left:MultiplicativeExpression _ operator:AdditiveOperator _ right:AdditiveExpression {
      return makeNode('BinaryExpression', { left, operator, right });
    }
  / MultiplicativeExpression

MultiplicativeExpression
  = left:PrimaryExpression _ operator:MultiplicativeOperator _ right:MultiplicativeExpression {
      return makeNode('BinaryExpression', { left, operator, right });
    }
  / PrimaryExpression

PrimaryExpression
  = ArrayAccess
  / Identifier
  / Literal
  / "(" _ expr:Expression _ ")" { return expr; }

LogicalOperator
  = "&&"
  / "||"

ComparisonOperator
  = "=="
  / "="  { return "=="; }  // Treat single equals as equality in expressions
  / "!="
  / "<="
  / ">="
  / "<"
  / ">"

AdditiveOperator
  = "+"
  / "-"

MultiplicativeOperator
  = "*"
  / "/"
  / "%"

ArrayAccess
  = array:Identifier _ "[" _ index:Expression _ "]" {
      return makeNode('ArrayAccess', { array, index });
    }

Identifier
  = first:[a-zA-Z_] rest:[a-zA-Z0-9_]* {
      return makeNode('Identifier', { name: first + rest.join('') });
    }

Literal
  = value:Number {
      return makeNode('Literal', { value });
    }
  / BooleanLiteral

BooleanLiteral
  = "true" { return makeNode('Literal', { value: true }); }
  / "false" { return makeNode('Literal', { value: false }); }

Number
  = digits:[0-9]+ {
      return parseInt(digits.join(''), 10);
    }

_ "whitespace"
  = [ \\t\\n\\r]*
  / Comment

Comment
  = "//" [^\\n]* "\\n"? { return null; }
`

// Create the parser from the grammar
const parser = pegjs.generate(grammar)

/**
 * Parse a program written in our mini-language
 * @param {string} code - The source code to parse
 * @returns {Object} The AST (Abstract Syntax Tree) of the program
 */
export function parseProgram(code) {
  try {
    console.log("Parsing code:", code)
    const ast = parser.parse(code)
    console.log("Parsed AST:", ast)
    return {
      success: true,
      ast,
    }
  } catch (error) {
    console.error("Parse error:", error)
    return {
      success: false,
      error: {
        message: error.message,
        location: error.location,
      },
    }
  }
}

/**
 * Pretty print the AST for debugging
 * @param {Object} ast - The AST to print
 * @returns {string} A formatted string representation of the AST
 */
export function prettyPrintAST(ast) {
  return JSON.stringify(ast, null, 2)
}
