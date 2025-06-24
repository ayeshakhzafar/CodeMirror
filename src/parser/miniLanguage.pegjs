// Mini-language grammar for PEG.js

function makeNode(type, props) {
    return Object.assign({ type }, props);
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
  = _ variable:(ArrayAccess / Identifier) _ ":=" _ expression:Expression _ ";" _
    { return makeNode('AssignmentStatement', { variable, expression }); }

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
  = "for" _ "(" _ init:AssignmentStatement _ condition:Expression _ ";" _ update:ForUpdate _ ")" _ "{" _ body:Statement* _ "}" _ {
      return makeNode('ForStatement', { init, condition, update, body });
    }

ForUpdate
  = variable:Identifier _ ":=" _ expression:Expression
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

Expression
  = BinaryExpression
  / ArrayAccess
  / Identifier
  / Literal
  / "(" _ expr:Expression _ ")" { return expr; }

BinaryExpression
  = left:Term _ operator:BinaryOperator _ right:Expression {
      return makeNode('BinaryExpression', { left, operator, right });
    }
  / Term

Term
  = ArrayAccess
  / Identifier
  / Literal
  / "(" _ expr:Expression _ ")" { return expr; }

ArrayAccess
  = array:Identifier _ "[" _ index:Expression _ "]" {
      return makeNode('ArrayAccess', { array, index });
    }

BinaryOperator
  = "+"
  / "-"
  / "*"
  / "/"
  / "%"
  / "=="
  / "!="
  / "<"
  / "<="
  / ">"
  / ">="
  / "&&"
  / "||"

Identifier
  = first:[a-zA-Z_] rest:[a-zA-Z0-9_]* {
      return makeNode('Identifier', { name: first + rest.join('') });
    }

Literal
  = value:Number {
      return makeNode('Literal', { value });
    }

Number
  = digits:[0-9]+ {
      return parseInt(digits.join(''), 10);
    }

_ "whitespace"
  = [ \t\n\r]*
  / Comment

Comment
  = "//" [^\n]* "\n"? { return null; }