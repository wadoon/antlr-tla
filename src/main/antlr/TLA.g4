grammar TLA;

//CommaList(L) == L & (tok',' &  L)*
//AtLeast4(s) == Tok({s \o s \o s} & {s}+)

ASSUME: 'ASSUME';
ELSE: 'ELSE';
LOCAL: 'LOCAL';
UNION: 'UNION';
ASSUMPTION: 'ASSUMPTION';
ENABLED: 'ENABLED';
MODULE: 'MODULE';
VARIABLE: 'VARIABLE';
AXIOM: 'AXIOM';
EXCEPT: 'EXCEPT';
OTHER: 'OTHER';
VARIABLES: 'VARIABLES';
CASE: 'CASE';
EXTENDS: 'EXTENDS';
SF_: 'SF_';
WF_: 'WF_';
CHOOSE: 'CHOOSE';
IF: 'IF';
SUBSET: 'SUBSET';
WITH: 'WITH';
CONSTANT: 'CONSTANT';
IN: 'IN';
THEN: 'THEN';
CONSTANTS: 'CONSTANTS' ;
INSTANCE: 'INSTANCE';
THEOREM: 'THEOREM';
COROLLARY: 'COROLLARY';
DOMAIN: 'DOMAIN';
LET: 'LET';
UNCHANGED: 'UNCHANGED';
BY: 'BY';
HAVE: 'HAVE';
QED: 'QED';
TAKE: 'TAKE';
DEF: 'DEF';
HIDE: 'HIDE';
RECURSIVE: 'RECURSIVE';
USE: 'USE';
DEFINE: 'DEFINE';
PROOF: 'PROOF';
WITNESS: 'WITNESS';
PICK: 'PICK';
DEFS: 'DEFS';
PROVE: 'PROVE';
SUFFICES: 'SUFFICES';
NEW: 'NEW';
LAMBDA: 'LAMBDA';
STATE: 'STATE';
ACTION: 'ACTION';
TEMPORAL: 'TEMPORAL';
OBVIOUS: 'OBVIOUS';
OMITTED: 'OMITTED';
LEMMA: 'LEMMA';
PROPOSITION: 'PROPOSITION';
ONLY: 'ONLY';

Comment: '\\*' ~[\n\r]*;

MinusSep: '-''-''-''-'+;
EqSep: '=''=''=''='+;

Minus:'-';
Eq: '==';

fragment Letter: [a-zA-Z];
fragment Numeral: [0-9];
fragment NameChar: Letter | Numeral | '_';

//name: Tok((nameChar* & Letter & nameChar*) \ ({'WF_','SF_'} & nameChar+))

Identifier: NameChar* Letter NameChar*;

fragment
NumberLexeme:
         Numeral+
      |  (Numeral*  '.'?  Numeral+)
      |  ('\\b'|'\\B') [01]+
      |  ('\\o'| '\\O') [0-7]+
      |  ('\\h'| '\\H') [0-9a-f]+
      ;

Number: NumberLexeme;

ProofStepId: '<'? (Numeral+ | '*') '>'? (Letter | Numeral | '_'?)+;

BeginStepToken: '<'?  (Numeral+ | '*' | '+')  '>'?  (Letter | Numeral)* '.'* ;

String: '"'  .*?  '"';

WS: [ \n\f\t]+ -> channel(HIDDEN);

prefixOp: '-'| '~' | '\\lnot'| '\\neg'| '[]'| '<>'| 'DOMAIN'|  'ENABLED'| 'SUBSET'| 'UNCHANGED'| 'UNION';

infixOp:
  '!!'|  '#'|    '##'|   '$'|    '$$'|   '%'|    '%%'|
         '&'|   '&&'|   '(+)'|  '(-)'|  '(.)'|  '(/)'|  '(\\X)'|
         '*'|   '**'|   '+'|    '++'|   '-'|    '-+->'| '--'|
         '-|'|  '..'|   '...'|  '/'|    '//'|   '/='|   '/\\'|
         ':'| ':='|   ':>'|   '<'|    '<:'|   '<=>'|  '='|
         '=<'|  '=>'|   '=|'|   '>'|    '>='|   '??'|
         '@@'|  '\\'|   '\\/'|  '^'|    '^^'|   '|'|    '|-'|
         '|='|  '||'|   '~>'|   '.'|    '<='| '::=' |
         '\\approx'|  '\\geq'|       '\\oslash'|     '\\sqsupseteq'|
         '\\asymp'|   '\\gg'|        '\\otimes'|     '\\star'|
         '\\bigcirc'| '\\in'|        '\\prec'|       '\\subset'|
         '\\bullet'|  '\\intersect'| '\\preceq'|     '\\subseteq'|
         '\\cap'|     '\\land'|      '\\propto'|     '\\succ'|
         '\\cdot'|    '\\leq'|       '\\sim'|        '\\succeq'|
         '\\circ'|    '\\ll'|        '\\simeq'|      '\\supset'|
         '\\cong'|    '\\lor'|       '\\sqcap'|      '\\supseteq'|
         '\\cup'|     '\\o'|         '\\sqcup'|      '\\union'|
         '\\div'|     '\\odot'|      '\\sqsubset'|   '\\uplus'|
         '\\doteq'|   '\\ominus'|    '\\sqsubseteq'| '\\wr'|
         '\\equiv'|   '\\oplus'|     '\\sqsupset'|   '\\notin';

postfixOp :  '^+'|  '^*'| '^#'| '\'';


identifierOrTuple:  Identifier | '<<' Identifier (',' Identifier) '>>';

module:
    MinusSep
    MODULE name
    MinusSep
    (EXTENDS extends+=name (',' extends+=name)*)?
    unit*
    EqSep
;

name:Identifier;

unit:
              variableDeclaration
           |  constantDeclaration
           |  recursive
           |  useOrHide
           |  (LOCAL)? operatorDefinition
           |  (LOCAL)? functionDefinition
           |  (LOCAL)? instance
           |  (LOCAL)? moduleDefinition
           |  assumption
           |  theorem proof?
           |  module
           |  MinusSep
;

variableDeclaration:
    ('VARIABLE' | 'VARIABLES')  Identifier (',' Identifier)*;

constantDeclaration:
    ('CONSTANT' | 'CONSTANTS') opDecl (',' opDecl)*;

recursive: 'RECURSIVE' opDecl (',' opDecl)*;

opDecl:
    Identifier
  | Identifier '(' '_' (',' '_')* ')'
  | prefixOp '_'
  |  '_'  infixOp '_'
  |  '_' postfixOp
;

operatorDefinition:
  (   nonFixLHS
  |  prefixOp    Identifier
  |  Identifier  infixOp  Identifier
  |  Identifier  postfixOp )
  '=='
  expression
;

nonFixLHS :
   Identifier
   ('(' (Identifier |  opDecl) (',' Identifier |  opDecl)* ')' )?
;

functionDefinition:
     Identifier
  '['  quantifierBound ( ',' quantifierBound)*  ']'
  '=='
  expression
;

quantifierBound:
  (identifierOrTuple | Identifier (',' Identifier)*)
  '\\in'
  expression
;

instance:
          'INSTANCE'
          name
        'WITH'?  substitution (',' substitution)*
;

substitution:
  (Identifier | prefixOp | infixOp | postfixOp )
  '<-'
  argument
;

argument: expression  | opname | lambda;

lambda: 'LAMBDA' Identifier (',' Identifier)* (':'  expression);

opname:
  (Identifier | prefixOp | infixOp | postfixOp | ProofStepId)
  (  '!'
    (Identifier | prefixOp | infixOp | postfixOp
    | ('<<'| '>>'| '@' | Number) )
  )*
;

opArgs: '(' argument (',' argument)* ')';
instOrSubexprPrefix:
  ( (ProofStepId  '!')?
    ( (   Identifier  (opArgs)?
      | ('<<'| '>>'| ':'| Number)
      | opArgs
      | (prefixOp | postfixOp)  '('  expression  ')'
      | infixOp  '('  expression  ','  expression  ')'
      )
      '!'
    )*
  )
;

generalIdentifier :
           instOrSubexprPrefix?  Identifier | ProofStepId;
        
moduleDefinition: nonFixLHS '==' instance;

assumption : ('ASSUME' | 'ASSUMPTION' | 'AXIOM' ) (name  '==')?  expression;
theorem : ('THEOREM'| 'PROPOSITION'| 'LEMMA'| 'COROLLARY')
              (name  '==')?  (expression | assumeProve)
;

assumeProve :    'ASSUME'
                          (expression | new | innerAssumeProve)
                          (',' (expression | new | innerAssumeProve))*
                  'PROVE'
                          expression
;

innerAssumeProve : (name  '::')?  assumeProve;

new:
  'NEW'? ('CONSTANT' | 'VARIABLE' | 'STATE' | 'ACTION' | 'TEMPORAL')?
  (Identifier  '\\in'  expression | opDecl)
;
   
proof :   terminalProof | nonTerminalProof;
terminalProof:   'PROOF'? 'BY'   ('ONLY'?  useBody | 'OBVIOUS' | 'OMITTED' );
nonTerminalProof: 'PROOF'? step* qedStep;

step:
  BeginStepToken
  (  ( useOrHide
    | 'DEFINE'? (operatorDefinition | functionDefinition | moduleDefinition)+
    | instance
    | 'HAVE'  expression
    | 'WITNESS'  expression (',' expression)*
    | 'TAKE'  ( quantifierBound (',' quantifierBound)*
              | Identifier (',' Identifier)* )
    )
  |  ( 'SUFFICES'? (expression | assumeProve)
    | 'CASE'  expression
    | 'PICK'
      ( quantifierBound (',' quantifierBound)*
      | Identifier (',' Identifier)* )
      ':' expression

    )
    proof?
  )
;

qedStep: BeginStepToken   'QED'  proof?;
useOrHide:  ( 'USE' 'ONLY'?  | 'HIDE' ) useBody;
useBody:  ((expression | 'MODULE'  name ) (',' (expression | 'MODULE'  name ))*)?
          ( ('DEF'| 'DEFS')
            (opname | 'MODULE'  name) (',' (opname | 'MODULE'  name))*
          )?
;

expression:
    name  ('('  Identifier (',' Identifier)*  ')')? '::'  expression
  |  instOrSubexprPrefix ('<<'| '>>'| ':' | Number | opArgs)
  |  generalIdentifier opArgs?
  |  prefixOp  expression
  |  expression  infixOp  expression
  |  expression  postfixOp
  |  '('  expression  ')'
  |  ('\\A'| '\\E') quantifierBound (',' quantifierBound)*
    ':'
    expression
  |    ('\\A'| '\\E'| '\\AA'| '\\EE')
     Identifier (',' Identifier)*
     ':'
     expression
  |    'CHOOSE' identifierOrTuple ('\\in'  expression)? ':' expression
  | '{' (expression (',' expression)*)? '}'
  | '{' identifierOrTuple  '\\in'  expression ':' expression '}'
  | '{' expression ':' quantifierBound (',' quantifierBound)* '}'
  | expression  '['  expression (',' expression)* ']'
  | '[' quantifierBound (',' quantifierBound)* '|->' expression ']'
  | '[' expression  '->' expression  ']'
  | '[' name  '|->'  expression (',' name  '|->'  expression)* ']'
  | '[' name  ':'  expression (',' name  ':'  expression)* ']'
  | '[' expression 'EXCEPT'
     '!' ( '.'  name |  '['  expression (',' expression)*  ']' )+ '='  expression
     (',' '!' ( '.'  name |  '['  expression (',' expression)*  ']' )+ '='  expression)*
  ']'
  |  expression  '.'  name
  |  '<<'  (expression (',' expression)*)?  '>>'
  |  expression  (('\\X'| '\\times') expression)+
  |  '['   expression  ']_' expression
  | '<<'  expression  '>>_'  expression
  | ('WF_'| 'SF_') expression '('  expression  ')'
  | 'IF'    expression 'THEN'   expression 'ELSE'  expression
  |  'CASE'
   expression  '->'  expression
   ('[]'  expression  '->'  expression)*
   ('[]'  'OTHER'  '->'  expression)?
  | LET (    operatorDefinition |  functionDefinition |  moduleDefinition)+
    'IN'
    expression
  |  ('/\\'  expression)+
  |  ('\\/'  expression)+
  |  Number
  |  String
  |  '@'
;
