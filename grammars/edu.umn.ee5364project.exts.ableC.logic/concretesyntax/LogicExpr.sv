grammar edu:umn:ee5364project:exts:ableC:logic:concretesyntax;

terminal MaxPrecLBracket_t /\[/ precedence=15, lexer classes {Csymbol};

terminal LogicalNotOp_t '!' precedence=14, lexer classes {Csymbol};

terminal LogicalAndOp_t '&&' association=left, precedence=5, lexer classes {Csymbol};

terminal LogicalOrOp_t '||' association=left, precedence=4, lexer classes {Csymbol};

terminal BitAppendOp_t /,/ association=right, precedence=1, lexer classes {Csymbol};

terminal LogicIdentifier_t /[A-Za-z_\$][A-Za-z_0-9\$]*/;

terminal True_t  'true'  dominates {LogicIdentifier_t};
terminal False_t 'false' dominates {LogicIdentifier_t};

terminal Range_t '..';

-- Disambiguate inside function calls
disambiguate Comma_t, BitAppendOp_t {
  pluck Comma_t;
}

nonterminal LogicExpr_c with ast<LogicExpr>, location;

concrete productions top::LogicExpr_c
| id::LogicIdentifier_t
  { top.ast = varLogicExpr(fromLogicId(id), location=top.location); }

| 'true'
   { top.ast = boolConstantLogicExpr(true, location=top.location); }
| 'false'
   { top.ast = boolConstantLogicExpr(false, location=top.location); }
| c::DecConstant_t
  { top.ast = intLiteralLogicExpr(true, toInt(c.lexeme), location=top.location); }
| '-' c::DecConstant_t
  { top.ast = intLiteralLogicExpr(true, -toInt(c.lexeme), location=top.location); }
| c::DecConstantU_t
  { top.ast = intLiteralLogicExpr(false, toInt(substring(0, length(c.lexeme) - 1, c.lexeme)), location=top.location); }
{-
| c::OctConstant_t
| c::OctConstantU_t
| c::HexConstant_t
| c::HexConstantU_t-}

| '(' e::LogicExpr_c ')'
  { top.ast = e.ast; }
  
| f::LogicIdentifier_t '(' a::LogicExprs_c ')'
  { top.ast = callLogicExpr(fromLogicId(f), a.ast, location=top.location); }
| e::LogicExpr_c MaxPrecLBracket_t i::DecConstant_t ']'
  { top.ast = bitSelectLogicExpr(e.ast, toInt(i.lexeme), location=top.location); }
| e::LogicExpr_c MaxPrecLBracket_t i::DecConstant_t '..' j::DecConstant_t ']'
  { top.ast = bitSelectRangeLogicExpr(e.ast, toInt(i.lexeme), toInt(j.lexeme), location=top.location); }

| LogicalNotOp_t e::LogicExpr_c
  { top.ast = logicalNotLogicExpr(e.ast, location=top.location); }
  
| e1::LogicExpr_c LogicalAndOp_t e2::LogicExpr_c
  { top.ast = logicalAndLogicExpr(e1.ast, e2.ast, location=top.location); }
  
| e1::LogicExpr_c LogicalOrOp_t e2::LogicExpr_c
  { top.ast = logicalOrLogicExpr(e1.ast, e2.ast, location=top.location); }

| e1::LogicExpr_c BitAppendOp_t e2::LogicExpr_c
  { top.ast = bitAppendLogicExpr(e1.ast, e2.ast, location=top.location); }

nonterminal LogicExprs_c with ast<LogicExprs>;

concrete productions top::LogicExprs_c
| h::LogicExpr_c ',' t::LogicExprs_c
  { top.ast = consLogicExpr(h.ast, t.ast); }
| h::LogicExpr_c
  { top.ast = consLogicExpr(h.ast, nilLogicExpr()); }
| 
  { top.ast = nilLogicExpr(); }

function fromLogicId
Name ::= n::LogicIdentifier_t
{
  return name(n.lexeme, location=n.location);
}
