grammar edu:umn:ee5364project:exts:ableC:logic:concretesyntax;

terminal BitAppendOp_t ',' association=right, precedence=0, lexer classes {Csymbol};

terminal LogicIdentifier_t /[A-Za-z_\$][A-Za-z_0-9\$]*/;

terminal True_t  'true'  dominates {LogicIdentifier_t};
terminal False_t 'false' dominates {LogicIdentifier_t};

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

| e1::LogicExpr_c BitAppendOp_t e2::LogicExpr_c
  { top.ast = bitAppendExpr(e1.ast, e2.ast, location=top.location); }

| '(' e::LogicExpr_c ')'
  { top.ast = e.ast; }

function fromLogicId
Name ::= n::LogicIdentifier_t
{
  return name(n.lexeme, location=n.location);
}
