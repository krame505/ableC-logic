grammar edu:umn:ee5364project:exts:ableC:logic:concretesyntax;

nonterminal LogicExpr_c with ast<LogicExpr>, location;

concrete productions top::LogicExpr_c
| id::Identifier_t
  { top.ast = varLogicExpr(fromId(id), location=top.location); }

| c::DecConstant_t
    { top.ast = intLiteralLogicExpr(true, toInt(c.lexeme), location=top.location); }
| c::DecConstantU_t
    { top.ast = intLiteralLogicExpr(false, toInt(c.lexeme), location=top.location); }
{-
| c::OctConstant_t
| c::OctConstantU_t
| c::HexConstant_t
| c::HexConstantU_t-}

| '(' e::LogicExpr_c ')'
  { top.ast = e.ast; }
