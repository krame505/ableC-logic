grammar edu:umn:ee5364project:exts:ableC:logic:concretesyntax;

terminal Bool_t 'bool';

nonterminal LogicTypeExpr_c with ast<LogicTypeExpr>, location;

concrete productions top::LogicTypeExpr_c
| 'bool'
  { top.ast = boolLogicTypeExpr(location=top.location); }
| 'signed' ':' size::DecConstant_t
  { top.ast = signedLogicTypeExpr(toInt(size.lexeme), location=top.location); }
| 'unsigned' ':' size::DecConstant_t
  { top.ast = unsignedLogicTypeExpr(toInt(size.lexeme), location=top.location); }

nonterminal LogicParameters_c with ast<LogicParameters>;

concrete productions top::LogicParameters_c
| 
  { top.ast = nilLogicParameter(); }
| p::LogicParameter_c
  { top.ast = consLogicParameter(p.ast, nilLogicParameter()); }
| h::LogicParameter_c ',' t::LogicParameters_c
  { top.ast = consLogicParameter(h.ast, t.ast); }

nonterminal LogicParameter_c with ast<LogicParameter>;

concrete productions top::LogicParameter_c
| ty::LogicTypeExpr_c id::Identifier_t
{
  top.ast = logicParameter(ty.ast, fromId(id));
}