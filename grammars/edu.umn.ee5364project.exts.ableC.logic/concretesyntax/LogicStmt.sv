grammar edu:umn:ee5364project:exts:ableC:logic:concretesyntax;

nonterminal LogicStmts_c with ast<LogicStmts>;

concrete productions top::LogicStmts_c
| h::LogicStmt_c t::LogicStmts_c
  { top.ast = consLogicStmt(h.ast, t.ast); }
| 'return' e::LogicExpr_c ';'
  { top.ast = resultLogicStmt(e.ast); }

nonterminal LogicStmt_c with ast<LogicStmt>;

concrete productions top::LogicStmt_c
| ty::LogicTypeExpr_c id::Identifier_t '=' e::LogicExpr_c ';'
  { top.ast = declLogicStmt(ty.ast, fromId(id), e.ast); } 