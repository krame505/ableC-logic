grammar edu:umn:ee5364project:exts:ableC:logic:concretesyntax;

imports edu:umn:cs:melt:ableC:concretesyntax;
imports silver:langutil only ast;

imports edu:umn:cs:melt:ableC:abstractsyntax:host;
imports edu:umn:cs:melt:ableC:abstractsyntax:construction;
imports edu:umn:cs:melt:ableC:abstractsyntax:env;

imports edu:umn:ee5364project:exts:ableC:logic:abstractsyntax;

marking terminal Logic_t 'logic' lexer classes {Ckeyword};

concrete production logicFunctionDecl_c
top::ExternalDeclaration_c ::= 'logic' decl::LogicFunctionDeclaration_c
{
  top.ast = decl.ast;
}

concrete production logicFunctionStmt_c
top::BlockItem_c ::= 'logic' decl::LogicFunctionDeclaration_c
{
  top.ast = [declStmt(decl.ast)];
}

nonterminal LogicFunctionDeclaration_c with ast<Decl>, location;

concrete production logicFunctionDeclaration_c
top::LogicFunctionDeclaration_c ::= ret::LogicTypeExpr_c id::Identifier_t '(' params::LogicParameters_c ')' '{' body::LogicStmts_c '}'
{
  top.ast = logicFunctionDeclaration(logicFunctionDecl(fromId(id), ret.ast, params.ast, body.ast));
}