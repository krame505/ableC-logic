grammar edu:umn:ee5364project:exts:ableC:logic:abstractsyntax;

import silver:util:raw:treemap as tm;

-- The flow computed for every bit of a logic expression
synthesized attribute logicFlow::[LogicFlowExpr];
synthesized attribute logicFlows::[[LogicFlowExpr]];
-- The flow computed for every named bit, used to build the overall flow graph
synthesized attribute logicFlowDefs::[Pair<String LogicFlowExpr>];

autocopy attribute logicFlowGraph::tm:Map<String Decorated LogicFlowExpr>;

autocopy attribute renameFn::(String ::= String);
synthesized attribute renamed::LogicFlowExpr;

nonterminal LogicFlowExpr with logicFlowGraph, renameFn, pp, renamed;

abstract production constantLogicFlowExpr
top::LogicFlowExpr ::= b::Boolean
{
  propagate renamed;
  top.pp = if b then pp"true" else pp"false";
}

abstract production varLogicFlowExpr
top::LogicFlowExpr ::= n::String
{
  top.pp = text(n);
  top.renamed = varLogicFlowExpr(top.renameFn(n));
}

abstract production andLogicFlowExpr
top::LogicFlowExpr ::= e1::LogicFlowExpr e2::LogicFlowExpr
{
  propagate renamed;
  top.pp = pp"(${e1.pp} & ${e2.pp})";
}

abstract production orLogicFlowExpr
top::LogicFlowExpr ::= e1::LogicFlowExpr e2::LogicFlowExpr
{
  propagate renamed;
  top.pp = pp"(${e1.pp} | ${e2.pp})";
}

abstract production notLogicFlowExpr
top::LogicFlowExpr ::= e::LogicFlowExpr
{
  propagate renamed;
  top.pp = pp"(!${e.pp})";
}

function buildFlowGraph
tm:Map<String LogicFlowExpr> ::= defs::[Pair<String LogicFlowExpr>]
{
  return tm:add(defs, tm:empty(compareString));
}

function renameLogicFlowExpr
LogicFlowExpr ::= renameFn::(String ::= String) lfe::LogicFlowExpr
{
  lfe.renameFn = renameFn;
  return lfe.renamed;
}

function renameLogicFlowDefs
[Pair<String LogicFlowExpr>] ::= renameFn::(String ::= String) defs::[Pair<String LogicFlowExpr>]
{
  return
    zipWith(
      pair,
      map(renameFn, map(fst, defs)),
      map(renameLogicFlowExpr(renameFn, _), map(snd, defs)));
}
