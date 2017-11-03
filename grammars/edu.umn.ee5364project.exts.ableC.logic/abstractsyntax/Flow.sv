grammar edu:umn:ee5364project:exts:ableC:logic:abstractsyntax;

import silver:util:raw:treemap as tm;

-- The flow computed for every bit of a logic expression
synthesized attribute logicFlow::[LogicFlowExpr];
synthesized attribute logicFlows::[[LogicFlowExpr]];
-- The flow computed for every named bit, used to build the overall flow graph
synthesized attribute logicFlowDefs::[Pair<String LogicFlowExpr>];

-- The complete flow graph that is provided to each element of the graph as a Map
autocopy attribute logicFlowGraph::tm:Map<String Decorated LogicFlowExpr>;

-- Functor and supporting attributes for function stitching
synthesized attribute renamed::LogicFlowExpr;
autocopy attribute renameFn::(String ::= String);

synthesized attribute paramSubstituted::LogicFlowExpr;
autocopy attribute parameters::[[LogicFlowExpr]];

nonterminal LogicFlowExpr with logicFlowGraph, renameFn, parameters, pp, renamed, paramSubstituted;

abstract production constantLogicFlowExpr
top::LogicFlowExpr ::= b::Boolean
{
  propagate renamed, paramSubstituted;
  top.pp = if b then pp"true" else pp"false";
}

abstract production parameterLogicFlowExpr
top::LogicFlowExpr ::= paramIndex::Integer bitIndex::Integer
{
  propagate renamed;
  top.pp = brackets(ppConcat([text(toString(paramIndex)), comma(), text(toString(bitIndex))]));
  top.paramSubstituted = head(drop(bitIndex, head(drop(paramIndex, top.parameters))));
}

abstract production nodeLogicFlowExpr
top::LogicFlowExpr ::= id::String
{
  propagate paramSubstituted;
  top.pp = text(id);
  top.renamed = nodeLogicFlowExpr(top.renameFn(id));
}

abstract production andLogicFlowExpr
top::LogicFlowExpr ::= e1::LogicFlowExpr e2::LogicFlowExpr
{
  propagate renamed, paramSubstituted;
  top.pp = pp"(${e1.pp} & ${e2.pp})";
}

abstract production orLogicFlowExpr
top::LogicFlowExpr ::= e1::LogicFlowExpr e2::LogicFlowExpr
{
  propagate renamed, paramSubstituted;
  top.pp = pp"(${e1.pp} | ${e2.pp})";
}

abstract production notLogicFlowExpr
top::LogicFlowExpr ::= e::LogicFlowExpr
{
  propagate renamed, paramSubstituted;
  top.pp = pp"(!${e.pp})";
}

{-
function buildFlowGraph
[Pair<String Decorated LogicFlowExpr>] ::= defs::[Pair<String LogicFlowExpr>]
{
  local flowGraph::[Pair<String Decorated LogicFlowExpr>] =
    zipWith(
      pair,
      map(fst, defs),
      map(\ lfe::LogicFlowExpr -> decorate lfe with {logicFlowGraph = flowGraphMap;}, map(snd, defs)));
  local flowGraphMap::tm:Map<String Decorated LogicFlowExpr> = tm:add(flowGraph, tm:empty(compareString));
  return flowGraph;
}
-}

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

function subParamsLogicFlowExpr
LogicFlowExpr ::= params::[[LogicFlowExpr]] lfe::LogicFlowExpr
{
  lfe.parameters = params;
  return lfe.paramSubstituted;
}

function subParamsLogicFlowDefs
[Pair<String LogicFlowExpr>] ::= params::[[LogicFlowExpr]] defs::[Pair<String LogicFlowExpr>]
{
  return
    zipWith(
      pair,
      map(fst, defs),
      map(subParamsLogicFlowExpr(params, _), map(snd, defs)));
}
