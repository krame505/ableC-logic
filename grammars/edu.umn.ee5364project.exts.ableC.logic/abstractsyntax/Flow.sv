grammar edu:umn:ee5364project:exts:ableC:logic:abstractsyntax;

import silver:util:raw:treemap as tm;

-- The flow computed for every bit of a logic expression
synthesized attribute flowResult::[FlowExpr];
synthesized attribute flowResults::[[FlowExpr]];
-- The flow computed for every named bit, used to build the overall flow graph
synthesized attribute flowDefs::[Pair<String FlowExpr>];

nonterminal FlowGraph with pp, flowDefs, flowResult;

abstract production flowGraph
top::FlowGraph ::= flowDefs::[Pair<String FlowExpr>] flowResult::[FlowExpr]
{
  top.pp =
    ppImplode(
      line(),
      map(
        \ item::Pair<String FlowExpr> -> pp"${text(item.fst)} = ${item.snd.pp};", flowDefs) ++
      [pp"return ${ppImplode(pp", ", map((.pp), flowResult))};"]);
  top.flowDefs = flowDefs;
  top.flowResult = flowResult;

  local flowEnv::tm:Map<String Decorated FlowExpr> =
    tm:add(decFlowDefs, tm:empty(compareString));
  production decFlowDefs::[Pair<String Decorated FlowExpr>] =
    zipWith(
      pair,
      map(fst, flowDefs),
      map(decorateFlowExpr(flowEnv, _), map(snd, flowDefs)));
  production decFlow::[Decorated FlowExpr] =
    map(decorateFlowExpr(flowEnv, _), flowResult);
}

-- The complete flow graph that is provided to each element of the graph as a Map
autocopy attribute flowEnv::tm:Map<String Decorated FlowExpr>;

-- Functor and supporting attributes for function stitching
synthesized attribute renamed::FlowExpr;
autocopy attribute renameFn::(String ::= String);

synthesized attribute paramSubstituted::FlowExpr;
autocopy attribute parameters::[[FlowExpr]];

nonterminal FlowExpr with flowEnv, renameFn, parameters, pp, renamed, paramSubstituted;
flowtype FlowExpr = decorate {flowEnv};

abstract production constantFlowExpr
top::FlowExpr ::= b::Boolean
{
  propagate renamed, paramSubstituted;
  top.pp = if b then pp"true" else pp"false";
}

abstract production parameterFlowExpr
top::FlowExpr ::= paramIndex::Integer bitIndex::Integer
{
  propagate renamed;
  top.pp = cat(braces(text(toString(paramIndex))), brackets(text(toString(bitIndex))));
  top.paramSubstituted = head(drop(bitIndex, head(drop(paramIndex, top.parameters))));
}

abstract production nodeFlowExpr
top::FlowExpr ::= id::String
{
  propagate paramSubstituted;
  top.pp = text(id);
  top.renamed = nodeFlowExpr(top.renameFn(id));
  
  production refNode::Decorated FlowExpr = head(tm:lookup(id, top.flowEnv));
}

abstract production andFlowExpr
top::FlowExpr ::= e1::FlowExpr e2::FlowExpr
{
  propagate renamed, paramSubstituted;
  top.pp = pp"(${e1.pp} & ${e2.pp})";
}

abstract production orFlowExpr
top::FlowExpr ::= e1::FlowExpr e2::FlowExpr
{
  propagate renamed, paramSubstituted;
  top.pp = pp"(${e1.pp} | ${e2.pp})";
}

abstract production notFlowExpr
top::FlowExpr ::= e::FlowExpr
{
  propagate renamed, paramSubstituted;
  top.pp = pp"(!${e.pp})";
}

function decorateFlowExpr
Decorated FlowExpr ::= flowEnv::tm:Map<String Decorated FlowExpr> lfe::FlowExpr
{
  return decorate lfe with {flowEnv = flowEnv;};
}

function renameFlowExpr
FlowExpr ::= renameFn::(String ::= String) lfe::FlowExpr
{
  lfe.renameFn = renameFn;
  return lfe.renamed;
}

function renameFlowDefs
[Pair<String FlowExpr>] ::= renameFn::(String ::= String) defs::[Pair<String FlowExpr>]
{
  return
    zipWith(
      pair,
      map(renameFn, map(fst, defs)),
      map(renameFlowExpr(renameFn, _), map(snd, defs)));
}

function subParamsFlowExpr
FlowExpr ::= params::[[FlowExpr]] lfe::FlowExpr
{
  lfe.parameters = params;
  return lfe.paramSubstituted;
}

function subParamsFlowDefs
[Pair<String FlowExpr>] ::= params::[[FlowExpr]] defs::[Pair<String FlowExpr>]
{
  return
    zipWith(
      pair,
      map(fst, defs),
      map(subParamsFlowExpr(params, _), map(snd, defs)));
}
