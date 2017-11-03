grammar edu:umn:ee5364project:exts:ableC:logic:abstractsyntax;

import silver:util:raw:treemap as tm;

-- The flow computed for every bit of a logic expression
synthesized attribute logicFlowResult::[LogicFlowExpr];
synthesized attribute logicFlowResults::[[LogicFlowExpr]];
-- The flow computed for every named bit, used to build the overall flow graph
synthesized attribute logicFlowDefs::[Pair<String [LogicFlowExpr]>];

nonterminal LogicFlowGraph with pp, logicFlowDefs, logicFlowResult;

abstract production logicFlowGraph
top::LogicFlowGraph ::= logicFlowDefs::[Pair<String [LogicFlowExpr]>] logicFlowResult::[LogicFlowExpr]
{
  top.pp =
    ppImplode(
      line(),
      map(
        \ item::Pair<String [LogicFlowExpr]> ->
          pp"${text(item.fst)} = ${ppImplode(pp", ", map((.pp), item.snd))};",
        logicFlowDefs) ++
    [ppImplode(pp", ", map((.pp), logicFlowResult))]);
  top.logicFlowDefs = logicFlowDefs;
  top.logicFlowResult = logicFlowResult;

  local logicFlowEnv::tm:Map<String [Decorated LogicFlowExpr]> = tm:add(decLogicFlowDefs, tm:empty(compareString));
  production decLogicFlowDefs::[Pair<String [Decorated LogicFlowExpr]>] =
    zipWith(
      pair,
      map(fst, logicFlowDefs),
      map(map(decorateLogicFlowExpr(logicFlowEnv, _), _), map(snd, logicFlowDefs)));
  production decLogicFlow::[Decorated LogicFlowExpr] = map(decorateLogicFlowExpr(logicFlowEnv, _), logicFlowResult);
}

-- The complete flow graph that is provided to each element of the graph as a Map
autocopy attribute logicFlowEnv::tm:Map<String [Decorated LogicFlowExpr]>;

-- Functor and supporting attributes for function stitching
synthesized attribute renamed::LogicFlowExpr;
autocopy attribute renameFn::(String ::= String);

synthesized attribute paramSubstituted::LogicFlowExpr;
autocopy attribute parameters::[[LogicFlowExpr]];

nonterminal LogicFlowExpr with logicFlowEnv, renameFn, parameters, pp, renamed, paramSubstituted;
flowtype LogicFlowExpr = decorate {logicFlowEnv};

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
  top.pp = ppConcat([braces(text(toString(paramIndex))), brackets(text(toString(bitIndex)))]);
  top.paramSubstituted = head(drop(bitIndex, head(drop(paramIndex, top.parameters))));
}

abstract production nodeLogicFlowExpr
top::LogicFlowExpr ::= id::String bitIndex::Integer
{
  propagate paramSubstituted;
  top.pp = cat(text(id), brackets(text(toString(bitIndex))));
  top.renamed = nodeLogicFlowExpr(top.renameFn(id), bitIndex);
  
  production refNode::Decorated LogicFlowExpr =
    head(drop(bitIndex, head(tm:lookup(id, top.logicFlowEnv))));
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

function decorateLogicFlowExpr
Decorated LogicFlowExpr ::= logicFlowEnv::tm:Map<String [Decorated LogicFlowExpr]> lfe::LogicFlowExpr
{
  return decorate lfe with {logicFlowEnv = logicFlowEnv;};
}

function renameLogicFlowExpr
LogicFlowExpr ::= renameFn::(String ::= String) lfe::LogicFlowExpr
{
  lfe.renameFn = renameFn;
  return lfe.renamed;
}

function renameLogicFlowDefs
[Pair<String [LogicFlowExpr]>] ::= renameFn::(String ::= String) defs::[Pair<String [LogicFlowExpr]>]
{
  return
    zipWith(
      pair,
      map(renameFn, map(fst, defs)),
      map(map(renameLogicFlowExpr(renameFn, _), _), map(snd, defs)));
}

function subParamsLogicFlowExpr
LogicFlowExpr ::= params::[[LogicFlowExpr]] lfe::LogicFlowExpr
{
  lfe.parameters = params;
  return lfe.paramSubstituted;
}

function subParamsLogicFlowDefs
[Pair<String [LogicFlowExpr]>] ::= params::[[LogicFlowExpr]] defs::[Pair<String [LogicFlowExpr]>]
{
  return
    zipWith(
      pair,
      map(fst, defs),
      map(map(subParamsLogicFlowExpr(params, _), _), map(snd, defs)));
}
