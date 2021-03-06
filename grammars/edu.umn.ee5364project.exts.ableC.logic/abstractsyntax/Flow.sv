grammar edu:umn:ee5364project:exts:ableC:logic:abstractsyntax;

-- The flow computed for every named bit, used to build the overall flow graph
synthesized attribute flowDefs::[FlowDef];
-- The flow computed for every bit of a logic expression
synthesized attribute flowExprs::[FlowExpr];

-- Used to build the flowEnv Map
synthesized attribute flowContribs::[Pair<String FlowExprItem>];

-- The flow graph provided to each element of the graph as a Map
autocopy attribute flowEnv::tm:Map<String FlowExprItem>;

-- Function application
synthesized attribute appliedFlowDefs::[FlowDef];
synthesized attribute appliedFlowExprs::[FlowExpr];

-- Functor and supporting attributes for function stitching
synthesized attribute applied<a>::a;
autocopy attribute callId::String; -- An identifier unique to each particular call
autocopy attribute arguments::[FlowExpr]; -- FlowExprs to substitute for all parameterFlowExprs
autocopy attribute renameFn::(String ::= String); -- Renaming function to apply on every node id in the graph
synthesized attribute hasParameters::Boolean; -- True if a parameterFlowExpr is contained

-- Graph simplification
autocopy attribute referenceEnv::tm:Map<String Unit>; -- Map that contains an entry for every time an id is referenced
synthesized attribute referenceEnvOut::tm:Map<String Unit>; -- referenceEnv passed up the FlowDefs tree
synthesized attribute simplified<a>::a; -- Collapse together nodes with only one reference, remove unused nodes
synthesized attribute canCollapse::Boolean; -- True if a def can be removed
synthesized attribute isSimple::Boolean; -- True if an expression may be duplicated without introducing extra logic
synthesized attribute referencedNodes::[String]; -- The list of nodes referenced in a logic expr or def

nonterminal FlowGraph with callId, arguments, pp, flowDefs, flowExprs, appliedFlowDefs, appliedFlowExprs, simplified<FlowGraph>;
flowtype FlowGraph = decorate {};

abstract production flowGraph
top::FlowGraph ::= name::String flowDefs::FlowDefs flowExprs::FlowExprs
{
  propagate simplified;
  top.pp =
    ppConcat([
      text(name), space(),
      braces(nestlines(2, ppConcat([terminate(line(), flowDefs.pps), pp"return ${ppImplode(pp", ", flowExprs.pps)};"])))]);
  top.flowDefs = flowDefs.flowDefs;
  top.flowExprs = flowExprs.flowExprs;
  
  flowExprs.position = 0;

  flowDefs.flowEnv = tm:empty(compareString);
  flowExprs.flowEnv = tm:add(flowDefs.flowContribs, flowDefs.flowEnv);
  
  -- Function application
  top.appliedFlowDefs = flowDefs.appliedFlowDefs;
  top.appliedFlowExprs = flowExprs.appliedFlowExprs;
  flowDefs.renameFn = \ n::String -> s"${name}_${n}_${top.callId}";
  flowExprs.renameFn = flowDefs.renameFn;
  
  -- Graph simplification
  flowDefs.referenceEnv =
    tm:add(map(pair(_, unit()), flowExprs.referencedNodes), tm:empty(compareString));
}

nonterminal FlowDefs with flowEnv, renameFn, arguments, referenceEnv, pps, flowDefs, flowContribs, appliedFlowDefs, hasParameters, simplified<FlowDefs>, referenceEnvOut;
flowtype FlowDefs = decorate {flowEnv, referenceEnv};

abstract production consFlowDef
top::FlowDefs ::= h::FlowDef t::FlowDefs
{
  top.pps = h.pp :: t.pps;
  top.flowDefs = h :: t.flowDefs;
  top.flowContribs = h.flowContribs ++ t.flowContribs;
  top.appliedFlowDefs = h.applied :: t.appliedFlowDefs;
  top.hasParameters = h.hasParameters || t.hasParameters;
  top.simplified = if h.canCollapse then t.simplified else consFlowDef(h.simplified, t.simplified);
  top.referenceEnvOut = tm:add(map(pair(_, unit()), h.referencedNodes), t.referenceEnvOut);
  
  t.flowEnv = tm:add(h.flowContribs, top.flowEnv);
  h.referenceEnv = t.referenceEnvOut;
}

abstract production nilFlowDef
top::FlowDefs ::= 
{
  propagate simplified;
  top.pps = [];
  top.flowDefs = [];
  top.flowContribs = [];
  top.appliedFlowDefs = [];
  top.hasParameters = false;
  top.referenceEnvOut = top.referenceEnv;
}

nonterminal FlowDef with flowEnv, renameFn, arguments, referenceEnv, pp, flowContribs, applied<FlowDef>, hasParameters, simplified<FlowDef>, canCollapse, referencedNodes;
flowtype FlowDef = decorate {flowEnv, referenceEnv};

abstract production flowDef
top::FlowDef ::= id::String e::FlowExpr
{
  propagate simplified;
  top.pp = pp"${text(id)} = ${e.pp};";
  top.flowContribs = [pair(id, flowExprItem(top.canCollapse, e))];
  top.applied = flowDef(top.renameFn(id), appliedFlowExpr(top.renameFn, top.arguments, e));
  top.hasParameters = e.hasParameters;
  local numReferences::Integer = length(tm:lookup(id, top.referenceEnv));
  top.canCollapse = e.simplified.isSimple || numReferences <= 1;
  top.referencedNodes = if numReferences > 0 then e.referencedNodes else [];
}

nonterminal FlowExprItem with canCollapse, simplified<FlowExpr>;

abstract production flowExprItem
top::FlowExprItem ::= canCollapse::Boolean e::Decorated FlowExpr
{
  top.canCollapse = canCollapse;
  top.simplified = e.simplified;
}

inherited attribute position::Integer; -- Initially 0

nonterminal FlowExprs with position, flowEnv, renameFn, arguments, pps, flowExprs, appliedFlowExprs, hasParameters, simplified<FlowExprs>, referencedNodes;
flowtype FlowExprs = decorate {position, flowEnv};

abstract production consFlowExpr
top::FlowExprs ::= h::FlowExpr t::FlowExprs
{
  propagate simplified;
  top.pps = h.pp :: t.pps;
  top.flowExprs = h :: t.flowExprs;
  top.appliedFlowExprs = appliedFlowExpr(top.renameFn, top.arguments, h) :: t.appliedFlowExprs;
  top.hasParameters = h.hasParameters || t.hasParameters;
  top.referencedNodes = h.referencedNodes ++ t.referencedNodes;
  
  t.position = top.position + 1;
}

abstract production nilFlowExpr
top::FlowExprs ::= 
{
  propagate simplified;
  top.pps = [];
  top.flowExprs = [];
  top.appliedFlowExprs = [];
  top.hasParameters = false;
  top.referencedNodes = [];
}

nonterminal FlowExpr with flowEnv, renameFn, arguments, pp, applied<FlowExpr>, hasParameters, simplified<FlowExpr>, referencedNodes, isSimple;
flowtype FlowExpr = decorate {flowEnv};

aspect default production
top::FlowExpr ::=
{
  top.isSimple = false;
}

-- Avoid performing extra successive renaming passes on an expression without parameters
abstract production appliedFlowExpr
top::FlowExpr ::= renameFn::(String ::= String) arguments::[FlowExpr] e::FlowExpr
{
  top.applied =
    if !e.hasParameters
    then appliedFlowExpr(\ s::String -> top.renameFn(renameFn(s)), top.arguments, e)
    else forward.applied;

  e.renameFn = renameFn;
  e.arguments = arguments;
  forwards to e.applied;
}

abstract production constantFlowExpr
top::FlowExpr ::= b::Boolean
{
  propagate applied, simplified;
  top.pp = if b then pp"true" else pp"false";
  top.hasParameters = false;
  top.referencedNodes = [];
  top.isSimple = true;
}

-- Invariant: A given parameter is only referenced in a flow graph at most once
abstract production parameterFlowExpr
top::FlowExpr ::= static::Boolean i::Integer
{
  propagate simplified;
  top.pp = cat(text(if static then "static_input" else "input"), brackets(text(toString(i))));
  top.applied =
    if static
    then error("Can't build flow graph for erroneous application of static logic function")
    else head(drop(i, top.arguments));
  top.hasParameters = true;
  top.referencedNodes = [];
  top.isSimple = false; -- NOT simple, since we don't know if what will be substituted in is simple
}

abstract production nodeFlowExpr
top::FlowExpr ::= id::String
{
  top.pp = text(id);
  top.applied = nodeFlowExpr(top.renameFn(id));
  
  production refNode::FlowExprItem =
    case tm:lookup(id, top.flowEnv) of
      [n] -> n
    | a :: b :: t -> error(s"Multiple definitions for flow node ${id}: ${hackUnparse(a :: b :: t)}")
    | [] -> error(s"Undefined flow node ${id}")
    end;
  top.simplified = if refNode.canCollapse then refNode.simplified else nodeFlowExpr(id);
  top.hasParameters = false;
  top.referencedNodes = [id];
  top.isSimple = true;
}

abstract production andFlowExpr
top::FlowExpr ::= e1::FlowExpr e2::FlowExpr
{
  propagate applied;
  top.pp = pp"(${e1.pp} & ${e2.pp})";
  top.hasParameters = e1.hasParameters || e2.hasParameters;
  top.simplified =
    case e1.simplified, e2.simplified of
      constantFlowExpr(false), _ -> constantFlowExpr(false)
    | _, constantFlowExpr(false) -> constantFlowExpr(false)
    | constantFlowExpr(true), s -> s
    | s, constantFlowExpr(true) -> s
    | notFlowExpr(s1), notFlowExpr(s2) -> notFlowExpr(orFlowExpr(s1, s2))
    | s1, s2 -> andFlowExpr(s1, s2)
    end;
  top.referencedNodes = e1.referencedNodes ++ e2.referencedNodes;
}

abstract production orFlowExpr
top::FlowExpr ::= e1::FlowExpr e2::FlowExpr
{
  propagate applied;
  top.pp = pp"(${e1.pp} | ${e2.pp})";
  top.hasParameters = e1.hasParameters || e2.hasParameters;
  top.simplified =
    case e1.simplified, e2.simplified of
      constantFlowExpr(false), s -> s
    | s, constantFlowExpr(false) -> s
    | constantFlowExpr(true), _ -> constantFlowExpr(true)
    | _, constantFlowExpr(true) -> constantFlowExpr(true)
    | notFlowExpr(s1), notFlowExpr(s2) -> notFlowExpr(andFlowExpr(s1, s2))
    | s1, s2 -> orFlowExpr(s1, s2)
    end;
  top.referencedNodes = e1.referencedNodes ++ e2.referencedNodes;
}

abstract production notFlowExpr
top::FlowExpr ::= e::FlowExpr
{
  propagate applied;
  top.pp = pp"(!${e.pp})";
  top.hasParameters = e.hasParameters;
  top.simplified =
    case e.simplified of 
      constantFlowExpr(b) -> constantFlowExpr(!b)
    | notFlowExpr(s) -> s
    | s -> notFlowExpr(s)
    end;
  top.referencedNodes = e.referencedNodes;
}

-- Flow constructor functions
function makeNegateFlowExprs
Pair<[FlowDef] [FlowExpr]> ::= logicFunctionEnv::Scopes<LogicFunctionItem> fes::[FlowExpr]
{
  return
    makeAddFlowExprs(
      logicFunctionEnv,
      map(notFlowExpr, fes),
      map(constantFlowExpr, repeat(false, length(fes) - 1) ++ [true]));
}

function makeAddFlowExprs
Pair<[FlowDef] [FlowExpr]> ::= logicFunctionEnv::Scopes<LogicFunctionItem> lhs::[FlowExpr] rhs::[FlowExpr]
{
  local halfAddFlowGraph::FlowGraph = head(lookupScope("halfAdd", logicFunctionEnv)).flowGraph;
  local fullAddFlowGraph::FlowGraph = head(lookupScope("fullAdd", logicFunctionEnv)).flowGraph;
  local buildAdder::(Pair<[FlowDef] [FlowExpr]> ::= [FlowExpr] [FlowExpr]) =
    \ lhs::[FlowExpr] rhs::[FlowExpr] ->
      case lhs, rhs of
        h1 :: t1, h2 :: t2 ->
          let rest::Pair<[FlowDef] [FlowExpr]> = buildAdder(t1, t2)
          in let applyRes::Pair<[FlowDef] [FlowExpr]> = applyFlowGraph(fullAddFlowGraph, [h1, h2, head(rest.snd)])
             in pair(rest.fst ++ applyRes.fst, applyRes.snd ++ tail(rest.snd))
             end
          end
      | [h1], [h2] -> applyFlowGraph(halfAddFlowGraph, [h1, h2])
      | _, _ -> error(s"Invalid adder inputs ${hackUnparse(lhs)} and ${hackUnparse(rhs)}")
      end;
  local adder::Pair<[FlowDef] [FlowExpr]> = buildAdder(lhs, rhs);
  return pair(adder.fst, tail(adder.snd)); -- Throw away the carry bit so output is the same width
}

function makeSubFlowExprs
Pair<[FlowDef] [FlowExpr]> ::= logicFunctionEnv::Scopes<LogicFunctionItem> lhs::[FlowExpr] rhs::[FlowExpr]
{
  local negateResult::Pair<[FlowDef] [FlowExpr]> = makeNegateFlowExprs(logicFunctionEnv, rhs);
  local addResult::Pair<[FlowDef] [FlowExpr]> = makeAddFlowExprs(logicFunctionEnv, lhs, negateResult.snd);
  return pair(negateResult.fst ++ addResult.fst, addResult.snd);
}

-- Utility functions
-- Construct a flow graph from lists of flow defs and flow exprs
function makeFlowGraph
FlowGraph ::= name::String flowDefs::[FlowDef] flowExprs::[FlowExpr]
{
  return
    flowGraph(
      name,
      foldr(consFlowDef, nilFlowDef(), flowDefs),
      foldr(consFlowExpr, nilFlowExpr(), flowExprs));
}

-- Get the lists of flow defs and flow exprs from applying a flow graph to input arguments
function applyFlowGraph
Pair<[FlowDef] [FlowExpr]> ::= flowGraph::FlowGraph arguments::[FlowExpr]
{
  flowGraph.callId = toString(genInt());
  flowGraph.arguments = arguments;
  return pair(flowGraph.appliedFlowDefs, flowGraph.appliedFlowExprs);
}
