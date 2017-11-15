grammar edu:umn:ee5364project:exts:ableC:logic:abstractsyntax;

import silver:util:raw:treemap as tm;

type ChannelId = Integer;

nonterminal NANDFlowGraph with pp;

abstract production nandFlowGraph
top::NANDFlowGraph ::= gateConfig::NANDGates outputChannels::ChannelIds
{
  top.pp =
    ppConcat([
      terminate(line(), gateConfig.pps),
      text("return "), ppImplode(pp", ", outputChannels.pps), semi()]);
}

nonterminal NANDGates with pps;

abstract production consNANDGate
top::NANDGates ::= h::NANDGate t::NANDGates
{
  top.pps = h.pp :: t.pps;
}

abstract production nilNANDGate
top::NANDGates ::=
{
  top.pps = [];
}

nonterminal NANDGate with pp;

abstract production nandGate
top::NANDGate ::= channel::ChannelId input1::ChannelId input2::ChannelId
{
  top.pp = pp"${text(toString(channel))} = !(${text(toString(input1))} & ${text(toString(input2))});";
}

nonterminal ChannelIds with pps;

abstract production consChannelId
top::ChannelIds ::= h::ChannelId t::ChannelIds
{
  top.pps = text(toString(h)) :: t.pps;
}

abstract production nilChannelId
top::ChannelIds ::=
{
  top.pps = [];
}

function nandTranslateFlowGraph
NANDFlowGraph ::= numInputs::Integer flowGraph::FlowGraph
{
  flowGraph.nextChannelIn = numInputs;
  return
    nandFlowGraph(
      foldr(consNANDGate, nilNANDGate(), flowGraph.gateConfig),
      foldr(consChannelId, nilChannelId(), flowGraph.outputChannels));
}

synthesized attribute gateConfig::[NANDGate] with ++;
attribute gateConfig occurs on FlowGraph, FlowDefs, FlowDef, FlowExprs, FlowExpr;
synthesized attribute outputChannel::ChannelId occurs on FlowDef, FlowExpr;
synthesized attribute outputChannels::[ChannelId] occurs on FlowGraph, FlowExprs;

inherited attribute isNegated::Boolean occurs on FlowExpr;
autocopy attribute trueChannel::ChannelId occurs on FlowDefs, FlowDef, FlowExprs, FlowExpr;
autocopy attribute falseChannel::ChannelId occurs on FlowDefs, FlowDef, FlowExprs, FlowExpr;

synthesized attribute outputChannelContribs::[Pair<String ChannelId>] occurs on FlowDefs, FlowDef;
autocopy attribute outputChannelEnv::tm:Map<String ChannelId> occurs on FlowDefs, FlowDef, FlowExprs, FlowExpr;

inherited attribute nextChannelIn::ChannelId occurs on FlowGraph, FlowDefs, FlowDef, FlowExprs, FlowExpr;
synthesized attribute nextChannelOut::ChannelId occurs on FlowDefs, FlowDef, FlowExpr;

aspect production flowGraph
top::FlowGraph ::= name::String flowDefs::FlowDefs flowExprs::FlowExprs
{
  top.gateConfig := flowDefs.gateConfig ++ flowExprs.gateConfig;
  top.outputChannels = flowExprs.outputChannels;
  
  top.gateConfig <-
    [nandGate(top.nextChannelIn, 0, 0),
     nandGate(top.nextChannelIn + 1, top.nextChannelIn, 0),
     nandGate(top.nextChannelIn + 2, top.nextChannelIn + 1, top.nextChannelIn + 1)];
  flowDefs.trueChannel = top.nextChannelIn + 2;
  flowDefs.falseChannel = top.nextChannelIn + 1;
  flowExprs.trueChannel = flowDefs.trueChannel;
  flowExprs.falseChannel = flowDefs.falseChannel;
  
  flowDefs.outputChannelEnv = tm:empty(compareString);
  flowExprs.outputChannelEnv = tm:add(flowDefs.outputChannelContribs, flowDefs.outputChannelEnv);
  
  flowDefs.nextChannelIn = top.nextChannelIn + 3;
  flowExprs.nextChannelIn = flowDefs.nextChannelOut;
}

aspect production consFlowDef
top::FlowDefs ::= h::FlowDef t::FlowDefs
{
  top.gateConfig := h.gateConfig ++ t.gateConfig;
  
  top.outputChannelContribs = h.outputChannelContribs ++ t.outputChannelContribs;
  t.outputChannelEnv = tm:add(h.outputChannelContribs, top.outputChannelEnv);
  
  h.nextChannelIn = top.nextChannelIn;
  t.nextChannelIn = h.nextChannelOut;
  top.nextChannelOut = t.nextChannelOut;
}

aspect production nilFlowDef
top::FlowDefs ::= 
{
  top.gateConfig := [];
  
  top.outputChannelContribs = [];
  
  top.nextChannelOut = top.nextChannelIn;
}

aspect production flowDef
top::FlowDef ::= id::String e::FlowExpr
{
  top.gateConfig := e.gateConfig;
  top.outputChannel = e.outputChannel;
  e.isNegated = false;
  
  top.outputChannelContribs = [pair(id, e.outputChannel)];
  
  e.nextChannelIn = top.nextChannelIn;
  top.nextChannelOut = e.nextChannelOut;
}

aspect production consFlowExpr
top::FlowExprs ::= h::FlowExpr t::FlowExprs
{
  top.gateConfig := h.gateConfig ++ t.gateConfig;
  top.outputChannels = h.outputChannel :: t.outputChannels;
  h.isNegated = false;
  
  h.nextChannelIn = top.nextChannelIn;
  t.nextChannelIn = h.nextChannelOut;
}

aspect production nilFlowExpr
top::FlowExprs ::= 
{
  top.gateConfig := [];
  top.outputChannels = [];
}

aspect production constantFlowExpr
top::FlowExpr ::= b::Boolean
{
  top.gateConfig := [];
  top.outputChannel = if b != top.isNegated then top.trueChannel else top.falseChannel;
  
  top.nextChannelOut = top.nextChannelIn;
}

aspect production parameterFlowExpr
top::FlowExpr ::= i::Integer
{
  top.gateConfig := [];
  top.outputChannel = i;
  
  top.nextChannelOut = top.nextChannelIn;
}

aspect production nodeFlowExpr
top::FlowExpr ::= id::String
{
  top.gateConfig := [];
  top.outputChannel = head(tm:lookup(id, top.outputChannelEnv));
  
  top.nextChannelOut = top.nextChannelIn;
}

aspect production andFlowExpr
top::FlowExpr ::= e1::FlowExpr e2::FlowExpr
{
  top.gateConfig := e1.gateConfig ++ e2.gateConfig;
  top.gateConfig <- [nandGate(top.nextChannelIn, e1.outputChannel, e2.outputChannel)];
  top.gateConfig <-
    if !top.isNegated
    then [nandGate(top.nextChannelIn + 1, top.nextChannelIn, top.nextChannelIn)]
    else [];
  top.outputChannel = if top.isNegated then top.nextChannelIn else top.nextChannelIn + 1;
  e1.isNegated = false;
  e2.isNegated = false;
  
  e1.nextChannelIn = top.nextChannelIn;
  e2.nextChannelIn = e1.nextChannelOut;
  top.nextChannelOut = e2.nextChannelOut + if top.isNegated then 1 else 2;
}

aspect production orFlowExpr
top::FlowExpr ::= e1::FlowExpr e2::FlowExpr
{
  top.gateConfig := e1.gateConfig ++ e2.gateConfig;
  top.gateConfig <- [nandGate(top.nextChannelIn, e1.outputChannel, e2.outputChannel)];
  top.gateConfig <-
    if top.isNegated
    then [nandGate(top.nextChannelIn + 1, top.nextChannelIn, top.nextChannelIn)]
    else [];
  top.outputChannel = if top.isNegated then top.nextChannelIn else top.nextChannelIn + 1;
  e1.isNegated = true;
  e2.isNegated = true;
  
  e1.nextChannelIn = top.nextChannelIn;
  e2.nextChannelIn = e1.nextChannelOut;
  top.nextChannelOut = e2.nextChannelOut + if top.isNegated then 2 else 1;
}

aspect production notFlowExpr
top::FlowExpr ::= e::FlowExpr
{
  top.gateConfig := e.gateConfig;
  top.outputChannel = e.outputChannel;
  e.isNegated = !top.isNegated;
  
  e.nextChannelIn = top.nextChannelIn;
  top.nextChannelOut = e.nextChannelOut;
}
