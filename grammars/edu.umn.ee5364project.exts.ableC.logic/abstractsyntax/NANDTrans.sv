grammar edu:umn:ee5364project:exts:ableC:logic:abstractsyntax;

import silver:util:raw:treemap as tm;

type ChannelId = Integer;

synthesized attribute softHostInitTrans::Stmt; 

nonterminal NANDFlowGraph with pp, softHostInitTrans;

abstract production nandFlowGraph
top::NANDFlowGraph ::= gateConfig::NANDGates outputChannels::OutputChannels
{
  top.pp = terminate(line(), gateConfig.pps ++ outputChannels.pps);
  top.softHostInitTrans = seqStmt(gateConfig.softHostInitTrans, outputChannels.softHostInitTrans);
}

nonterminal NANDGates with pps, softHostInitTrans;

abstract production consNANDGate
top::NANDGates ::= h::NANDGate t::NANDGates
{
  top.pps = h.pp :: t.pps;
  top.softHostInitTrans = seqStmt(h.softHostInitTrans, t.softHostInitTrans);
}

abstract production nilNANDGate
top::NANDGates ::=
{
  top.pps = [];
  top.softHostInitTrans = nullStmt();
}

nonterminal NANDGate with pp, softHostInitTrans;

abstract production nandGate
top::NANDGate ::= channel::ChannelId input1::ChannelId input2::ChannelId
{
  top.pp = pp"${text(toString(channel))} = !(${text(toString(input1))} & ${text(toString(input2))});";
  top.softHostInitTrans =
    exprStmt(
      directCallExpr(
        name("soft_gate_config", location=builtin),
        foldExpr(map(mkIntConst(_, builtin), [channel, input1, input2])),
        location=builtin));
}

nonterminal OutputChannels with pps, softHostInitTrans;

abstract production consOutputChannel
top::OutputChannels ::= h::OutputChannel t::OutputChannels
{
  top.pps = h.pp :: t.pps;
  top.softHostInitTrans = seqStmt(h.softHostInitTrans, t.softHostInitTrans);
}

abstract production nilOutputChannel
top::OutputChannels ::=
{
  top.pps = [];
  top.softHostInitTrans = nullStmt();
}

nonterminal OutputChannel with pp, softHostInitTrans;

abstract production outputChannel
top::OutputChannel ::= output::ChannelId channel::ChannelId
{
  top.pp = pp"output ${text(toString(output))} = ${text(toString(channel))};";
  top.softHostInitTrans =
    exprStmt(
      directCallExpr(
        name("soft_output_config", location=builtin),
        foldExpr(map(mkIntConst(_, builtin), [output, channel])),
        location=builtin));
}

function makeNANDFlowGraph
NANDFlowGraph ::= gateConfig::[NANDGate] outputChannels::[OutputChannel]
{
  return
    nandFlowGraph(
      foldr(consNANDGate, nilNANDGate(), gateConfig),
      foldr(consOutputChannel, nilOutputChannel(), outputChannels));
}

synthesized attribute gateConfig::[NANDGate] with ++;
attribute gateConfig occurs on FlowGraph, FlowDefs, FlowDef, FlowExprs, FlowExpr;
synthesized attribute channel::ChannelId occurs on FlowDef, FlowExpr;
synthesized attribute outputChannels::[OutputChannel] occurs on FlowGraph, FlowExprs;

inherited attribute isNegated::Boolean occurs on FlowExpr;
autocopy attribute trueChannel::ChannelId occurs on FlowDefs, FlowDef, FlowExprs, FlowExpr;
autocopy attribute falseChannel::ChannelId occurs on FlowDefs, FlowDef, FlowExprs, FlowExpr;

synthesized attribute outputChannelContribs::[Pair<String ChannelId>] occurs on FlowDefs, FlowDef;
autocopy attribute outputChannelEnv::tm:Map<String ChannelId> occurs on FlowDefs, FlowDef, FlowExprs, FlowExpr;

inherited attribute nextChannelIn::ChannelId occurs on FlowGraph, FlowDefs, FlowDef, FlowExprs, FlowExpr;
synthesized attribute nextChannelOut::ChannelId occurs on FlowGraph, FlowDefs, FlowDef, FlowExprs, FlowExpr;

aspect production flowGraph
top::FlowGraph ::= name::String flowDefs::FlowDefs flowExprs::FlowExprs
{
  top.gateConfig := flowDefs.gateConfig ++ flowExprs.gateConfig;
  top.outputChannels = flowExprs.outputChannels;
  
  top.gateConfig <-
    [nandGate(top.nextChannelIn, 0, 0),
     nandGate(top.nextChannelIn + 1, top.nextChannelIn, 0),
     nandGate(top.nextChannelIn + 2, top.nextChannelIn + 1, top.nextChannelIn + 1)];
  flowDefs.trueChannel = top.nextChannelIn + 1;
  flowDefs.falseChannel = top.nextChannelIn + 2;
  flowExprs.trueChannel = flowDefs.trueChannel;
  flowExprs.falseChannel = flowDefs.falseChannel;
  
  flowDefs.outputChannelEnv = tm:empty(compareString);
  flowExprs.outputChannelEnv = tm:add(flowDefs.outputChannelContribs, flowDefs.outputChannelEnv);
  
  flowDefs.nextChannelIn = top.nextChannelIn + 3;
  flowExprs.nextChannelIn = flowDefs.nextChannelOut;
  top.nextChannelOut = flowExprs.nextChannelOut;
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
  top.channel = e.channel;
  e.isNegated = false;
  
  top.outputChannelContribs = [pair(id, e.channel)];
  
  e.nextChannelIn = top.nextChannelIn;
  top.nextChannelOut = e.nextChannelOut;
}

aspect production consFlowExpr
top::FlowExprs ::= h::FlowExpr t::FlowExprs
{
  top.gateConfig := h.gateConfig ++ t.gateConfig;
  top.outputChannels = outputChannel(top.position, h.channel) :: t.outputChannels;
  h.isNegated = false;
  
  h.nextChannelIn = top.nextChannelIn;
  t.nextChannelIn = h.nextChannelOut;
  top.nextChannelOut = t.nextChannelOut;
}

aspect production nilFlowExpr
top::FlowExprs ::= 
{
  top.gateConfig := [];
  top.outputChannels = [];
  
  top.nextChannelOut = top.nextChannelIn;
}

aspect production constantFlowExpr
top::FlowExpr ::= b::Boolean
{
  top.gateConfig := [];
  top.channel = if b != top.isNegated then top.trueChannel else top.falseChannel;
  
  top.nextChannelOut = top.nextChannelIn;
}

aspect production parameterFlowExpr
top::FlowExpr ::= i::Integer
{
  top.gateConfig := [];
  top.gateConfig <-
    if top.isNegated
    then [nandGate(top.nextChannelIn, i, i)]
    else [];
  top.channel = if top.isNegated then top.nextChannelIn else i;
  
  top.nextChannelOut = top.nextChannelIn + if top.isNegated then 1 else 0;
}

aspect production nodeFlowExpr
top::FlowExpr ::= id::String
{
  top.gateConfig := [];
  local refChannel::ChannelId = head(tm:lookup(id, top.outputChannelEnv));
  top.gateConfig <-
    if top.isNegated
    then [nandGate(top.nextChannelIn, refChannel, refChannel)]
    else [];
  top.channel = if top.isNegated then top.nextChannelIn else refChannel;
  
  top.nextChannelOut = top.nextChannelIn + if top.isNegated then 1 else 0;
}

aspect production andFlowExpr
top::FlowExpr ::= e1::FlowExpr e2::FlowExpr
{
  top.gateConfig := e1.gateConfig ++ e2.gateConfig;
  top.gateConfig <- [nandGate(e2.nextChannelOut, e1.channel, e2.channel)];
  top.gateConfig <-
    if !top.isNegated
    then [nandGate(e2.nextChannelOut + 1, e2.nextChannelOut, e2.nextChannelOut)]
    else [];
  top.channel = if top.isNegated then e2.nextChannelOut else e2.nextChannelOut + 1;
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
  top.gateConfig <- [nandGate(e2.nextChannelOut, e1.channel, e2.channel)];
  top.gateConfig <-
    if top.isNegated
    then [nandGate(e2.nextChannelOut + 1, e2.nextChannelOut, e2.nextChannelOut)]
    else [];
  top.channel = if !top.isNegated then e2.nextChannelOut else e2.nextChannelOut + 1;
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
  top.channel = e.channel;
  e.isNegated = !top.isNegated;
  
  e.nextChannelIn = top.nextChannelIn;
  top.nextChannelOut = e.nextChannelOut;
}
