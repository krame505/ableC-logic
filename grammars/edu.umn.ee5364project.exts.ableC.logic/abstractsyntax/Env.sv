grammar edu:umn:ee5364project:exts:ableC:logic:abstractsyntax;

-- Logic values
autocopy attribute logicValueEnv::Scopes<LogicValueItem>;
synthesized attribute logicValueDefs::Contribs<LogicValueItem>;

nonterminal LogicValueItem with logicType, sourceLocation;

abstract production logicValueItem
top::LogicValueItem ::= logicType::LogicType sourceLocation::Location
{
  top.logicType = logicType;
  top.sourceLocation = top.sourceLocation;
}

abstract production errorLogicValueItem
top::LogicValueItem ::=
{
  top.logicType = errorLogicType();
  top.sourceLocation = loc("nowhere", -1, -1, -1, -1, -1, -1);
}

-- Logic flow graphs for values
-- Seperate scope from logicValueItem to avoid flow dependancy
autocopy attribute logicFlowEnv::Scopes<[Decorated LogicFlowExpr]>;
synthesized attribute logicFlowDefs::Contribs<[Decorated LogicFlowExpr]>;

-- Logic functions
autocopy attribute logicFunctionEnv::Scopes<LogicFunctionItem>;
synthesized attribute logicFunctionDefs::Contribs<LogicFunctionItem>;

nonterminal LogicFunctionItem with parameterNames, parameterLogicTypes, returnLogicType, logicFlowGraph, sourceLocation;

abstract production logicFunctionItem
top::LogicFunctionItem ::= f::Decorated LogicFunctionDecl
{
  top.parameterNames = f.parameterNames;
  top.parameterLogicTypes = f.parameterLogicTypes;
  top.returnLogicType = f.returnLogicType;
  top.logicFlowGraph = f.logicFlowGraph;
  top.sourceLocation = f.sourceLocation;
}

abstract production errorLogicFunctionItem
top::LogicFunctionItem ::=
{
  top.parameterNames = [];
  top.parameterLogicTypes = [];
  top.returnLogicType = errorLogicType();
  top.logicFlowGraph = error("Demanded logic flow graph when function lookup failed"); -- No sensible default
  top.sourceLocation = loc("nowhere", -1, -1, -1, -1, -1, -1);
}

-- Global logic function env
synthesized attribute logicFunctions::Scopes<LogicFunctionItem> occurs on Env;
synthesized attribute logicFunctionContribs::Contribs<LogicFunctionItem> occurs on Defs, Def;

aspect production emptyEnv_i
top::Env ::=
{
  top.logicFunctions = emptyScope();
}
aspect production addEnv_i
top::Env ::= d::Defs  e::Decorated Env
{
  top.logicFunctions = addGlobalScope(gd.logicFunctionContribs, addScope(d.logicFunctionContribs, e.logicFunctions));
}
aspect production openEnvScope_i
top::Env ::= e::Decorated Env
{
  top.logicFunctions = openScope(e.logicFunctions);
}
aspect production globalEnv_i
top::Env ::= e::Decorated Env
{
  top.logicFunctions = globalScope(e.logicFunctions);
}

aspect production nilDefs
top::Defs ::=
{
  top.logicFunctionContribs = [];
}
aspect production consDefs
top::Defs ::= h::Def  t::Defs
{
  top.logicFunctionContribs = h.logicFunctionContribs ++ t.logicFunctionContribs;
}

aspect default production
top::Def ::=
{
  top.logicFunctionContribs = [];
}

abstract production logicFunctionDef
top::Def ::= s::String  t::LogicFunctionItem
{
  top.logicFunctionContribs = [pair(s, t)];
}

-- Logic function ValueItem
abstract production logicFunctionValueItem
top::ValueItem ::= env::Decorated Env  f::Decorated LogicFunctionDecl
{
  top.pp = text("LogicFunctionValueItem");

  top.typerep =
    functionType(
      logicTypeToHostType(env, f.returnLogicType),
      protoFunctionType(map(logicTypeToHostType(env, _), f.parameterLogicTypes), false),
      nilQualifier());
  top.sourceLocation = f.sourceLocation;

  top.directCallHandler = logicFunctionDirectCallExpr(_, _, location=_);
}

-- General convinence stuff with Name
attribute logicValueEnv, logicFunctionEnv, logicFlowEnv occurs on Name;

synthesized attribute logicValueRedeclarationCheck::[Message] occurs on Name;
synthesized attribute logicFunctionRedeclarationCheck::[Message] occurs on Name;

synthesized attribute logicValueLookupCheck::[Message] occurs on Name;
synthesized attribute logicFunctionLookupCheck::[Message] occurs on Name;

synthesized attribute logicValueItem::Decorated LogicValueItem occurs on Name;
synthesized attribute logicFunctionItem::Decorated LogicFunctionItem occurs on Name;
synthesized attribute logicFlowRef::[Decorated LogicFlowExpr] occurs on Name;

aspect production name
top::Name ::= n::String
{
  top.logicValueRedeclarationCheck =
    case lookupInLocalScope(n, top.logicValueEnv) of
    | [] -> []
    | v :: _ -> 
        [err(top.location, 
          "Redeclaration of " ++ n ++ ". Original (from line " ++
          toString(v.sourceLocation.line) ++ ")")]
    end;
  top.logicFunctionRedeclarationCheck =
    case lookupInLocalScope(n, top.logicFunctionEnv) of
    | [] -> []
    | v :: _ -> 
        [err(top.location, 
          "Redeclaration of " ++ n ++ ". Original (from line " ++
          toString(v.sourceLocation.line) ++ ")")]
    end;
    
  local logicValues::[LogicValueItem] = lookupScope(n, top.logicValueEnv);
  local logicFunctions::[LogicFunctionItem] = lookupScope(n, top.logicFunctionEnv);
  local logicFlowRefs::[[Decorated LogicFlowExpr]] = lookupScope(n, top.logicFlowEnv);
  top.logicValueLookupCheck =
    case logicValues of
    | [] -> [err(top.location, "Undeclared logic value " ++ n)]
    | _ :: _ -> []
    end;
  top.logicFunctionLookupCheck =
    case logicFunctions of
    | [] -> [err(top.location, "Undeclared logic function " ++ n)]
    | _ :: _ -> []
    end;
  
  local logicValue::LogicValueItem =
    if null(logicValues) then errorLogicValueItem() else head(logicValues);
  local logicFunction::LogicFunctionItem =
    if null(logicFunctions) then errorLogicFunctionItem() else head(logicFunctions);
  local logicFlowRef::[Decorated LogicFlowExpr] =
    if null(logicFunctions) then error("Demanded logic flow reference when lookup failed") else head(logicFlowRefs);
  top.logicValueItem = logicValue;
  top.logicFunctionItem = logicFunction;
  top.logicFlowRef = logicFlowRef;
}
