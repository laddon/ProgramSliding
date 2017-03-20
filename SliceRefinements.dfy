datatype Statement = Assignment(LHS: seq<Variable>, RHS: seq<Expression>) | Skip | SeqComp(S1: Statement, S2: Statement) | 
		IF(B0: BooleanExpression, Sthen: Statement, Selse: Statement) | DO(B: BooleanExpression, Sloop: Statement) |
		LocalDeclaration(L: seq<Variable>, S0: Statement)
type Variable = string
datatype Value = Int(i: int) | Bool(b: bool)
type Expression = (State -> Value, set<Variable>)
type BooleanExpression = (State -> bool, set<Variable>) // State->Value,set<Variable>
type State = map<Variable, Value>
type Predicate = (State -> bool, set<Variable>)//string


predicate Valid(stmt: Statement) reads *
{
	match stmt {
		case Skip => true
		case Assignment(LHS,RHS) => ValidAssignments(LHS,RHS) 
		case SeqComp(S1,S2) => Valid(S1) && Valid(S2)
		case IF(B0,Sthen,Selse) => 
			(forall state: State :: B0.0.requires(state) /*&& B.0(state).Bool?*/) && 
			Valid(Sthen) && Valid(Selse)
		case DO(B,Sloop) =>
			(forall state: State :: B.0.requires(state) /*&& B.0(state).Bool?*/) && Valid(Sloop)
		case LocalDeclaration(L,S0) => Valid(S0)
	} &&
	forall state1: State, P: Predicate  :: P.0.requires(state1)

}

function ValidAssignments(LHS:  seq<Variable>, RHS: seq<Expression>) : bool 
{
	if (|LHS| != |RHS|) then false else true 
}
/*
method ValidAssignments(LHS:  seq<Variable>, RHS: seq<Expression>) returns (x: bool)
{
	if (|LHS| != |RHS|) {return false;} 
	var i: int := 0;
	x := true;
	while i < |LHS|
      invariant 0 <= i <= |LHS|
      decreases |LHS|-i
   {
      if (typeof(RHS[i]) == typeof(Expression))
		{
			if (typeof(LHS[i]) != typeof(Int))
			{return false;}
		}
		else
		{
			if (typeof(LHS[i]) != typeof(Bool))
				{return false;}
		}
   }

}
*/

/* here's how Leino expresses the fact that a function is total and it reads nothing from the heap
predicate IsTotal<A>(comparator: (A, A) -> bool)
  reads comparator.reads
{
  forall a,b :: comparator.reads(a,b) == {} && comparator.requires(a,b)
}
*/

// program,post-condition => wp
function wp(stmt: Statement, P: Predicate): Predicate
	reads Valid.reads(stmt)
	requires Valid(stmt)
	//requires stmt.LocalDeclaration? ==> vars(P) !! setOf(L)
{
	match stmt {
		case Skip => P
		case Assignment(LHS,RHS) => sub(P, LHS, RHS)
		case SeqComp(S1,S2) => wp(S1, wp(S2, P))
		case IF(B0,Sthen,Selse) => var f := (state: State)
			reads *
			requires B0.0.requires(state)
			requires Valid(Sthen) && wp(Sthen, P).0.requires(state)
			requires Valid(Selse) && wp(Selse, P).0.requires(state)
			=> /*B.0(state).Bool? && */
			(B0.0(state) ==> wp(Sthen, P).0(state)) && (!B0.0(state) ==> wp(Selse, P).0(state));
			(f,vars(P)-ddef(stmt)+input(stmt))
		case DO(B,Sloop) => var f:= (state: State)
			reads * //B.reads
			requires forall state1: State, P: Predicate  :: P.0.requires(state1)
			=>
				(var k: Predicate -> Predicate := Q
				=>
				var g := ((state: State)
						reads *
						requires Valid(Sloop)
						requires B.0.requires(state) /*&& B.0(state).Bool?*/
						requires wp(Sloop, Q).0.requires(state)
						requires P.0.requires(state)
					=>
					(B.0(state) || P.0(state)) && (!B.0(state) || wp(Sloop, Q).0(state)));
					(g,vars(Q)-ddef(stmt)+input(stmt));
				existsK(0, k, state));
				(f,vars(P)-ddef(stmt)+input(stmt))
					
		case LocalDeclaration(L,S0) => wp(S0,P)
	}
}

function existsK(i: nat, k: Predicate -> Predicate, state: State): bool
	reads *
	requires forall i: nat :: power.requires(k, i)
	requires forall i: nat, P: Predicate :: power(k, i).requires(P)
	requires forall state1: State, P: Predicate  :: P.0.requires(state1)
{
	var P := ((_ => false),(set v | v in state));
	exists i: nat :: power(k, i)(P).0(state)
}
/*
function power(k: (Predicate, State) -> bool, i: nat): (Predicate, State) -> bool
	decreases i
{
	if i == 0 then (Q: Predicate, state: State) requires Q.requires(state) => Q(state)
	else (Q: Predicate, state: State)
		requires power(k, i-1).requires(Q, state)
		requires k.requires(power(k, i-1)(Q, state))
		reads *
		=> k(power(k, i-1)(Q, state))
}
*/

function power<T>(f: T->T, i: nat): T->T
	decreases i
{
	if i == 0 then x => x
	else x
		requires power(f, i-1).requires(x)
		requires f.requires(power(f, i-1)(x))
		reads *
		=> f(power(f, i-1)(x))
}


function vars(P: Predicate): set<Variable> { P.1 } 

function sub(P: Predicate, X: seq<Variable>, E: seq<Expression>): Predicate
	requires |X| == |E|
{
	var f:= (state: State)
	reads *
	requires StateUpdate.requires(state, X, E, state)
	requires P.0.requires(StateUpdate(state, X, E, state))
	=>
		var newState := StateUpdate(state, X, E, state); 
		P.0(newState);
	(f,P.1 - setOf(X) + varsInExps(E))
}

function StateUpdate(oldState: State, X: seq<Variable>, E: seq<Expression>, newState: State): State
	requires |X| == |E|
	requires forall i: nat :: i < |E| ==> E[i].0.requires(oldState)
	reads *
{
	if |X| == 0 then newState else
	StateUpdate(oldState, X[1..], E[1..], newState[X[0] := E[0].0(oldState)])
}

function ConstantPredicate(b: bool): Predicate
{
	if b then ((_ => true),{})
	else ((_ => false),{})
}

method Main()
{
	print "try 1";
/*	var S : Statement;
	//S := FromString("i,sum,prod := i+1,sum+i,prod*i;");
	S := Assignment(["i","sum","prod"],[(s: State) => assume "i" in s && s["i"].Int?; Int(s["i"].i+1),(s: State) => assume "i" in s && "sum" in s && s["i"].Int? && s["sum"].Int?; Int(s["sum"].i+s["i"].i),(s: State) => assume "i" in s && "prod" in s && s["i"].Int? && s["prod"].Int?; Int(s["prod"].i*s["i"].i)]);
	var V := ["sum"];
	//ghost var allVars := glob(S);
	var S' := DuplicateStatement(S,V);
//	assert S' == LocalDeclaration(["isum"]+["ii","iprod"]+["fsum"],SeqComp(SeqComp(SeqComp(SeqComp(
//		SeqComp(Assignment(["isum"]+["ii","iprod"],V+["i","prod"]),S),Assignment(["fsum"],V)),Assignment(V+["i","prod"],["isum"]+["ii","iprod"])),S),Assignment(V,["fsum"])));
	var result := ToString(S');
	print(result);
	//assert result == "{ var isum,ii,iprod,fsum; isum,ii,iprod := sum,i,prod;i,sum,prod := i+1,sum+i,prod*i;fsum := sum;sum,i,prod := isum,ii,iprod;i,sum,prod := i+1,sum+i,prod*i;sum := fsum; } ";

	//flow-insensitive sliding:
	var SV: Statement, ScoV: Statement;
	S',SV,ScoV := FlowInsensitiveSliding(S,V);
	//assert S' == LocalDeclaration(["isum"]+["ii","iprod"]+["fsum"],SeqComp(SeqComp(SeqComp(SeqComp(
	//	SeqComp(Assignment(["isum"]+["ii","iprod"],V+["i","prod"]),SV),Assignment(["fsum"],V)),Assignment(V+["i","prod"],["isum"]+["ii","iprod"])),ScoV),Assignment(V,["fsum"])));
	//assert SV == Assignment(["sum"],["sum+i"]);
	//assert ScoV == Assignment(["i","prod"],["i+1","prod*i"]);
	result := ToString(ScoV);
	print(result);
	*/
}

// pretty printing...
function method ToString(S: Statement) : string
	//ensures ToString(S) == "i,sum,prod := i+1,sum+i,prod*i;";
{
	match S {
		case Assignment(LHS,RHS) => AssignmentToString(LHS,RHS)
		case Skip => ";"
		case SeqComp(S1,S2) => ToString(S1) + ToString(S2)
		case IF(B0,Sthen,Selse) => "if " + BooleanExpressionToString(B0) + " {" + ToString(Sthen) + " else " + ToString(Selse) + " } "
		case DO(B,Sloop) => "while (" + BooleanExpressionToString(B) + ") { " + ToString(Sloop) + " } "
		case LocalDeclaration(L,S0) => "{ var " + VariableListToString(L) + "; " + ToString(S0) + " } "
	}
}

function method BooleanExpressionToString(B: BooleanExpression) : string { "boolean expression... " } // TODO: implement

function method PredicateToString(P: Predicate) : string { "predicate " } // TODO: implement

function method AssignmentToString(LHS: seq<Variable>, RHS: seq<Expression>) : string
{
	VariableListToString(LHS) + " := " + ExpressionListToString(RHS) + ";"
}

function method VariableListToString(variables: seq<Variable>) : string
{
	if |variables| > 1 then
		variables[0] + "," + VariableListToString(variables[1..])
	else if |variables| > 0 then
		variables[0]
	else
		""
}

function method ExpressionListToString(expressions: seq<Expression>) : string
{
//	if |expressions| > 1 then
//		expressions[0] + "," + ExpressionListToString(expressions[1..])
//	else if |expressions| > 0 then
//		expressions[0]
//	else
//		""
	"expressions... "
}

// parsing...
/*function method FromString(str : string) : Statement
	//ensures ToString(FromString(str)) == str;
{
	if str == ";" then
		Skip
	else if |str| > 2 && str[..2] == "if " then
		IF(PredicateFromString("x == 0"),Skip,Skip) // FIXME parse recursively
	else if |str| > 6 && str[..6] == "while " then
		DO(PredicateFromString("x == 0"),Skip) // FIXME parse recursively
	else if |str| > 6 && str[..6] == "{ var " then
		LocalDeclaration([],Skip) // FIXME parse recursively
	else if exists i :: 0 <= i < |str| && str[i] == ';' then
		SeqComp(Skip,Skip) // FIXME parse recursively
	else // assert ValidAssignment(str)
		Assignment(["i","sum","prod"],["i+1","sum+i","prod*i"]) // FIXME parse LHS,RHS
}
*/
function method PredicateFromString(str: string): Predicate
{
	((state: map<Variable, Value>) => true,{})
}

predicate method ValidAssignment(str: string)
{
	true // check ":=" with same-length lists to its left and right, the former of distinct variable names and the right of expressions
}

/*
function method freshInit(vars : seq<Variable>, ghost allVars : set<Variable>) : seq<Variable>
	//requires |setOf(vars)| == |vars|;
	requires setOf(vars) < allVars;
	requires forall v :: v in vars ==> "i"+v !in allVars;
	ensures setOf(freshInit(vars,allVars)) !! allVars;
	ensures setOf(freshInit(vars,allVars)) !! allVars;
	ensures |freshInit(vars,allVars)| == |vars|;
{
	if vars == [] then [] else ["i"+vars[0]] + freshInit(vars[1..],allVars+{"i"+vars[0]})
}
*/
function method def(S: Statement) : set<Variable>
{
	match S {
		case Assignment(LHS,RHS) => setOf(LHS)
		case Skip => {}
		case SeqComp(S1,S2) => def(S1) + def(S2)
		case IF(B0,Sthen,Selse) => def(Sthen) + def(Selse)
		case DO(B,Sloop) => def(Sloop)
		case LocalDeclaration(L,S0) => def(S0) - setOf(L)
	}
}

function method ddef(S: Statement) : set<Variable>
{
	match S {
		case Assignment(LHS,RHS) => setOf(LHS)
		case Skip => {}
		case SeqComp(S1,S2) => ddef(S1) + ddef(S2)
		case IF(B0,Sthen,Selse) => ddef(Sthen) * ddef(Selse)
		case DO(B,S) => {}
		case LocalDeclaration(L,S0) => ddef(S0) - setOf(L)
	}
}

function input(S: Statement) : set<Variable>
{
	match S {
		case Assignment(LHS,RHS) => varsInExps(RHS) 
		case Skip => {}
		case SeqComp(S1,S2) => input(S1) + (input(S2) - ddef(S1)) 
		case IF(B0,Sthen,Selse) => B0.1 + input(Sthen) + input(Selse)
		case DO(B,S) => B.1 + input(S) 
		case LocalDeclaration(L,S0) => input(S0) - setOf(L)
	}
}



function glob(S: Statement) : set<Variable>
{
	set x | x in def(S) + input(S)
}

function method setOf(s: seq<Variable>) : set<Variable>
{
	set x | x in s
}

function method coVarSeq(xs: seq<Variable>, ys: seq<Variable>) : seq<Variable>
{
	if xs == [] then [] else if xs[0] in ys then coVarSeq(xs[1..],ys) else [xs[0]] + coVarSeq(xs[1..],ys)
}

function method isUniversallyDisjunctive(P: Predicate) : bool
{
	//TODO: implament if 
	true
}

function method varsInExps(exps: seq<Expression>): set<Variable>
{
	if exps == [] then {} else exps[0].1+varsInExps(exps[1..])
}

/*
method DuplicateStatement(S : Statement, V : seq<Variable>) returns (result : Statement)
	//requires ToString(S) == "i,sum,prod := i+1,sum+i,prod*i;";
	requires V == ["sum"];
	//requires setOf(V) < setOf(def(S));
//	ensures result == LocalDeclaration(["isum"]+["ii","iprod"]+["fsum"],SeqComp(SeqComp(SeqComp(SeqComp(
//		SeqComp(Assignment(["isum"]+["ii","iprod"],V+["i","prod"]),S),Assignment(["fsum"],V)),Assignment(V+["i","prod"],["isum"]+["ii","iprod"])),S),Assignment(V,["fsum"])));
	//ensures forall P: Predicate :: wp(S)(P) == wp(result)(P)
{
	var coV := ["i","prod"]; //coVarSeq(def(S),V);
	var iV := ["isum"]; // freshInit(V, allVars);
	var icoV := ["ii","iprod"]; //freshInit(coV, allVars);
	var fV := ["fsum"]; //freshInit(V, allVars);
	result := DS0(S,V,coV,iV,icoV,fV);
}

method DS0(S : Statement, V : seq<Variable>, coV : seq<Variable>, iV : seq<Variable>, icoV : seq<Variable>, fV : seq<Variable>) returns (result : Statement)
	//requires ToString(S) == "i,sum,prod := i+1,sum+i,prod*i;";
	requires V == ["sum"] && coV == ["i","prod"] && iV == ["isum"] && icoV == ["ii","iprod"] && fV == ["fsum"];
	requires |V| + |coV| + |iV| + |icoV| + |fV| == |V + coV + iV + icoV + fV|; // disjoint sets
	requires |V| == |iV| == |fV|;
	requires |coV| == |icoV|;
	//requires setOf(def(S)) == setOf(V+coV);
//	requires glob(S) == {"i","sum","prod"};
	requires setOf(iV) == {"isum"};
//	requires setOf(iV + icoV + fV) !! glob(S); // fresh variables
//	ensures result == LocalDeclaration(iV+icoV+fV,SeqComp(SeqComp(SeqComp(SeqComp(
//		SeqComp(Assignment(iV+icoV,V+coV),S),Assignment(fV,V)),Assignment(V+coV,iV+icoV)),S),Assignment(V,fV)));
{
	var S1 := DS1(S,V,coV,iV,icoV);
//	assert S1 == Assignment(iV+icoV,V+coV);//ToString(result) == "isum,ii,iprod := sum,i,prod;";
	result := S1;
//	assert result == Assignment(iV+icoV,V+coV);//ToString(result) == "isum,ii,iprod := sum,i,prod;";
	var S2 := DS2(S);
	assert S2 == S;
	result := SeqComp(result,S2);
	assert result == SeqComp(S1,S);
	var S3 := DS3(S,V,fV);
//	assert S3 == Assignment(fV,V);
	result := SeqComp(result,S3);
	assert result == SeqComp(SeqComp(S1,S2),S3);
	var S4 := DS4(S,V,coV,iV,icoV);
//	assert S4 == Assignment(V+coV,iV+icoV);
	result := SeqComp(result,S4);
	assert result == SeqComp(SeqComp(SeqComp(S1,S2),S3),S4);
	var S5 := DS5(S);
	assert S5 == S;
	result := SeqComp(result,S5);
	assert result == SeqComp(SeqComp(SeqComp(SeqComp(S1,S2),S3),S4),S5);
	var S6 := DS6(S,V,fV);
//	assert S6 == Assignment(V,fV);
	result := SeqComp(result,S6);
	assert result == SeqComp(SeqComp(SeqComp(SeqComp(SeqComp(S1,S2),S3),S4),S5),S6);
	result := LocalDeclaration(iV+icoV+fV,result);
	assert result == LocalDeclaration(iV+icoV+fV,SeqComp(SeqComp(SeqComp(SeqComp(SeqComp(S1,S2),S3),S4),S5),S6));
}

method DS1(S : Statement, V : seq<Variable>, coV : seq<Variable>, iV : seq<Variable>, icoV : seq<Variable>) returns (result : Statement)
	//requires ToString(S) == "i,sum,prod := i+1,sum+i,prod*i;";
	requires V == ["sum"] && coV == ["i","prod"] && iV == ["isum"] && icoV == ["ii","iprod"];
	requires |V| + |coV| + |iV| + |icoV| == |V + coV + iV + icoV|; // disjoint sets
	requires |V| == |iV|;
	requires |coV| == |icoV|;
	//requires setOf(def(S)) == setOf(V+coV);
	//requires (iV + icoV + fV) !! glob(S); // fresh variables
	//ensures ToString(result) == "isum,ii,iprod := sum,i,prod;";
//	ensures result == Assignment(iV+icoV,V+coV);
{
	//result := "isum,ii,iprod := sum,i,prod;";
	assert iV+icoV == ["isum","ii","iprod"];
	assert V+coV == ["sum","i","prod"];
	//result := Assignment(iV+icoV,ExpressionsFromVariables(V+coV));
//	result := Assignment(iV+icoV,V+coV);
}
/*
function method ExpressionsFromVariables(variables : seq<Variable>) : seq<Expression>
{
	if |variables| == 0 then [] else [variables[0]] + ExpressionsFromVariables(variables[1..])
}
*/
method DS2(S : Statement) returns (result : Statement)
	ensures result == S;
{
	result := S;
}

method DS3(S : Statement, V : seq<Variable>, fV : seq<Variable>) returns (result : Statement)
	//requires ToString(S) == "i,sum,prod := i+1,sum+i,prod*i;";
	//requires V == ["sum"] && fV == ["fsum"];
	requires |V| + |fV| == |V + fV|; // disjoint sets
	requires |V| == |fV|;
//	ensures result == Assignment(fV,V);
{
//	result := Assignment(fV,V);
}

method DS4(S : Statement, V : seq<Variable>, coV : seq<Variable>, iV : seq<Variable>, icoV : seq<Variable>) returns (result : Statement)
	//requires ToString(S) == "i,sum,prod := i+1,sum+i,prod*i;" && V == ["sum"] && coV == ["i","prod"] && iV == ["isum"] && icoV == ["ii","iprod"];
	requires |V| + |coV| + |iV| + |icoV| == |V + coV + iV + icoV|; // disjoint sets
	requires |V| == |iV|;
	requires |coV| == |icoV|;
	//requires setOf(def(S)) == setOf(V+coV);
	//requires (iV + icoV) !! glob(S); // fresh variables
//	ensures result == Assignment(V+coV,iV+icoV);
{
//	result := Assignment(V+coV,iV+icoV);
}

method DS5(S : Statement) returns (result : Statement)
	ensures result == S;
{
	result := S;
}

method DS6(S : Statement, V : seq<Variable>, fV : seq<Variable>) returns (result : Statement)
	//requires ToString(S) == "i,sum,prod := i+1,sum+i,prod*i;" && V == ["sum"] && fV == ["fsum"];
	requires |V| + |fV| == |V + fV|; // disjoint sets
	requires |V| == |fV|;
//	ensures result == Assignment(V,fV);
{
//	result := Assignment(V,fV);
}

method FlowInsensitiveSliding(S : Statement, V : seq<Variable>) returns (result : Statement, SV: Statement, ScoV: Statement)
	//requires ToString(S) == "i,sum,prod := i+1,sum+i,prod*i;"
	requires V == ["sum"]
	//requires setOf(V) < setOf(def(S))
	//ensures result == LocalDeclaration(["isum"]+["ii","iprod"]+["fsum"],SeqComp(SeqComp(SeqComp(SeqComp(
	//	SeqComp(Assignment(["isum"]+["ii","iprod"],V+["i","prod"]),SV),Assignment(["fsum"],V)),Assignment(V+["i","prod"],["isum"]+["ii","iprod"])),ScoV),Assignment(V,["fsum"])))
	//ensures SV == FlowInsensitiveSlice(S,setOf(V))
	//ensures ScoV == FlowInsensitiveSlice(S,def(S) - setOf(V))
{
	var coV := ["i","prod"]; //coVarSeq(def(S),V);
	var iV := ["isum"]; // freshInit(V, allVars);
	var icoV := ["ii","iprod"]; //freshInit(coV, allVars);
	var fV := ["fsum"]; //freshInit(V, allVars);
	SV := ComputeFISlice(S,setOf(V));
	ScoV := ComputeFISlice(S,setOf(coV));
	result := DS0(S,V,coV,iV,icoV,fV);
}

function FlowInsensitiveSlice(S: Statement, V: set<Variable>): Statement
	// FIXME: generalize
	//requires S == Assignment(["i","sum", "prod"],["i+1","sum+i","prod*i"])
{
//	if V == {"sum"} then Assignment(["sum"],["sum+i"])
//	else Assignment(["i","prod"],["i+1","prod*i"])
Skip
}

function method GetAssignmentsOfV(LHS : seq<Variable>, RHS : seq<Expression>, V: set<Variable>) : Statement
	//requires |LHS| == |RHS|
	ensures GetAssignmentsOfV(LHS, RHS, V).Assignment? || GetAssignmentsOfV(LHS, RHS, V).Skip?
	//ensures V * setOf(LHS) != {} ==> GetAssignmentsOfV(LHS, RHS, V).Assignment?
{
	if LHS == [] || RHS == [] then Skip
	else if LHS[0] in V then //assert V * setOf(LHS) != {};
	var tempRes := GetAssignmentsOfV(LHS[1..], RHS[1..], V);
	match tempRes {
		case Assignment(LHS1,RHS1) => Assignment([LHS[0]]+LHS1, [RHS[0]]+RHS1)
		case Skip => Assignment([LHS[0]], [RHS[0]])
	}
	else GetAssignmentsOfV(LHS[1..], RHS[1..], V)

	/*if LHS == [] then Skip
	else if LHS[0] in V then SeqComp(Assignment([LHS[0]],[RHS[0]]), GetAssignmentsOfV(LHS[1..], RHS[1..], V))
	else GetAssignmentsOfV(LHS[1..], RHS[1..], V)*/
}

function method ComputeSlides(S: Statement, V: set<Variable>) : Statement

{
	if V * def(S) == {} then Skip
	else
	match S {
		case Skip => Skip
		case Assignment(LHS,RHS) => GetAssignmentsOfV(LHS,RHS,V)
		case SeqComp(S1,S2) => SeqComp(ComputeSlides(S1,V), ComputeSlides(S2,V))
		case IF(B0,Sthen,Selse) => IF(B0, ComputeSlides(Sthen,V) , ComputeSlides(Selse,V))
		case DO(B,S) => DO(B, ComputeSlides(S,V))
		case LocalDeclaration(L,S0) => Skip
	}
}

function method ComputeSlidesDepRtc(S: Statement, V: set<Variable>) : set<Variable>
	decreases glob(S) - V
{
	var slidesSV := ComputeSlides(S, V);
	var U := glob(slidesSV) * def(S);

	if U <= V then V else ComputeSlidesDepRtc(S, V + U)
}


method ComputeFISlice(S: Statement, V: set<Variable>) returns (SV: Statement)
	//ensures SV == FlowInsensitiveSlice(S,V)
{
	var Vstar := ComputeSlidesDepRtc(S, V);

	SV := ComputeSlides(S, Vstar);
}*/


// *** Definitions ***

predicate EquivalentPredicates(P1: Predicate, P2: Predicate) reads *
{
	forall s: State :: P1.0.requires(s) && P2.0.requires(s) ==> P1.0(s) == P2.0(s)  
}

lemma EquivalentPredicatesLemma(P1: Predicate, P2: Predicate)
ensures EquivalentPredicates(P1,P2) <==> (forall s: State :: P1.0.requires(s) && P2.0.requires(s) ==> P1.0(s) == P2.0(s))

predicate EquivalentStatments(S1: Statement, S2: Statement)
	reads *
	requires Valid(S1)
	requires Valid(S2)
{
   forall P: Predicate :: EquivalentPredicates(wp(S1,P), wp(S2,P))
}

lemma EquivalentStatmentsLemma(S1: Statement, S2: Statement)
requires Valid(S1)
requires Valid(S2)
ensures EquivalentStatments(S1, S2) <==> (forall P: Predicate :: EquivalentPredicates(wp(S1,P), wp(S2,P)))


predicate Refinement(S1: Statement, S2: Statement)
	reads *
	requires Valid(S1)
	requires Valid(S2)
{
   forall P: Predicate,s: State :: (wp(S1,P).0(s) ==> wp(S2,P).0(s))
}

lemma RefinementLemma(S1: Statement, S2: Statement)
requires Valid(S1)
requires Valid(S2)
ensures Refinement(S1, S2) <==> (forall P: Predicate,s: State :: (wp(S1,P).0(s) ==> wp(S2,P).0(s)))

predicate SliceRefinement(S1: Statement, S2: Statement,V: set<Variable>)
	reads *
	requires Valid(S1)
	requires Valid(S2)
{
   forall P: Predicate,s: State :: (vars(P) <= V) ==> ((wp(S1,P).0(s) ==> wp(S2,P).0(s)))
}

lemma SliceRefinementLemma(S1: Statement, S2: Statement,V: set<Variable>)
requires Valid(S1)
requires Valid(S2)
ensures SliceRefinement(S1, S2, V) <==> (forall P: Predicate,s: State :: (vars(P) <= V) ==> ((wp(S1,P).0(s) ==> wp(S2,P).0(s))))


predicate CoSliceRefinement(S1: Statement, S2: Statement,V: set<Variable>)
	reads *
	requires Valid(S1)
	requires Valid(S2)
{
   forall P: Predicate,s: State :: (vars(P) !! V) ==> ((wp(S1,P).0(s) ==> wp(S2,P).0(s)))
}

lemma CoSliceRefinementLemma(S1: Statement, S2: Statement,V: set<Variable>)
requires Valid(S1)
requires Valid(S2)
ensures CoSliceRefinement(S1, S2, V) <==> (forall P: Predicate,s: State :: (vars(P) !! V) ==> ((wp(S1,P).0(s) ==> wp(S2,P).0(s))))


// *** Predicate Operators ***

function AND(P1: Predicate,P2: Predicate): Predicate
{
	((s: State) reads * requires P1.0.requires(s) && P2.0.requires(s) => P1.0(s) && P2.0(s),P1.1 + P2.1)
}

function OR(P1: Predicate,P2: Predicate): Predicate
{
	((s: State) reads * requires P1.0.requires(s) && P2.0.requires(s) => P1.0(s) || P2.0(s),P1.1 + P2.1)
}

function IMPLIES(P1: Predicate,P2: Predicate): Predicate  
{
	((s: State) reads * requires P1.0.requires(s) && P2.0.requires(s) => P1.0(s) ==> P2.0(s), P1.1 + P2.1) 
}

function NOT(P1: Predicate): Predicate  
{
	((s: State) reads * requires P1.0.requires(s) => !P1.0(s), P1.1)
}

// ******

lemma FinitelyConjunctive(S: Statement,P1: Predicate, P2: Predicate)
requires Valid(S)
ensures EquivalentPredicates(AND(wp(S,P1),wp(S,P2)),wp(S,AND(P1,P2)))

lemma IdentityOfAND(S: Statement,P1: Predicate)
requires Valid(S)
ensures EquivalentPredicates(wp(S,AND(P1,ConstantPredicate(true))),wp(S,P1))

lemma Leibniz<T>(f: Predicate->T, P1: Predicate, P2: Predicate)
requires EquivalentPredicates(P1,P2)
requires f.requires(P1) && f.requires(P2)
ensures f(P1) == f(P2)

lemma Leibniz2<S,T>(f: (S,Predicate)->T, P1: Predicate, P2: Predicate, s: S)
requires EquivalentPredicates(P1,P2)
requires f.requires(s,P1) && f.requires(s,P2)
ensures f(s,P1) == f(s,P2)

lemma ConjWp(S: Statement, P1: Predicate, P2: Predicate)
requires Valid(S)
ensures  EquivalentPredicates(wp(S,AND(P1,P2)),AND(wp(S,P1),wp(S,P2)))

lemma LocalDecStrangers(S: Statement,P: Predicate)
requires S.LocalDeclaration? 
ensures S.LocalDeclaration? ==> vars(P) !! setOf(S.L)

lemma LocalDecStrangers2(S: Statement,P: Predicate)
requires S.LocalDeclaration? 
ensures S.LocalDeclaration? ==> vars(P) - ddef(S.S0) + input(S.S0) == vars(P) - ddef(S) + input(S)

lemma Dummy(P: Predicate,LHS: seq<Variable>, RHS: seq<Expression>,s: State)
requires setOf(LHS) !! vars(P)
requires P.0.requires(s)
requires |LHS| == |RHS|
requires sub(P, LHS, RHS).0.requires(s)
ensures P.0(s) == sub(P, LHS, RHS).0(s)

lemma Equation_5_1(P: Predicate,V: set<Variable>)
ensures EquivalentPredicates(P,(((s1: State) reads * requires P.0.requires(s1) => exists p: State :: P.0.requires(p) && P.0(p) && forall v: Variable :: v in V ==> v in s1 && v in p && s1[v] == p[v]), P.1))

lemma Equation_5_2(S: Statement, Sco: Statement, V: set<Variable>)
requires Valid(S)
requires Valid(Sco)
ensures (forall s: State, v: Variable :: v in V && v in s ==> var P:= (((s1: State) reads *  => v in s1 && s1[v] == s[v]),{v}); (wp(S,P).0(s) ==> wp(Sco,P).0(s)))

// *** RE1-5 ***

function VarsOfPredicateSet(W: set<Predicate>): set<Variable>
{
	if W == {} then {} else var w :| w in W; w.1 + VarsOfPredicateSet(W-{w})
}

lemma {:verify true} RE1(S: Statement, W: set<Predicate>)
requires Valid(S)
ensures EquivalentPredicates( wp(S,((s1: State) reads * requires forall Q :: Q in W ==> Q.0.requires(s1) => exists P: Predicate :: P.0.requires(s1) && P.0(s1), VarsOfPredicateSet(W))), (((s1: State) reads * requires forall Q :: Q in W ==> Q.0.requires(s1) => exists P: Predicate :: P in W && wp.requires(S,P) && (wp(S,P)).0(s1), VarsOfPredicateSet(W))))

//EquivalentPredicates(wp(S,(((s1: State) reads * requires P.0.requires(s1) => exists p: State :: P.0.requires(p) && P.0(p) && P2(p).0(s1)), P.1)),(((s1: State) reads * requires P.0.requires(s1)=> exists p: State :: P.0.requires(p) && P.0(p) && wp.requires(S,P2(p)) && (wp(S,P2(p)).0(s1))),P.1);

//requires isUniversallyDisjunctive(wp(S,P))
//ensures isUniversallyDisjunctive(wp(SeqComp(L,S),P))
/*{
	// NEED TO UNDERSTAND THEN FIX
	/*calc{
		wp(SeqComp(L,S),P)
		== { L !! glob(P)}
		wp(S,P)
		== {proviso}
		(9P : P 2 Ps : wp.S.P)
		== {again, wp of locals}
		(9P : P 2 Ps : wp.“ |[var L ; S]| ”.P)
	}*/
}*/

lemma {:verify true} RE2( S: Statement,P: Predicate)
requires Valid(S)
ensures vars(wp(S,P)) <= vars(P) - ddef(S) + input(S)
{
	match S {
		case Assignment(LHS, RHS) =>  calc {
			vars(wp(S,P)); 
			== {/* wp of assignment */}
			vars(sub(P, LHS, RHS));
			<= {/* glob of normal sub */}
			vars(P)- setOf(LHS) + varsInExps(RHS);
			== {/* ddef of input of assignment */}
			vars(P)-ddef(S) + input(S);
		}
		case SeqComp(S1, S2) =>  calc {
			vars(wp(S,P)); 
			== {/* wp of SeqComp */ Leibniz(vars,wp(S,P),wp(S1,wp(S2,P)));}
			vars(wp(S1,wp(S2,P)));
			<= {RE2(S1,wp(S2,P));}
			vars(wp(S2,P)) - ddef(S1) + input(S1);
			<= {RE2(S2,P);}
			((vars(P) - ddef(S2)) + input(S2)) - ddef(S1) + input(S1);
			== {/* set theory: (a [ b) \ c = (a \ c) [ (b \ c) and (d \ e) \ f = d \ (e [ f ) */}
			(vars(P) - (ddef(S1) + ddef(S2))) + (input(S2) - ddef(S1)) + input(S1);
			== {/* ddef and input of SeqComp */}
			(vars(P) - ddef(SeqComp(S1,S2))) + input(SeqComp(S1,S2));
			== {/* definition of SeqComp */}
			(vars(P) - ddef(S)) + input(S);
		}
		case IF(B0, Sthen, Selse) => forall s:State { calc {
			vars(wp(S,P));
			== {/* IF definition */}
			vars(wp(IF(B0, Sthen, Selse),P));
			== {/* wp definitionof IF */Leibniz(vars,wp(IF(B0, Sthen, Selse),P),AND(IMPLIES(B0,wp(Sthen,P)), IMPLIES(NOT(B0),wp(Selse,P))));}
			vars(AND(IMPLIES(B0,wp(Sthen,P)), IMPLIES(NOT(B0),wp(Selse,P))));
			== {/* def. of glob; glob.B = glob.(¬B) */}
			B0.1 + vars(wp(Sthen,P)) + vars(wp(Selse,P));
			<= {/* proviso, twice */}
			B0.1 + (vars(P) - ddef(Sthen)) + input(Sthen) + (vars(P) - ddef(Selse)) + input(Selse);
			== {/* */}
			(vars(P) - ddef(Sthen)) + (vars(P) - ddef(Selse)) + input(Sthen) + input(Selse) + B0.1;
			== {/* set theory */}
			(vars(P) - (ddef(Sthen) /* common */* ddef(Selse))) + input(Sthen) + input(Selse) + B0.1;
			== {/* ddef and input of IF */}
			(vars(P) - ddef(IF(B0,Sthen,Selse))) + input(IF(B0,Sthen,Selse));
			== {/* IF definition */}
			vars(P) - ddef(S) + input(S);
		}
		}
		case DO(B,Sloop) => /* forall Q:Predicate { calc { 
			vars(wp(S,P));
			== {assert EquivalentPredicates(wp(S,P),AND(OR(B,P), OR(NOT(B), wp(Sloop, Q))));Leibniz(vars,wp(S,P),AND(OR(B,P), OR(NOT(B), wp(Sloop, Q))));} // maybe cuased by forall Q
			vars(AND(OR(B,P), OR(NOT(B), wp(Sloop, Q))));
			== {}
			vars(B) + vars(P) + vars(wp(Sloop, Q));
			<= {/*Proviso glob.(wp.S.Q) <= (glob.Q\ddef.S) + input.S */}
			vars(B) + vars(P) + (vars(Q) - ddef(Sloop)) + input(Sloop);
			<= {/*Set theory*/}
			vars(B) + vars(P) + vars(Q) + input(Sloop);
			<= {/*Proviso glob.Q <=  glob.P + glob.B + input.S*/}
			vars(B) + vars(P) + vars(B) + vars(P) + input(Sloop) + input(Sloop);
			== {/*Set theory*/}
			vars(B) + vars(P) + input(Sloop);
		}}*/		assume vars(wp(S,P)) <= vars(P) - ddef(S) + input(S);
		case Skip => calc {

		}
		case LocalDeclaration(L,S0) => calc {
			(vars(wp(S,P)));
			== {/* wp definition of LocalDeclaration */}
			vars(wp(S0,P)); 
			<= {RE2(S0,P);}
			(vars(P) - ddef(S0) + input(S0));
			== {LocalDecStrangers2(S,P);}
			(vars(P) - ddef(S) + input(S));
		} 
	}
}

lemma {:verify true} RE3( S: Statement,P: Predicate)
requires  def(S) !! vars(P)
requires Valid(S)
ensures EquivalentPredicates(wp(S,P), AND(P, wp(S,ConstantPredicate(true))))
{
   
	match S {
		case Skip => forall s: State { calc {
		wp(S,P).0(s);
		== {IdentityOfAND(S,P);}
		wp(S,AND(P,ConstantPredicate(true))).0(s);
		== {ConjWp(S, P, ConstantPredicate(true));}
		AND(wp(S,P),wp(S,ConstantPredicate(true))).0(s);
		== {/*def of wp*/}
		AND(P,wp(S,ConstantPredicate(true))).0(s);
		}
		}

		case SeqComp(S1, S2) => forall s: State { calc {
		wp(S,P).0(s);
		== {}
		wp(SeqComp(S1, S2),P).0(s);
		== {/* wp of SeqComp */}
		wp(S1, wp(S2, P)).0(s);
		== {assert def(S2) !! vars(P);RE3(S2,P); Leibniz2(wp,wp(S2, P),AND(P,wp(S2,ConstantPredicate(true))),S1);}
		wp(S1, AND(P,wp(S2,ConstantPredicate(true)))).0(s);
		== {/* wp(S1) is finitely conjunctive */ConjWp(S1, P, wp(S2,ConstantPredicate(true)));}
		AND(wp(S1,P),wp(S1,wp(S2,ConstantPredicate(true)))).0(s);
		== {assert def(S1) !! vars(P);}
		AND(AND(P,wp(S1,ConstantPredicate(true))),wp(S1,wp(S2,ConstantPredicate(true)))).0(s);
		== {}
		AND(P,AND(wp(S1,ConstantPredicate(true)),wp(S1,wp(S2,ConstantPredicate(true))))).0(s);
		== {/* finitely conjunctive */ConjWp(S1, ConstantPredicate(true),wp(S2,ConstantPredicate(true)));}
		AND(P,wp(S1,AND(ConstantPredicate(true),wp(S2,ConstantPredicate(true))))).0(s);
		== {/* identity element of ^ */assert def(S2) !! vars(ConstantPredicate(true));RE3(S2,ConstantPredicate(true));Leibniz2(wp,wp(S2, ConstantPredicate(true)),AND(ConstantPredicate(true),wp(S2,ConstantPredicate(true))),S1);}
		AND(P,wp(S1,wp(S2,ConstantPredicate(true)))).0(s);
		== {/* wp of SeqComp */}
		AND(P,wp(SeqComp(S1, S2),ConstantPredicate(true))).0(s);
		== {/* definition of SeqComp */}
		AND(P,wp(S,ConstantPredicate(true))).0(s);
		}
		}

		case IF(B0, Sthen, Selse) => forall s: State { calc {
			wp(S,P).0(s);
			== {/* IF definition */}
			wp(IF(B0, Sthen, Selse),P).0(s);
			== {/* wp definition of IF */}
			AND(IMPLIES(B0,wp(Sthen,P)),IMPLIES(NOT(B0),wp(Selse,P))).0(s);
			== {/*proviso: def(IF) !! vars(P) => def(Sthen) !! vars(P) */}
			AND(IMPLIES(B0,AND(P,wp(Sthen,ConstantPredicate(true)))),IMPLIES(NOT(B0),wp(Selse,P))).0(s);
			== {/*proviso: def(IF) !! vars(P) => def(Selse) !! vars(P) */}
			AND(IMPLIES(B0,AND(P,wp(Sthen,ConstantPredicate(true)))),IMPLIES(NOT(B0),AND(P,wp(Selse,ConstantPredicate(true))))).0(s);
			== {/* pred. calc.: [X => (Y && Z) == (X => Y) && (X => Z)] */}
			AND(AND(IMPLIES(B0,P),IMPLIES(B0,wp(Sthen,ConstantPredicate(true)))),IMPLIES(NOT(B0),AND(P,wp(Selse,ConstantPredicate(true))))).0(s);
			== {/* pred. calc.: [X => (Y && Z) == (X => Y) && (X => Z)] */}
			AND(AND(IMPLIES(B0,P),IMPLIES(B0,wp(Sthen,ConstantPredicate(true)))),AND(IMPLIES(NOT(B0),P),IMPLIES(NOT(B0),wp(Selse,ConstantPredicate(true))))).0(s);
			== {/* pred. calc.: [(A && B) && C == (A && C) && B] */}
			AND(AND(IMPLIES(B0,P),IMPLIES(NOT(B0),P)),AND(IMPLIES(B0,wp(Sthen,ConstantPredicate(true))),IMPLIES(NOT(B0),wp(Selse,ConstantPredicate(true))))).0(s);
			== {/* pred. calc.: [Y => Z) && (!Y => Z) == Z] */}
			AND(P,AND(IMPLIES(B0,wp(Sthen,ConstantPredicate(true))),IMPLIES(NOT(B0),wp(Selse,ConstantPredicate(true))))).0(s);
			== {/* wp definition of IF */}
			AND(P,wp(IF(B0,Sthen,Selse),ConstantPredicate(true))).0(s);
			== {/* IF definition */}
			AND(P,wp(S,ConstantPredicate(true))).0(s);
		}
		}

		case DO(B,Sloop) => /*forall s: State { calc {
		wp(S,P)(s);
		== {}
		AND(P, wp(S,ConstantPrdicate(true)))(s);
		}
		}*/
		assume EquivalentPredicates(wp(S,P), AND(P, wp(S,ConstantPredicate(true))));
		
		case LocalDeclaration(L,S0) => forall s: State { calc {
			wp(S,P).0(s);
			== {assert setOf(L) !! vars(P) by {LocalDecStrangers(S,P);}}
			wp(S0,P).0(s);
			== {assert vars(P) !! def(S0) by {assert def(S) !! vars(P);assert setOf(L) !! vars(P) by {LocalDecStrangers(S,P); }}RE3(S0,P);/**/}
			AND(P, wp(S0,ConstantPredicate(true))).0(s);
			== //{ vars(ConstantPrdicate(true)) = XX;} //TODO 26/11/16: pharse this
			AND(P, wp(S,ConstantPredicate(true))).0(s); 
		}
		}
		
		case Assignment(LHS, RHS) => forall s: State { calc {
		(AND(P,wp(S,ConstantPredicate(true)))).0(s);
		== {/* wp of assignment */}
		(AND(P,sub(ConstantPredicate(true), LHS, RHS))).0(s);
		== {assert setOf(LHS) !! vars(ConstantPredicate(true));}
		(AND(P,ConstantPredicate(true))).0(s);
		== {/* identity element of ^ */}
		P.0(s);
		== {assert setOf(LHS) !! vars(P);Dummy(P,LHS,RHS,s);}
		sub(P, LHS, RHS).0(s);
		== {/* wp of assignment */}
		wp(S,P).0(s);
		}
		}		
	}
}




lemma RE4(S: Statement)
//	requires ddef(S) <= def(S)
//	ensures S.LocalDeclaration? ==> ddef(S) <= def(S)

lemma RE5(S: Statement)
	//ensures S.LocalDeclaration? ==> vars(SeqComp(L,S)) == def(SeqComp(L,S)) + input(SeqComp(L,S))
/*{
	match S{
		case LocalDeclaration(L,S1) => calc{
			glob(S); 
			==
			glob(S1);
			== {/*glob of locals;*/}
			def(S1) + input(S1);
			== {/*def and input of locals*/}
			def(S) + input(S);
		}
	}
}
*/

// *** THEOREMS ***

lemma {:verify true} AbsorptionOfTermination3_14(P: Predicate,S: Statement)
	requires Valid(S)
	ensures EquivalentPredicates(AND(wp(S,P),wp(S,ConstantPredicate(true))) , wp(S,P));
{
	forall s:State {calc {
		AND(wp(S,P),wp(S,ConstantPredicate(true))).0(s);
		== {FinitelyConjunctive(S,P,ConstantPredicate(true));}
		wp(S,AND(P,ConstantPredicate(true))).0(s);
		== {IdentityOfAND(S,P);}
		wp(S,P).0(s);
	}	
	}
}

lemma {:verify true} Theorem_4_1(S: Statement, T: Statement) 
requires Valid(S)
requires Valid(T)
ensures (EquivalentStatments(S,T)) <==> ((Refinement(S,T)) && EquivalentPredicates(wp(S,ConstantPredicate(true)),wp(T,ConstantPredicate(true))))
{
	 calc {
		EquivalentStatments(S,T);
		== {EquivalentStatmentsLemma(S,T);}
		(forall P: Predicate ::EquivalentPredicates(wp(S,P), wp(T,P)));
		== {/*def. of program equivalence*/}
		(forall P: Predicate, s: State :: (wp(S,P).0(s) == wp(T,P).0(s)));
		== {Lemma_4_2(S,T);}
		(forall P: Predicate, s: State :: (wp(S,P).0(s) ==> wp(T,P).0(s))) && (EquivalentPredicates(wp(S,ConstantPredicate(true)),wp(T,ConstantPredicate(true))));
		== {/*pred. calc. (3.7): the range is non-empty}*/}
		(forall P: Predicate, s: State :: (wp(S,P).0(s) ==> wp(T,P).0(s))) && (EquivalentPredicates(wp(S,ConstantPredicate(true)),wp(T,ConstantPredicate(true))));
		== {RefinementLemma(S,T);}
		(Refinement(S,T)) && (EquivalentPredicates(wp(S,ConstantPredicate(true)),wp(T,ConstantPredicate(true))));
	}
}

lemma {:verify true} Lemma_4_2(S: Statement, T: Statement)
requires Valid(S)
requires Valid(T)
ensures (forall P: Predicate, s: State :: wp(S,P).0(s) == wp(T,P).0(s)) <==> (forall P: Predicate, s:State :: (wp(S,P).0(s) ==> wp(T,P).0(s)) && (EquivalentPredicates(wp(S,ConstantPredicate(true)),wp(T,ConstantPredicate(true)))))

/*TODO : Complete 3 err*/
lemma {:verify false} Theorem_5_1 (S: Statement, SV: Statement, V: set<Variable>)
requires Valid(S)
requires Valid(SV)
ensures SliceRefinement(S,SV,V) ==> (forall s: State :: ((wp(S,ConstantPredicate(true)).0(s) ==> wp(SV,ConstantPredicate(true)).0(s)))) && (forall s: State, v: Variable :: v in V && v in s ==> var P:= (((s1: State) reads *  => v in s1 && s1[v] == s[v]),{v}); (wp(S,P).0(s) ==> wp(SV,P).0(s)))
ensures SliceRefinement(S,SV,V) <==> (forall s: State :: ((wp(S,ConstantPredicate(true)).0(s) ==> wp(SV,ConstantPredicate(true)).0(s)))) && (forall s: State, v: Variable :: v in V && v in s ==> var P:= (((s1: State) reads *  => v in s1 && s1[v] == s[v]),{v}); (wp(S,P).0(s) ==> wp(SV,P).0(s)))
{
	forall s: State,P: Predicate | vars(P) <= V 
	{
		var P1 := (((s1: State) reads * requires P.0.requires(s1) => exists p: State :: P.0.requires(p) && P.0(p) && forall v: Variable :: v in V ==> v in s1 && v in p && s1[v] == p[v]), P.1);
		var P2 := (p: State) => (((s0:State)=>(forall v: Variable :: v in V ==> v in s0 && v in p && s0[v] == p[v])),P.1);
		var P3 := (((s1: State) reads * requires P.0.requires(s1)=> exists p: State :: P.0.requires(p) && P.0(p) && wp.requires(S,P2(p)) && (wp(S,P2(p)).0(s1))),P.1);
		calc{
		wp(S,P).0(s);
		== {Equation_5_1(P,V);assert EquivalentPredicates(P,P1);Leibniz2(wp,P,P1,S);}
		wp(S,P1).0(s);
		== {}
		wp(S,(((s1: State) reads * requires P.0.requires(s1) => exists p: State :: P.0.requires(p) && P.0(p) && forall v: Variable :: v in V ==> v in s1 && v in p && s1[v] == p[v]), P.1)).0(s);
		== {assert forall s1: State, p: State :: (forall v: Variable :: v in V ==> v in s1 && v in p && s1[v] == p[v]) == (P2(p).0(s1));
			var P4 := (((s1: State) reads * requires P.0.requires(s1) => exists p: State :: P.0.requires(p) && P.0(p) && forall v: Variable :: v in V ==> v in s1 && v in p && s1[v] == p[v]), P.1); 
			var P5 := (((s1: State) reads * requires P.0.requires(s1) => exists p: State :: P.0.requires(p) && P.0(p) && P2(p).0(s1)), P.1);
			assert EquivalentPredicates(P4,P5);
			Leibniz2(wp, P4,P5, S);}
		wp(S,(((s1: State) reads * requires P.0.requires(s1) => exists p: State :: P.0.requires(p) && P.0(p) && P2(p).0(s1)), P.1)).0(s);
		== { assert EquivalentPredicates(wp(S,(((s1: State) reads * requires P.0.requires(s1) => exists p: State :: P.0.requires(p) && P.0(p) && P2(p).0(s1)), P.1)),P3) by { RE1(S,{P/*2(p)*/});}} 
		//(((s1: State) reads * requires P.0.requires(s1) => exists p: State :: P.0.requires(p) && P.0(p) && wp.requires(S,P2(p)) && (wp(S,P2(p)).0(s1))), P.1).0(s);
		//=={}                                                                                              
		  P3.0(s);
		== {}
		(exists p: State :: P.0.requires(p) && P.0(p) && wp(S,((s0:State)=>(forall v: Variable :: v in V ==> v in s0 && v in p && s0[v] == p[v]),P.1)).0(s));
		}
	}
}

lemma {:verify true} Corollary_5_2 (S: Statement, SV: Statement, V: set<Variable>)
requires Valid(S)
requires Valid(SV)
ensures (CoSliceRefinement(S,SV,V)) ==> (((forall s: State :: ((wp(S,ConstantPredicate(true)).0(s) ==> wp(SV,ConstantPredicate(true)).0(s)))) && (forall s: State, v: Variable :: v in (def(S)+def(SV)-V) && v in s ==> var P:= (((s1: State) reads *  => v in s1 && s1[v] == s[v]),{v}); (wp(S,P).0(s) ==> wp(SV,P).0(s)))))
ensures (CoSliceRefinement(S,SV,V)) <== (((forall s: State :: ((wp(S,ConstantPredicate(true)).0(s) ==> wp(SV,ConstantPredicate(true)).0(s)))) && (forall s: State, v: Variable :: v in (def(S)+def(SV)-V) && v in s ==> var P:= (((s1: State) reads *  => v in s1 && s1[v] == s[v]),{v}); (wp(S,P).0(s) ==> wp(SV,P).0(s)))))
{
	calc {
	CoSliceRefinement(S,SV,V);
	== {Corollary_5_3(S,SV,V,(def(S) + def(SV)) - V);}
	SliceRefinement(S,SV,(def(S) + def(SV)) - V);
	== {Theorem_5_1(S,SV,(def(S) + def(SV)) - V);}
	((forall s:State :: ((wp(S,ConstantPredicate(true)).0(s) ==> wp(SV,ConstantPredicate(true)).0(s)))) && (forall s: State, v: Variable :: v in (def(S)+def(SV)-V) && v in s ==> var P:= (((s1: State) reads *  => v in s1 && s1[v] == s[v]),{v}); (wp(S,P).0(s) ==> wp(SV,P).0(s))));
	}
}

lemma {:verify true} Corollary_5_3 (S: Statement, SV: Statement, V: set<Variable>, CoV: set<Variable>)
requires Valid(S)
requires Valid(SV)
requires CoV == (def(S) + def(SV)) - V
ensures CoSliceRefinement(S,SV,V) == SliceRefinement(S,SV,CoV)
{
	calc
	{
	CoSliceRefinement(S,SV,V);
	== {Corollary_5_3Left(S,SV,V,CoV); Corollary_5_3Right(S,SV,V,CoV);}
	SliceRefinement(S,SV,CoV);
	}
}


lemma {:verify true} Corollary_5_3Left (S: Statement, SV: Statement, V: set<Variable>, CoV: set<Variable>)
requires Valid(S)
requires Valid(SV)
requires CoV == (def(S) + def(SV)) - V
ensures CoSliceRefinement(S,SV,V) ==> SliceRefinement(S,SV,CoV)
{
	calc{
		CoSliceRefinement(S,SV,V);
		==>  {}
		SliceRefinement(S,SV,CoV);
		}
}

/*TODO: Complete */
lemma {:verify false} Corollary_5_3Right (S: Statement, SV: Statement, V: set<Variable>, CoV: set<Variable>)
requires Valid(S)
requires Valid(SV)
requires CoV == (def(S) + def(SV)) - V
ensures CoSliceRefinement(S,SV,V) <== SliceRefinement(S,SV,CoV)
{
	forall s: State, P: Predicate{
		var CoV1 := vars(P) * CoV;
		var ND := vars(P) - CoV;
		var n1 := |CoV1|;
		var n2 := |vars(P)|;
		calc {
			wp(S,P).0(s);
			==> {}
			wp(SV,P).0(s);
		}
	}
}


/*TODO : Complete 4 err*/
lemma {:verify false} Corollary_5_4 (S: Statement, T: Statement, V: set<Variable>)
requires Valid(S)
requires Valid(T)
ensures Refinement(S,T) <==> SliceRefinement(S,T,V) && CoSliceRefinement(S,T,V)
{
		calc {
		Refinement(S,T);
		== {RefinementLemma(S,T);}
		(forall P: Predicate, s: State ::(wp(S,P).0(s) ==> wp(T,P).0(s)));
		== {/*def. of refinement; glob.P  ; holds for all P*/}
		(forall P: Predicate, s: State :: (vars(P) !! {}) ==> (wp(S,P).0(s) ==> wp(T,P).0(s)));
		== {CoSliceRefinementLemma(S,T,{});}
		CoSliceRefinement(S,T,{});
		== {Corollary_5_2 (S, T, {});} 
		((forall s: State :: ((wp(S,ConstantPredicate(true)).0(s) ==> wp(T,ConstantPredicate(true)).0(s)))) 
		&& (forall s: State ,v: Variable ,P: Predicate :: v in (def(S)+def(T)-{}) && v in P.1 ==> (wp(S,P).0(s) ==> wp(T,P).0(s))));
		== {}
		(forall s: State :: ((wp(S,ConstantPredicate(true)).0(s) ==> wp(T,ConstantPredicate(true)).0(s)))) 
		&& (forall s: State ,v: Variable ,P: Predicate :: v in (def(S)+def(T)) && v in P.1 ==> (wp(S,P).0(s) ==> wp(T,P).0(s)));
		== {/*(forall P: Predicate :: (vars(P) !! (V-def(S)+def(T)))); Corollary_5_5(S, T,P);*/}
		(forall s: State :: ((wp(S,ConstantPredicate(true)).0(s) ==> wp(T,ConstantPredicate(true)).0(s)))) 
		&& (forall s: State ,v: Variable ,P: Predicate :: v in (def(S)+def(T)) && v in P.1 ==> (wp(S,P).0(s) ==> wp(T,P).0(s)))
		&& (forall s: State ,v: Variable ,P: Predicate :: v in (V-(def(S)+def(T))) && v in P.1 ==> (wp(S,P).0(s) ==> wp(T,P).0(s)));
		== {/*merging the ranges*/}
		(forall s: State :: ((wp(S,ConstantPredicate(true)).0(s) ==> wp(T,ConstantPredicate(true)).0(s)))) 
		&& (forall s: State ,v: Variable ,P: Predicate :: v in (V+def(S)+def(T)) && v in P.1 ==> (wp(S,P).0(s) ==> wp(T,P).0(s)));
		== {/*splitting the range; pred. calc.*/}
		(forall s: State :: ((wp(S,ConstantPredicate(true)).0(s) ==> wp(T,ConstantPredicate(true)).0(s)))) 
		&& (forall s: State ,v: Variable ,P: Predicate :: v in (V) && v in P.1 ==> (wp(S,P).0(s) ==> wp(T,P).0(s)))
		&& (forall s: State ,v: Variable ,P: Predicate :: v in ((def(S)+def(T))-V) && v in P.1 ==> (wp(S,P).0(s) ==> wp(T,P).0(s)));
		== {/*splitting the range; pred. calc.*/}
		((forall s: State :: ((wp(S,ConstantPredicate(true)).0(s) ==> wp(T,ConstantPredicate(true)).0(s)))) 
		&& (forall s: State ,v: Variable ,P: Predicate :: v in (V) && v in P.1 ==> (wp(S,P).0(s) ==> wp(T,P).0(s))))
		&& ((forall s: State :: ((wp(S,ConstantPredicate(true)).0(s) ==> wp(T,ConstantPredicate(true)).0(s)))) 
		&& (forall s: State ,v: Variable ,P: Predicate :: v in ((def(S)+def(T))-V) && v in P.1 ==> (wp(S,P).0(s) ==> wp(T,P).0(s))));
		== {Theorem_5_1(S,T,V);}
		SliceRefinement(S,T,V) 
		&& ((forall s: State :: ((wp(S,ConstantPredicate(true)).0(s) ==> wp(T,ConstantPredicate(true)).0(s)))) 
		&& (forall s: State ,v: Variable ,P: Predicate :: v in ((def(S)+def(T))-V) && v in P.1 ==> (wp(S,P).0(s) ==> wp(T,P).0(s))));
		== {Corollary_5_2(S,T,V);}
		SliceRefinement(S,T,V) && CoSliceRefinement(S,T,V);
		}
}

lemma {:verify true} Corollary_5_5 (S: Statement, T: Statement, P:Predicate)
requires Valid(S)
requires Valid(T)
requires vars(P) !! (def(S) + def(T))
requires forall s:State :: (wp(S,ConstantPredicate(true))).0(s) ==> (wp(T,ConstantPredicate(true))).0(s)
ensures forall s:State :: (wp(S,P)).0(s) ==> (wp(T,P)).0(s)
{
	forall s:State {
		calc {
			wp(S,P).0(s);
			== {RE3(S,P);}
			AND(P,wp(S,ConstantPredicate(true))).0(s);
			== {}
			P.0(s) && wp(S,ConstantPredicate(true)).0(s);
			==> {assert forall s1:State :: IMPLIES(wp(S,ConstantPredicate(true)),wp(T,ConstantPredicate(true))).0(s1);}
			P.0(s) && wp(T,ConstantPredicate(true)).0(s);
			== {}
			AND(P,wp(T,ConstantPredicate(true))).0(s);
			== {RE3(T,P);}
			wp(T,P).0(s);
			}
	}
}


/*TODO : Complete 3 err */
lemma {:verify false} Corollary_5_6 (S: Statement, T: Statement, V: set<Variable>)
requires Valid(S)
requires Valid(T)
ensures EquivalentStatments(S,T) <==> (forall P: Predicate, s: State :: vars(P) <= V ==> wp(S, P).0(s) == wp(T, P).0(s))
&& (forall P: Predicate, s: State :: vars(P) !! V ==> wp(S, P).0(s) == wp(T, P).0(s))
{
		calc{
		EquivalentStatments(S,T);
		== {Theorem_4_1(S,T);}
		Refinement(S,T) && EquivalentPredicates(wp(S,ConstantPredicate(true)),wp(T,ConstantPredicate(true)));
		== {Corollary_5_4(S,T,V);}
		SliceRefinement(S,T,V) && CoSliceRefinement(S,T,V) && EquivalentPredicates(wp(S,ConstantPredicate(true)),wp(T,ConstantPredicate(true)));
		== {SliceRefinementLemma(S,T,V);}
		((forall P: Predicate, s: State :: vars(P) <= V ==> wp(S, P).0(s) ==> wp(T, P).0(s)) 
		&&  CoSliceRefinement(S,T,V) 
		&& EquivalentPredicates(wp(S,ConstantPredicate(true)),wp(T,ConstantPredicate(true))));
		== {CoSliceRefinementLemma(S,T,V);}
		((forall P: Predicate, s: State :: vars(P) <= V ==> wp(S, P).0(s) ==> wp(T, P).0(s)) 
		&&  (forall P: Predicate, s: State :: vars(P) !! V ==> wp(S, P).0(s) ==> wp(T, P).0(s)) 
		&& EquivalentPredicates(wp(S,ConstantPredicate(true)),wp(T,ConstantPredicate(true))));
		=={/*def. of slice-refinement and co-slice-refinement*/ /*pred. calc. ((3.7), twice): the ranges are non-empty*/}
		((forall P: Predicate, s: State :: vars(P) <= V ==> wp(S, P).0(s) ==> wp(T, P).0(s)) 
		&&  (forall P: Predicate, s: State :: vars(P) !! V ==> wp(S, P).0(s) ==> wp(T, P).0(s)) 
		&& EquivalentPredicates(wp(S,ConstantPredicate(true)),wp(T,ConstantPredicate(true)))
		&& EquivalentPredicates(wp(S,ConstantPredicate(true)),wp(T,ConstantPredicate(true))));
		=={/*def. of slice-refinement and co-slice-refinement*/ /*pred. calc. ((3.7), twice): the ranges are non-empty*/}
		(forall P: Predicate, s: State :: vars(P) <= V ==> wp(S, P).0(s) ==> wp(T, P).0(s))
		&& EquivalentPredicates(wp(S,ConstantPredicate(true)),wp(T,ConstantPredicate(true))) 
		&&  (forall P: Predicate, s: State :: vars(P) !! V ==> wp(S, P).0(s) ==> wp(T, P).0(s)) 
		&& EquivalentPredicates(wp(S,ConstantPredicate(true)),wp(T,ConstantPredicate(true)));
		=={/*def. of slice-refinement and co-slice-refinement*/ /*pred. calc. ((3.7), twice): the ranges are non-empty*/}
		((forall P: Predicate, s: State :: vars(P) <= V ==> wp(S, P).0(s) ==> wp(T, P).0(s))
		&& EquivalentPredicates(wp(S,ConstantPredicate(true)),wp(T,ConstantPredicate(true)))) 
		&&  ((forall P: Predicate, s: State :: vars(P) !! V ==> wp(S, P).0(s) ==> wp(T, P).0(s)) 
		&& EquivalentPredicates(wp(S,ConstantPredicate(true)),wp(T,ConstantPredicate(true))));
		== { Lemma_4_2(S, T);}
		(forall P: Predicate, s: State :: vars(P) <= V ==> wp(S, P).0(s) == wp(T, P).0(s)) 
		&&  ((forall P: Predicate, s: State :: vars(P) !! V ==> wp(S, P).0(s) ==> wp(T, P).0(s) 
		&& EquivalentPredicates(wp(S,ConstantPredicate(true)),wp(T,ConstantPredicate(true)))));
		== { Lemma_4_2(S, T);}
		(forall P: Predicate, s: State :: vars(P) <= V ==> wp(S, P).0(s) == wp(T, P).0(s)) 
		&&  (forall P: Predicate, s: State :: vars(P) !! V ==> wp(S, P).0(s) == wp(T, P).0(s));
		}
}

lemma {:verify true} ProgramEquivalence5_7 ( S1: Statement, S2: Statement)
	requires def(S1) !! def(S2)
	requires input(S1) !! def(S2)
	requires def(S1) !! input(S2)
	requires Valid(S1)
	requires Valid(S2)
    ensures EquivalentStatments(SeqComp(S1,S2),SeqComp(S2,S1))
{
	forall P: Predicate, s: State | vars(P) <= def(S1) {
		calc {
			wp(SeqComp(S1,S2), P).0(s);
			== {/*wp of ‘ ; ’*/}
			wp(S1,(wp(S2,P))).0(s);
			== {RE3(S2,P);Leibniz2(wp, wp(S2,P), AND(P, wp(S2,ConstantPredicate(true))), S1);}
			wp(S1, AND(P, wp(S2,ConstantPredicate(true)))).0(s);
			== {ConjWp(S1, P, wp(S2,ConstantPredicate(true)));}
			AND(wp(S1,P), wp(S1,(wp(S2,ConstantPredicate(true))))).0(s);
			== { var P1 := wp(S2,ConstantPredicate(true)); assert vars(P1) !! def(S1) by { assert vars(P1) <= input(S2) by { RE2(S2,ConstantPredicate(true)); assert vars(P1) <= vars(ConstantPredicate(true)) - ddef(S2) + input(S2); assert vars(ConstantPredicate(true)) - ddef(S2) + input(S2) <= input(S2) by { assert vars(ConstantPredicate(true)) == {}; }} assert def(S1) !! input(S2);} RE3(S1,P1); }
			AND(wp(S1,P),AND(wp(S2,ConstantPredicate(true)), wp(S1,ConstantPredicate(true)))).0(s);
			== {}
			AND(AND(wp(S1,P),wp(S1,ConstantPredicate(true))), wp(S2,ConstantPredicate(true))).0(s);
			== {AbsorptionOfTermination3_14(P,S1);}
			AND(wp(S1,P), wp(S2,ConstantPredicate(true))).0(s);
			/*== {}
			AND(wp(S2,ConstantPrdicate(true)), wp(S1,P)).0(s);*/
			== {var P1 := wp(S1,P); assert vars(P1) !! def(S2) by { assert vars(P1) <= vars(P) - ddef(S1) + input(S1) by { RE2(S1,P); } assert def(S2) !! (input(S1) + vars(P));} RE3(S2,P1); }
			(wp(S2,(wp(S1,P)))).0(s);
			== {/*wp of ‘ ; ’*/}
			wp(SeqComp(S2,S1), P).0(s);
		} 
	}
	forall P: Predicate, s: State | vars(P) !! def(S1) {
		calc {
			wp(SeqComp(S2,S1), P).0(s);
			==	{/*wp of ‘ ; ’*/}
			wp(S2,(wp(S1,P))).0(s);
			== {RE3(S1,P);Leibniz2(wp,wp(S1,P),AND(P,wp(S1,ConstantPredicate(true))),S2);}
			wp(S2,AND(P , wp(S1,ConstantPredicate(true)))).0(s);
			== {ConjWp(S2, P, wp(S1,ConstantPredicate(true)));}
			AND(wp(S2,P), wp(S2,(wp(S1,ConstantPredicate(true))))).0(s);
			== {var P1 := wp(S1,ConstantPredicate(true)); assert vars(P1) !! def(S2) by { assert vars(P1) <= input(S1) by { RE2(S1,ConstantPredicate(true)); } assert def(S2) !! input(S1) ;} RE3(S2,P1); }
			AND(wp(S2,P), AND(wp(S2,ConstantPredicate(true)), wp(S1,ConstantPredicate(true)))).0(s);
			== {}
			AND(AND(wp(S2,P), wp(S2,ConstantPredicate(true))), wp(S1,ConstantPredicate(true))).0(s);
			== {AbsorptionOfTermination3_14(P,S2);}
			AND(wp(S2,P), wp(S1,ConstantPredicate(true))).0(s);
			== {var P1 := wp(S2,P); assert vars(P1) !! def(S1) by { assert vars(P1) <= vars(P) - ddef(S2) + input(S2) by { RE2(S2,P); } assert def(S1) !! (input(S2) + vars(P));} RE3(S1,P1); }
			wp(S1,(wp(S2,P))).0(s);
			== {/*wp of ‘ ; ’*/}
			wp(SeqComp(S1,S2), P).0(s);
		}
	}
	assert EquivalentStatments(SeqComp(S1,S2),SeqComp(S2,S1)) by {Corollary_5_6 (SeqComp(S1,S2), SeqComp(S2,S1), def(S1));}
}
