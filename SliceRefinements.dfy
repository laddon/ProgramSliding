datatype Statement = Assignment(LHS: seq<Variable>, RHS: seq<Expression>) | Skip | SeqComp(S1: Statement, S2: Statement) | 
		IF(B0: BooleanExpression, Sthen: Statement, Selse: Statement) | DO(B: BooleanExpression, S: Statement) |
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
		case IF(B,Sthen,Selse) => 
			(forall state: State :: B.0.requires(state) /*&& B.0(state).Bool?*/) && 
			Valid(Sthen) && Valid(Selse)
		case DO(B,S) =>
			(forall state: State :: B.0.requires(state) /*&& B.0(state).Bool?*/) && Valid(S)
		case LocalDeclaration(L,S) => Valid(S)
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
		case IF(B,Sthen,Selse) => var f := (state: State)
			reads *
			requires B.0.requires(state)
			requires Valid(Sthen) && wp(Sthen, P).0.requires(state)
			requires Valid(Selse) && wp(Selse, P).0.requires(state)
			=> /*B.0(state).Bool? && */
			(B.0(state) ==> wp(Sthen, P).0(state)) && (!B.0(state) ==> wp(Selse, P).0(state));
			(f,vars(P)-ddef(stmt)+input(stmt))
		case DO(B,S) => var f:= (state: State)
			reads * //B.reads
			requires forall state1: State, P: Predicate  :: P.0.requires(state1)
			=>
				(var k: Predicate -> Predicate := Q
				=>
				var g := ((state: State)
						reads *
						requires Valid(S)
						requires B.0.requires(state) /*&& B.0(state).Bool?*/
						requires wp(S, Q).0.requires(state)
						requires P.0.requires(state)
					=>
					(B.0(state) || P.0(state)) && (!B.0(state) || wp(S, Q).0(state)));
					(g,vars(Q)-ddef(stmt)+input(stmt));
				existsK(0, k, state));
				(f,vars(P)-ddef(stmt)+input(stmt))
					
		case LocalDeclaration(L,S) => wp(S,P)
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

function ConstantPrdicate(b: bool): Predicate
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
		case DO(B,S) => "while (" + BooleanExpressionToString(B) + ") { " + ToString(S) + " } "
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
function method def(S: Statement) : set<Variable> // FIXME: make it return a set
//	ensures def(S) == {"i","sum","prod"};
{
	match S {
		case Assignment(LHS,RHS) => setOf(LHS) + varsInExps(RHS)// FIXME
		case Skip => {}
		case SeqComp(S1,S2) => def(S1) + def(S2)
		case IF(B0,Sthen,Selse) => def(Sthen) + def(Selse)
		case DO(B,S) => def(S)
		case LocalDeclaration(L,S0) => def(S0) - setOf(L)
	}
}

function method ddef(S: Statement) : set<Variable>
//	ensures ddef(S) == ["i","sum","prod"];
{
	match S {
		case Assignment(LHS,RHS) => setOf(LHS) // FIXME
		case Skip => {}
		case SeqComp(S1,S2) => ddef(S1) + ddef(S2)
		case IF(B0,Sthen,Selse) => ddef(Sthen) * ddef(Selse)
		case DO(B,S) => {}
		case LocalDeclaration(L,S0) => ddef(S0) - setOf(L)
	}
}

function input(S: Statement) : set<Variable>
//	ensures input(S) == ["i","sum","prod"];
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
	//ensures glob(S) == setOf(def(S) + input(S));
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




predicate EquivalentPredicates(P1: Predicate, P2: Predicate) reads *
{
	forall s: State :: P1.0.requires(s) && P2.0.requires(s) ==> P1.0(s) == P2.0(s)  
}
predicate EquivalentStatments(S1: Statement, S2: Statement)
	reads *
	requires Valid(S1)
	requires Valid(S2)
{
	//TODO: make the predicate work based on the definition of predicate: State => Bool
   forall P: Predicate :: wp(S1,P) == wp(S2,P)
}

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

/*function BooleanExpressionToPredicate(B0: BooleanExpression): Predicate
{
	if (B0.0(state).Bool??) then 
		(s: State) => (Prdicate)B0.0
	else if B0.0(state) !! 0 then 
		(s: State) => ConstantPrdicate(true)
	else (s: State) => ConstantPrdicate(false)
}
*/
lemma AbsorptionOfTermination3_14(P: Predicate,S: Statement)
	requires Valid(S)
	ensures EquivalentPredicates(AND(wp(S,P),wp(S,ConstantPrdicate(true))) , wp(S,P));
{
	forall s:State {calc {
		AND(wp(S,P),wp(S,ConstantPrdicate(true))).0(s);
		== {FinitelyConjunctive(S,P,ConstantPrdicate(true));}
		wp(S,AND(P,ConstantPrdicate(true))).0(s);
		== {IdentityOfAND(S,P);}
		wp(S,P).0(s);
	}	
	}
}

lemma FinitelyConjunctive(S: Statement,P1: Predicate, P2: Predicate)
	requires Valid(S)
	ensures EquivalentPredicates(AND(wp(S,P1),wp(S,P2)),wp(S,AND(P1,P2)))

lemma IdentityOfAND(S: Statement,P1: Predicate)
	requires Valid(S)
	//ensures EquivalentPredicates(AND(P1,ConstantPrdicate(true)),P1)
	ensures EquivalentPredicates(wp(S,AND(P1,ConstantPrdicate(true))),wp(S,P1))

lemma ProgramEquivalence5_7( S1: Statement, S2: Statement)
	//requires !S1.Skip?
	//requires !S2.Skip?
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
			== {RE3(S2,P);Leibniz2(wp, wp(S2,P), AND(P, wp(S2,ConstantPrdicate(true))), S1);}
			wp(S1, AND(P, wp(S2,ConstantPrdicate(true)))).0(s);
			== {ConjWp(S1, P, wp(S2,ConstantPrdicate(true)));}
			AND(wp(S1,P), wp(S1,(wp(S2,ConstantPrdicate(true))))).0(s);
			== { var P1 := wp(S2,ConstantPrdicate(true)); assert vars(P1) !! def(S1) by { assert vars(P1) <= input(S2) by { RE2(S2,ConstantPrdicate(true)); assert vars(P1) <= vars(ConstantPrdicate(true)) - ddef(S2) + input(S2); assert vars(ConstantPrdicate(true)) - ddef(S2) + input(S2) <= input(S2) by { assert vars(ConstantPrdicate(true)) == {}; }} assert def(S1) !! input(S2);} RE3(S1,P1); }
			AND(wp(S1,P),AND(wp(S2,ConstantPrdicate(true)), wp(S1,ConstantPrdicate(true)))).0(s);
			== {}
			AND(AND(wp(S1,P),wp(S1,ConstantPrdicate(true))), wp(S2,ConstantPrdicate(true))).0(s);
			== {AbsorptionOfTermination3_14(P,S1);}
			AND(wp(S1,P), wp(S2,ConstantPrdicate(true))).0(s);
			== {}
			AND(wp(S2,ConstantPrdicate(true)), wp(S1,P)).0(s);
			== {var P1 := wp(S1,P); assert vars(P1) !! def(S2) by { assert vars(P1) <= input(S1) by { RE2(S1,P); } assert def(S2) !! (input(S1) + vars(P));} RE3(S2,P1); }
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
			== {RE3(S1,P);Leibniz2(wp,wp(S1,P),AND(P,wp(S1,ConstantPrdicate(true))),S2);}
			wp(S2,AND(P , wp(S1,ConstantPrdicate(true)))).0(s);
			== {ConjWp(S2, P, wp(S1,ConstantPrdicate(true)));}
			AND(wp(S2,P), wp(S2,(wp(S1,ConstantPrdicate(true))))).0(s);
			== {var P1 := wp(S1,ConstantPrdicate(true)); assert vars(P1) !! def(S2) by { assert vars(P1) <= input(S1) by { RE2(S1,ConstantPrdicate(true)); } assert def(S2) !! input(S1) ;} RE3(S2,P1); }
			AND(wp(S2,P), AND(wp(S2,ConstantPrdicate(true)), wp(S1,ConstantPrdicate(true)))).0(s);
			== {}
			AND(AND(wp(S2,P), wp(S2,ConstantPrdicate(true))), wp(S1,ConstantPrdicate(true))).0(s);
			== {AbsorptionOfTermination3_14(P,S2);}
			AND(wp(S2,P), wp(S1,ConstantPrdicate(true))).0(s);
			== {var P1 := wp(S2,P); assert vars(P1) !! def(S1) by { assert vars(P1) <= input(S2) by { RE2(S2,P1); } assert def(S1) !! (input(S2) + vars(P));} RE3(S1,P1); }
			wp(S1,(wp(S2,P))).0(s);
			== {/*wp of ‘ ; ’*/}
			wp(SeqComp(S1,S2), P).0(s);
		}
	}
}


//TODO 1/12/16: RE1-5

//TODO 26/11/16:  -> define glob for predicates
//TODO 26/11/16:  -> define subtarct operator for setVaribale<>
//TODO 26/11/16:  -> define Union operator for setVaribale<>
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

lemma RE1(P: Predicate, S: Statement)
	requires Valid(S)
	requires isUniversallyDisjunctive(wp(S,P))
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

lemma RE2( S: Statement,P: Predicate)
	requires Valid(S)
	//requires S.LocalDeclaration? ==> setOf(L) !! vars(P)
	ensures vars(wp(S,P)) <= vars(P) - ddef(S) + input(S)
	//ensures S.LocalDeclaration? ==> vars(wp(SeqComp(L,S),P)) <= vars(P) - ddef(SeqComp(L,S)) + input(SeqComp(L,S))
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
		case DO(B,S1) => /* forall Q:Predicate { calc { 
			vars(wp(S,P));
			== {assert EquivalentPredicates(wp(S,P),AND(OR(B,P), OR(NOT(B), wp(S1, Q))));Leibniz(vars,wp(S,P),AND(OR(B,P), OR(NOT(B), wp(S1, Q))));} // maybe cuased by forall Q
			vars(AND(OR(B,P), OR(NOT(B), wp(S1, Q))));
			== {}
			vars(B) + vars(P) + vars(wp(S1, Q));
			<= {/*Proviso glob.(wp.S.Q) <= (glob.Q\ddef.S) + input.S */}
			vars(B) + vars(P) + (vars(Q) - ddef(S1)) + input(S1);
			<= {/*Set theory*/}
			vars(B) + vars(P) + vars(Q) + input(S1);
			<= {/*Proviso glob.Q <=  glob.P + glob.B + input.S*/}
			vars(B) + vars(P) + vars(B) + vars(P) + input(S1) + input(S1);
			== {/*Set theory*/}
			vars(B) + vars(P) + input(S1);
		}}*/		assume vars(wp(S,P)) <= vars(P) - ddef(S) + input(S);
		case Skip => calc {

		}
		case LocalDeclaration(L,S0) => /*calc {
			vars(wp(S,P));
			== {/* wp definition of LocalDeclaration */}
			vars(wp(S0,P));
			<=  {/*proviso and property of ‘\’*/} 
			vars(P) - ddef(S0) + input(S0);
			== {/*assert setOf(L) !! vars(P);*/}
			vars(P) - ddef(S) + input(S);
		} */ 
		assume vars(wp(S,P)) <= vars(P) - ddef(S) + input(S);
	}
}

lemma RE3( S: Statement,P: Predicate)
	//requires !S.Skip?
	requires  def(S) !! vars(P)
	requires Valid(S)
	ensures EquivalentPredicates(wp(S,P), AND(P, wp(S,ConstantPrdicate(true))))
   //ensures S.LocalDeclaration? ==> wp(S,P) == AND(P, wp(S,ConstantPrdicate(true)))
{
   
	match S {
		case Skip => forall s: State { calc {
		wp(S,P).0(s);
		== {IdentityOfAND(S,P);}
		wp(S,AND(P,ConstantPrdicate(true))).0(s);
		== {ConjWp(S, P, ConstantPrdicate(true));}
		AND(wp(S,P),wp(S,ConstantPrdicate(true))).0(s);
		== {/*def of wp*/}
		AND(P,wp(S,ConstantPrdicate(true))).0(s);
		}
		}
		case SeqComp(S1, S2) => forall s: State { calc {
		wp(S,P).0(s);
		== {}
		wp(SeqComp(S1, S2),P).0(s);
		== {/* wp of SeqComp */}
		wp(S1, wp(S2, P)).0(s);
		== {assert def(S2) !! vars(P);RE3(S2,P); Leibniz2(wp,wp(S2, P),AND(P,wp(S2,ConstantPrdicate(true))),S1);}
		wp(S1, AND(P,wp(S2,ConstantPrdicate(true)))).0(s);
		== {/* wp(S1) is finitely conjunctive */ConjWp(S1, P, wp(S2,ConstantPrdicate(true)));}
		AND(wp(S1,P),wp(S1,wp(S2,ConstantPrdicate(true)))).0(s);
		== {assert def(S1) !! vars(P);}
		AND(AND(P,wp(S1,ConstantPrdicate(true))),wp(S1,wp(S2,ConstantPrdicate(true)))).0(s);
		== {}
		AND(P,AND(wp(S1,ConstantPrdicate(true)),wp(S1,wp(S2,ConstantPrdicate(true))))).0(s);
		== {/* finitely conjunctive */ConjWp(S1, ConstantPrdicate(true),wp(S2,ConstantPrdicate(true)));}
		AND(P,wp(S1,AND(ConstantPrdicate(true),wp(S2,ConstantPrdicate(true))))).0(s);
		== {/* identity element of ^ */assert def(S2) !! vars(ConstantPrdicate(true));RE3(S2,ConstantPrdicate(true));Leibniz2(wp,wp(S2, ConstantPrdicate(true)),AND(ConstantPrdicate(true),wp(S2,ConstantPrdicate(true))),S1);}
		AND(P,wp(S1,wp(S2,ConstantPrdicate(true)))).0(s);
		== {/* wp of SeqComp */}
		AND(P,wp(SeqComp(S1, S2),ConstantPrdicate(true))).0(s);
		== {/* definition of SeqComp */}
		AND(P,wp(S,ConstantPrdicate(true))).0(s);
		}
		}
		case IF(B0, Sthen, Selse) => forall s: State { calc {
			wp(S,P).0(s);
			== {/* IF definition */}
			wp(IF(B0, Sthen, Selse),P).0(s);
			== {/* wp definition of IF */}
			AND(IMPLIES(B0,wp(Sthen,P)),IMPLIES(NOT(B0),wp(Selse,P))).0(s);
			== {/*proviso: def(IF) !! vars(P) => def(Sthen) !! vars(P) */}
			AND(IMPLIES(B0,AND(P,wp(Sthen,ConstantPrdicate(true)))),IMPLIES(NOT(B0),wp(Selse,P))).0(s);
			== {/*proviso: def(IF) !! vars(P) => def(Selse) !! vars(P) */}
			AND(IMPLIES(B0,AND(P,wp(Sthen,ConstantPrdicate(true)))),IMPLIES(NOT(B0),AND(P,wp(Selse,ConstantPrdicate(true))))).0(s);
			== {/* pred. calc.: [X => (Y && Z) == (X => Y) && (X => Z)] */}
			AND(AND(IMPLIES(B0,P),IMPLIES(B0,wp(Sthen,ConstantPrdicate(true)))),IMPLIES(NOT(B0),AND(P,wp(Selse,ConstantPrdicate(true))))).0(s);
			== {/* pred. calc.: [X => (Y && Z) == (X => Y) && (X => Z)] */}
			AND(AND(IMPLIES(B0,P),IMPLIES(B0,wp(Sthen,ConstantPrdicate(true)))),AND(IMPLIES(NOT(B0),P),IMPLIES(NOT(B0),wp(Selse,ConstantPrdicate(true))))).0(s);
			== {/* pred. calc.: [(A && B) && C == (A && C) && B] */}
			AND(AND(IMPLIES(B0,P),IMPLIES(NOT(B0),P)),AND(IMPLIES(B0,wp(Sthen,ConstantPrdicate(true))),IMPLIES(NOT(B0),wp(Selse,ConstantPrdicate(true))))).0(s);
			== {/* pred. calc.: [Y => Z) && (!Y => Z) == Z] */}
			AND(P,AND(IMPLIES(B0,wp(Sthen,ConstantPrdicate(true))),IMPLIES(NOT(B0),wp(Selse,ConstantPrdicate(true))))).0(s);
			== {/* wp definition of IF */}
			AND(P,wp(IF(B0,Sthen,Selse),ConstantPrdicate(true))).0(s);
			== {/* IF definition */}
			AND(P,wp(S,ConstantPrdicate(true))).0(s);
		}
		}
		case DO(B,S1) => /*forall s: State { calc {
		wp(S,P)(s);
		== {}
		AND(P, wp(S,ConstantPrdicate(true)))(s);
		}
		}*/
		assume EquivalentPredicates(wp(S,P), AND(P, wp(S,ConstantPrdicate(true))));
		case LocalDeclaration(L,S1) => forall s: State { calc {
			wp(S,P).0(s);
			== //{assert vars(P) !! setOf(L);}
			wp(S1,P).0(s);
			== //{assert def(S1) !! vars(P);}
			AND(P, wp(S1,ConstantPrdicate(true))).0(s);
			== //{ vars(ConstantPrdicate(true)) = XX;} //TODO 26/11/16: pharse this
			AND(P, wp(S,ConstantPrdicate(true))).0(s); 
		}
		}
		case Assignment(LHS, RHS) => forall s: State { calc {
		(AND(P,wp(S,ConstantPrdicate(true)))).0(s);
		== {/* wp of assignment */}
		(AND(P,sub(ConstantPrdicate(true), LHS, RHS))).0(s);
		== {assert setOf(LHS) !! vars(ConstantPrdicate(true));}
		(AND(P,ConstantPrdicate(true))).0(s);
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

lemma Dummy(P: Predicate,LHS: seq<Variable>, RHS: seq<Expression>,s: State)
requires setOf(LHS) !! vars(P)
requires P.0.requires(s)
requires |LHS| == |RHS|
requires sub(P, LHS, RHS).0.requires(s)
ensures P.0(s) == sub(P, LHS, RHS).0(s)

//TODO Lemma for vars(P) !! setOf(L)

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
function method isUniversallyDisjunctive(P: Predicate) : bool
{
	// implament if 
	true
}

function method varsInExps(exps: seq<Expression>): set<Variable>
{
	if exps == [] then {} else exps[0].1+varsInExps(exps[1..])
}
