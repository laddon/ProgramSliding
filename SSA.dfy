datatype Statement = Assignment(LHS : seq<Variable>, RHS : seq<Expression>) | Skip | SeqComp(S1 : Statement, S2 : Statement) | 
		IF(B0 : BooleanExpression, Sthen : Statement, Selse : Statement) | DO(B : BooleanExpression, S : Statement) |
		LocalDeclaration(L : seq<Variable>, S0 : Statement)
type Variable = string
type Expression = string
type BooleanExpression = string

class VariablesSSA {

	var m: map<Variable, seq<Variable>>;
	var n: int;

	constructor ()
		modifies this
		requires ValidVsSSA(this)
		ensures ValidVsSSA(this)
	{
		n := 1;
	}

	method getAndIncN() returns (res: int)
		modifies this
		requires ValidVsSSA(this)
		requires n >= 1
		ensures n == old(n)+1
		ensures res >= 1
		ensures res == old(n)
		ensures ValidVsSSA(this)
		ensures m == old(m)
	{
		res := n;
		n := n + 1;
	}

	method variablesToSSAVariables(variables: seq<Variable>, instances: seq<Variable>)
		requires forall v :: v in m ==> |m[v]| >= 1
		requires ValidVsSSA(this)
		requires |instances| == |variables|
		modifies this
		ensures ValidVsSSA(this)
		ensures forall i :: i in instances ==> existsVariable(i)
		ensures forall v :: v in old(m) ==> v in m && (forall i :: i in old(m[v]) ==> i in m[v])
		ensures forall v :: v in m ==> |m[v]| >= 1
	{
		if !(variables == [])
		{
			var a := addVariable(variables[0], instances[0]);
			assert existsVariable(instances[0]);
			variablesToSSAVariables(variables[1..], instances[1..]);
		}
	}

	/*method addVariable(v: Variable, vSSA: Variable)
		requires ValidVsSSA(this)
		modifies this
		ensures ValidVsSSA(this)
	{
		if v in m { m := m[v := m[v] + [vSSA]]; } else { m := m[v := [vSSA]]; }
	}*/

	method addVariable(v: Variable, vSSA: Variable) returns (res: seq<Variable>)
		requires forall v :: v in m ==> |m[v]| >= 1
		requires ValidVsSSA(this)
		modifies this
		ensures ValidVsSSA(this)
		ensures vSSA in res && existsVariable(vSSA)
		//ensures addVariableP(v, vSSA, old(m), res)
		ensures v in m && (v in old(m) ==> forall i :: i in old(m[v]) ==> i in m[v])
		//ensures forall v' :: v' in old(m) && v' != v ==> v' in m && (v' in old(m) ==> forall i :: i in old(m[v']) ==> i in m[v'])
		ensures forall v' :: v' in old(m) && v' != v ==> v' in m && old(m[v']) == m[v']
		ensures forall v :: v in m ==> |m[v]| >= 1
	{
		if v in m
		{
			res := addExistingVariable(v, vSSA);
		}
		else
		{
			res := addNewVariable(v, vSSA);
		}
	}

	predicate addVariableP(v: Variable, vSSA: Variable, oldM: map<Variable, seq<Variable>>, res: seq<Variable>)
		reads this
	{
		if (v in oldM) then res == oldM[v] + [vSSA]  else  res == [vSSA]
	}

	method addExistingVariable(v: Variable, vSSA: Variable) returns (res: seq<Variable>)
		requires forall v :: v in m ==> |m[v]| >= 1
		requires ValidVsSSA(this)
		requires v in m 
		modifies this
		ensures ValidVsSSA(this)
		ensures vSSA in res && existsVariable(vSSA)
		//ensures res == old(m[v]) + [vSSA]
		ensures v in m && (forall i :: i in old(m[v]) ==> i in m[v])
		//ensures forall v' :: v' in old(m) && v' != v ==> v' in m && (v' in old(m) ==> forall i :: i in old(m[v']) ==> i in m[v'])
		ensures forall v' :: v' in old(m) && v' != v ==> v' in m && old(m[v']) == m[v']
		ensures forall v :: v in m ==> |m[v]| >= 1
	{
		m := m[v := m[v] + [vSSA]];
		res := m[v];
	}

	method addNewVariable(v: Variable, vSSA: Variable) returns (res: seq<Variable>)
		requires forall v :: v in m ==> |m[v]| >= 1
		requires ValidVsSSA(this)
		requires v !in m
		modifies this
		ensures ValidVsSSA(this)
		ensures vSSA in res && existsVariable(vSSA)
		//ensures res == [vSSA]
		ensures v in m 
		//ensures forall v' :: v' in old(m) && v' != v ==> v' in m && (v' in old(m) ==> forall i :: i in old(m[v']) ==> i in m[v'])
		ensures forall v' :: v' in old(m) && v' != v ==> v' in m && old(m[v']) == m[v']
		ensures forall v :: v in m ==> |m[v]| >= 1
	{
		m := m[v := [vSSA]];
		res := m[v];
	}

	method getVariableInRegularForm(vSSA: Variable)  returns (v : Variable)
		requires ValidVsSSA(this)
		requires existsVariable(vSSA)
		ensures ValidVsSSA(this)
	{
		v :| v in m && vSSA in m[v]; 
	}

	predicate existsVariable(vSSA: Variable)
		reads this
		requires ValidVsSSA(this)
		ensures ValidVsSSA(this)
	{
		exists v :: v in m && vSSA in m[v]
	}

	method instancesToVariables(instances: seq<Variable>) returns (V : seq<Variable>)
		requires ValidVsSSA(this)
		requires forall i :: i in instances ==> existsVariable(i)
		ensures |instances| == |V|
		ensures ValidVsSSA(this)
		
	{
		if instances == [] { V := []; } 
		else { 
			var v := getVariableInRegularForm(instances[0]);
			var V' := instancesToVariables(instances[1..]);

			V := [v] + V';
		}
	}

	predicate existsInstance(v: Variable)
		reads this
		//requires ValidVsSSA(this)
		//ensures ValidVsSSA(this)
	{
		v in m && |m[v]| >= 1
	}

	method getInstancesOfVarible(v : Variable) returns (instances : seq<Variable>)
		requires ValidVsSSA(this)
		requires existsInstance(v)
		ensures |instances| >= 1
		ensures ValidVsSSA(this)
		ensures forall i :: i in instances ==> existsVariable(i)
	{
		instances := m[v];
	}

	method getInstancesOfVaribleSeq(V : seq<Variable>) returns (instances : seq<Variable>)
		requires ValidVsSSA(this)
		requires forall v :: v in V ==> existsInstance(v)
		ensures ValidVsSSA(this)
		ensures forall i :: i in instances ==> existsVariable(i)
	{
		if V == [] { instances := []; }
		else {
			var vInstaces := getInstancesOfVarible(V[0]);
			var instances' := getInstancesOfVaribleSeq(V[1..]);
			instances := vInstaces + instances';
		}
	}

	function getAllInstances(allVars: seq<Variable>) : seq<Variable>
		reads this
		requires forall v :: v in allVars ==> v in m
	{
		if (allVars == []) then [] else m[allVars[0]] + getAllInstances(allVars[1..])
	}
}

method Main()
{
	print "hello!";

}


predicate method ValidAssignment(str : string)
{
	true // check ":=" with same-length lists to its left and right, the former of distinct variable names and the right of expressions
}

predicate Valid(stmt: Statement) reads *
{
	match stmt {
		case Skip => true
		case Assignment(LHS, RHS) => |LHS| == |RHS|
		case SeqComp(S1,S2) => Valid(S1) && Valid(S2)
		case IF(B,Sthen,Selse) => Valid(Sthen) && Valid(Selse)
			//(forall state: State :: B.requires(state) && B(state).Bool?) && 
			//Valid(Sthen) && Valid(Selse)
		case DO(B,S) => Valid(S)
			//(forall state: State :: B.requires(state) && B(state).Bool?) && Valid(S)
		case LocalDeclaration(L,S) => Valid(S)
	} 
	//&&
	//forall state1: State, P: Predicate  :: P.requires(state1)

}

predicate ValidVsSSA(vsSSA: VariablesSSA) reads vsSSA
{
	vsSSA != null && vsSSA.n >= 1 && forall v :: v in vsSSA.m ==> |vsSSA.m[v]| >= 1
}

method digitToString(num: int) returns (str: string)
	requires num >= 0 && num <= 9
{
	if num == 0 { str := "0"; }
	else if num == 1 { str := "1"; }
	else if num == 2 { str := "2"; }
	else if num == 3 { str := "3"; }
	else if num == 4 { str := "4"; }
	else if num == 5 { str := "5"; }
	else if num == 6 { str := "6"; }
	else if num == 7 { str := "7"; }
	else if num == 8 { str := "8"; }
	else if num == 9 { str := "9"; }
}


method intToString(num: int) returns (str: string)
	requires num >= 0
{
	if num >= 0 && num <= 9 { str := digitToString(num); }
	else
	{
		var digitStr := digitToString(num % 10);
		var str' := intToString(num / 10);
		str := str' + digitStr;
	}
}

 method freshInit(vars : seq<Variable>, ghost allVars : set<Variable>, vsSSA : VariablesSSA) returns (res: seq<Variable>)
	requires ValidVsSSA(vsSSA)
	ensures |res| == |vars|
	modifies vsSSA
	ensures ValidVsSSA(vsSSA)
	ensures vsSSA.m == old(vsSSA.m)
{
	if vars == [] { res := []; } 
	else
	{
		var n := vsSSA.getAndIncN();
		var nStr := intToString(n);
		var res' := freshInit(vars[1..], allVars + {vars[0] + nStr}, vsSSA);

		res := [vars[0] + nStr] + res';
	}
}

function method def(S : Statement) : set<Variable> // FIXME: make it return a set
//	ensures def(S) == {"i","sum","prod"};
{
	match S {
		case Assignment(LHS,RHS) => setOf(LHS) // FIXME
		case Skip => {}
		case SeqComp(S1,S2) => def(S1) + def(S2)
		case IF(B0,Sthen,Selse) => def(Sthen) + def(Selse)
		case DO(B,S) => def(S)
		case LocalDeclaration(L,S0) => def(S0) - setOf(L)
	}
}

function method ddef(S : Statement) : set<Variable>
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

function method input(S : Statement) : set<Variable>
//	ensures input(S) == ["i","sum","prod"];
{
	match S {
		case Assignment(LHS,RHS) => setOf(LHS) // FIXME (LHS is a sequence of Expression(s), not Variable(s)
		case Skip => {}
		case SeqComp(S1,S2) => input(S1) + (input(S2) - ddef(S1)) // right?
		case IF(B0,Sthen,Selse) => setOf([B0]) + input(Sthen) + input(Selse) // FIXME: variables of B0?
		case DO(B,S) => setOf([B]) + input(S) // FIXME: variables of B?
		case LocalDeclaration(L,S0) => input(S0) - setOf(L) // FIXME is the "- L" not redundant?
	}
}

function method glob(S : Statement) : set<Variable>
	//ensures glob(S) == setOf(def(S) + input(S));
{
	set v | v in def(S) + input(S)
}

function method setOf(s : seq<Variable>) : set<Variable>
	ensures forall v :: v in setOf(s) ==> v in s
{
	set x | x in s
}


/*function method setToSeq(s : set<Variable>) : seq<Variable>
	requires |s| >= 1
{
	var v :| v in s;

	if |s| == 1 then [v] else [v] + setToSeq(s - {v})
}*/


 method setToSeq(s : set<Variable>) returns (res: seq<Variable>)
	ensures setOf(res) == s
	ensures |res| == |s|
{
	if s == {} { res := []; }
	else
	{
		var v :| v in s;
		var res' := setToSeq(s - {v});

		res := [v] + res';
	}
}


//////////////////////////////////////////////////////////


method IsVariableInSet(v: Variable, X: set<Variable>) returns (isInSet: bool)
{
	if X == {} { isInSet := false; }
	else
	{
		var x :| x in X;
		if x == v { isInSet := true; }
		else
		{
			 isInSet := IsVariableInSet(v, X - {x});
		}
	}
}

method GetXandE(LHS: seq<Variable>, RHS: seq<Expression>, X: set<Variable>, index: int) returns (XSeq: seq<Variable>, ESeq: seq<Expression>, indexSeq: seq<int>)
	requires Valid(Assignment(LHS,RHS))
	ensures LHS == old(LHS)
	ensures RHS == old(RHS)
	ensures X == old(X)
	ensures |XSeq| == |ESeq| == |indexSeq|
{
	if LHS == [] { XSeq:= []; ESeq := []; indexSeq := []; }
	else
	{
		var x, e, i := [], [], [];
		var isVariableInSet := IsVariableInSet(LHS[0], X);
		
		if isVariableInSet == true
		{
			x := [LHS[0]];
			e := [RHS[0]];
			i := [index];
		}

		var XSeq', ESeq', indexSeq' := GetXandE(LHS[1..], RHS[1..], X, index + 1);

		XSeq := x + XSeq';
		ESeq := e + ESeq';
		indexSeq := i + indexSeq';
	}
}

method GetInstanceAccordingToX(x: Variable, instancesOfX: set<Variable>, vsSSA: VariablesSSA) returns (x': Variable)
	requires vsSSA != null
	requires |instancesOfX| >= 1
	requires vsSSA.existsInstance(x)
	ensures x' in instancesOfX
{
	var i :| i in instancesOfX;

	if |instancesOfX| == 1 { x' := i; }
	else if i in vsSSA.m[x] { x' := i; }
	else
	{
		x' := GetInstanceAccordingToX(x, instancesOfX - {i}, vsSSA);
	}
}

/*method InstancesSetToSeq(instancesOfX: set<Variable>, X: seq<Variable>, vsSSA: VariablesSSA) returns (instancesOfXSeq: seq<Variable>)
	requires ValidVsSSA(vsSSA)
	requires |instancesOfX| == |X|
	requires forall x :: x in X ==> vsSSA.existsInstance(x)
{
	// For example: instancesOfX	= {b2,a3,c1}
	//				X				= [a,b,c]
	//				instancesOfXSeq = [a3,b2,c1]	

	if X == [] { instancesOfXSeq := []; }
	else
	{  
		var i := GetInstanceAccordingToX(X[0], instancesOfX, vsSSA);					// i = a3
		var instancesOfXSeq' := InstancesSetToSeq(instancesOfX - {i}, X[1..], vsSSA);	// instancesOfXSeq = [b2,c1]
		
		instancesOfXSeq := [i] + instancesOfXSeq';										// instancesOfXSeq = [a3,b2,c1]
	}
}*/

method InstancesSetToSeq(instancesOfX: set<Variable>, X: seq<Variable>, vsSSA: VariablesSSA) returns (instancesOfXSeq: seq<Variable>)
	requires ValidVsSSA(vsSSA)
	requires forall x :: x in X ==> vsSSA.existsInstance(x)
{
	// For example: instancesOfX	= {b2,a3,c1}
	//				X				= [a,b,c]
	//				instancesOfXSeq = [a3,b2,c1]	

	if X == [] { instancesOfXSeq := []; }
	else
	{  
		var instancesOfX0 := vsSSA.getInstancesOfVarible(X[0]);						// instancesOfX0 = [a1,a2,a3,a4...]
		var i := setOf(instancesOfX0) * instancesOfX;								// i = {a3}
		var instancesOfXSeq' := InstancesSetToSeq(instancesOfX - i, X[1..], vsSSA);	// instancesOfXSeq = [b2,c1]
		
		var temp := setToSeq(i);													// temp = [a3]
		instancesOfXSeq := temp + instancesOfXSeq';									// instancesOfXSeq = [a3,b2,c1]
	}
}

method SubstitueExpressionSeq(E: seq<Expression>, X: seq<set<Variable>>, XLi: seq<set<Variable>>) returns (E': seq<Expression>)
	ensures |E| == |E'|
{
	E' := E;
	// TODO - OR!
}

method SubstitueBooleanExpression(B: BooleanExpression, X: seq<set<Variable>>, XLi: seq<set<Variable>>) returns (B': BooleanExpression)
	ensures |B| == |B'|
{
	B' := B;
	// TODO - OR!
}

/*method GetNewLHS(LHS: seq<Variable>, instances: set<Variable>, vsSSA: VariablesSSA) returns (LHS': seq<Variable>)
	requires vsSSA != null
	requires |instances| >= 1
	requires forall x :: x in LHS ==> vsSSA.existsInstance(x)
{
	if LHS == [] { LHS' := []; }
	else
	{
		var x' := GetInstanceAccordingToX(LHS[0], instances, vsSSA);
		var LHS'' := GetNewLHS(LHS[1..], instances, vsSSA);

		LHS' := [x'] + LHS'';
	}
}*/

method GetNewLHS(LHS: seq<Variable>, instances: set<Variable>, vsSSA: VariablesSSA) returns (LHS': seq<Variable>)
	requires ValidVsSSA(vsSSA);
	requires forall x :: x in LHS ==> vsSSA.existsInstance(x)
{
	if LHS == [] { LHS' := []; }
	else
	{
		var instancesOfLHS0 := vsSSA.getInstancesOfVarible(LHS[0]);
		var i := setOf(instancesOfLHS0) * instances;	
		var LHS'' := GetNewLHS(LHS[1..], instances, vsSSA);

		var temp := setToSeq(i);
		LHS' := temp + LHS'';	
	}
}

method FindIndexOfNum(arr: seq<int>, num: int) returns (i: int)
	ensures -1 <= i <= |arr|-1
{
	if |arr| == 0 { i := -1; }
	else if arr[0] == num { i := 0; }
	else
	{
		i := FindIndexOfNum(arr[1..], num);
		i := i + 1; 
	}
}

method GetNewRHS(indices: seq<int>, E: seq<Expression>, index: int) returns (RHS': seq<Variable>)
	requires |indices| == |E|
	requires index >= 0
	requires index <= |indices| 
	requires 0 <= |indices|-index <= |indices|
	decreases |indices|-index
{
	if index == |indices| { RHS' := []; }
	else
	{
		var i := FindIndexOfNum(indices, index);
		var RHS'' := GetNewRHS(indices, E, index + 1);

		if !(i == -1) { RHS' := [E[i]] + RHS''; }
	}
}

method FindVariableIndexInVariableSequence(v: Variable, V: seq<Variable>) returns (i: int)
	ensures i >= -1 && i < |V|
{
	if |V| == 0 { i := -1; }
	else if V[0] == v { i := 0; }
	else
	{
		i := FindVariableIndexInVariableSequence(v, V[1..]);
		i := i + 1;
	}
}

/*method FindVariableIndexInVariableSequence(v: Variable, V: seq<Variable>) returns (i: int)
	requires |V| >= 1
	ensures i >= 0 && i < |V|
{
	if |V| == 1 { i := 0; }
	else if V[0] == v { i := 0; }
	else
	{
		i := FindVariableIndexInVariableSequence(v, V[1..]);
		i := i + 1;
	}
}*/

method OrganizeVariables(vars1: seq<Variable>, vars2: seq<Variable>, vsSSA: VariablesSSA) returns (res: seq<Variable>)
	requires ValidVsSSA(vsSSA)
	requires forall i :: i in vars1 ==> vsSSA.existsVariable(i)
	requires forall i :: i in vars2 ==> vsSSA.existsVariable(i)
	ensures ValidVsSSA(vsSSA)
{
	if vars1 == [] { res := []; }
	else
	{
		var v1 := vsSSA.getVariableInRegularForm(vars1[0]);
		var vars2Variables := vsSSA.instancesToVariables(vars2);
		var index := FindVariableIndexInVariableSequence(v1, vars2Variables);
		var res' := OrganizeVariables(vars1[1..], vars2, vsSSA);

		res := res';

		if index != -1 { res := [vars2[index]] + res'; }
	}
}

/*method OrganizeVariables(vars1: seq<Variable>, vars2: seq<Variable>, vsSSA: VariablesSSA) returns (res: seq<Variable>)
	requires ValidVsSSA(vsSSA)
	requires forall i :: i in vars1 ==> vsSSA.existsVariable(i)
	requires forall i :: i in vars2 ==> vsSSA.existsVariable(i)
	requires |vars1| >= 0 && |vars2| >= 1
	ensures ValidVsSSA(vsSSA)
{
	if vars1 == [] { res := []; }
	else
	{
		var v1 := vsSSA.getVariableInRegularForm(vars1[0]);
		var vars2Variables := vsSSA.instancesToVariables(vars2);
		var index := FindVariableIndexInVariableSequence(v1, vars2Variables);
		var res' := OrganizeVariables(vars1[1..], vars2, vsSSA);

		assert index < |vars2| && index >= 0;
		res := [vars2[index]] + res';
	}
}*/


method ToSSA(S: Statement, X: seq<Variable>, liveOnEntryX: seq<Variable>, liveOnExitX: seq<Variable>, Y: set<Variable>, XLs: set<Variable>, vsSSA: VariablesSSA) returns(S': Statement)
	requires Valid(S)
	requires ValidVsSSA(vsSSA)
	requires forall i :: i in liveOnEntryX ==> vsSSA.existsVariable(i)
	requires forall i :: i in liveOnExitX ==> vsSSA.existsVariable(i)
	requires forall v :: v in X ==> vsSSA.existsInstance(v)
	requires forall v :: v in Y ==> vsSSA.existsInstance(v)
	modifies vsSSA
	decreases *
	ensures Valid(S')
	ensures ValidVsSSA(vsSSA)
	ensures forall i :: i in liveOnEntryX ==> vsSSA.existsVariable(i)
	ensures forall i :: i in liveOnExitX ==> vsSSA.existsVariable(i)
	ensures forall v :: v in X ==> vsSSA.existsInstance(v)
	ensures forall v :: v in old(vsSSA.m) ==> v in vsSSA.m && (forall i :: i in old(vsSSA.m[v]) ==> i in vsSSA.m[v])
{
	//var vsSSA := new VariablesSSA(); // Create in main!

	match S {
		/*case Assignment(LHS,RHS) => S' := AssignmentToSSA(LHS, RHS, X, liveOnEntryX, liveOnExitX, Y, XLs, vsSSA);
		case SeqComp(S1,S2) => S' := SeqCompToSSA(S1, S2, X, liveOnEntryX, liveOnExitX, Y, XLs, vsSSA);
		case IF(B0,Sthen,Selse) => S' := IfToSSA(B0, Sthen, Selse, X, liveOnEntryX, liveOnExitX, Y, XLs, vsSSA);
		case DO(B,S) => S' := DoToSSA(B, S, X, liveOnEntryX, liveOnExitX, Y, XLs, vsSSA);
		case LocalDeclaration(L,S0) => S' := Skip;
		case Skip => S' := Skip;*/

		case Assignment(LHS,RHS) => S' := Skip;
		case SeqComp(S1,S2) => S' := Skip;
		case IF(B0,Sthen,Selse) => S' := IfToSSA(B0, Sthen, Selse, X, liveOnEntryX, liveOnExitX, Y, XLs, vsSSA);
		case DO(B,S) => S' := Skip;
		case LocalDeclaration(L,S0) => S' := Skip;
		case Skip => S' := Skip;
	}
}


method {:verify false}AssignmentToSSA(LHS: seq<Variable>, RHS: seq<Expression>, X: seq<Variable>, liveOnEntryX: seq<Variable>, liveOnExitX: seq<Variable>, Y: set<Variable>, XLs: set<Variable>, vsSSA: VariablesSSA) returns (S': Statement)
	requires ValidVsSSA(vsSSA)
	requires Valid(Assignment(LHS,RHS))
	requires forall i :: i in liveOnEntryX ==> vsSSA.existsVariable(i)
	requires forall i :: i in liveOnExitX ==> vsSSA.existsVariable(i)
	requires forall x :: x in X ==> vsSSA.existsInstance(x)
	requires forall y :: y in Y ==> vsSSA.existsInstance(y)
	requires setOf(LHS) <= (setOf(X) + Y)
	modifies vsSSA
	ensures ValidVsSSA(vsSSA)
	ensures forall i :: i in liveOnEntryX ==> vsSSA.existsVariable(i)
	ensures forall i :: i in liveOnExitX ==> vsSSA.existsVariable(i)
	ensures forall v :: v in X ==> vsSSA.existsInstance(v)
	ensures forall v :: v in old(vsSSA.m) ==> v in vsSSA.m && (forall i :: i in old(vsSSA.m[v]) ==> i in vsSSA.m[v])
{
	// הפונקציה עוברת קימפול! :)
	// רק 2 דקות דרך cmd.


	// defined in thesis:
	// toSSA.("X4,X2,X5,X6,Y1 := E1,E2,E3,E4,E5",
	// X, (XL1i, XL2i, XL3i, XL4i), (XL3i, XL4f ,XL5f), Y ,XLs)) is:
	// "XL4f, XL2, XL5f, XL6, Y1 := E1', E2', E3', E4', E5'"

	//// find X1,X2,X3,X4,X5,X6,Y1 SETS ////

	var XL3i := setOf(liveOnEntryX) * setOf(liveOnExitX);
	assert XL3i <= setOf(liveOnEntryX) && XL3i <= setOf(liveOnExitX);
	var temp := setToSeq(XL3i);
	var X3Seq := vsSSA.instancesToVariables(temp);
	var X3 := setOf(X3Seq);

	var XL1iXL2iXL4i := setOf(liveOnEntryX) - XL3i;
	assert XL1iXL2iXL4i <= setOf(liveOnEntryX);
	temp := setToSeq(XL1iXL2iXL4i);
	var X1X2X4 := vsSSA.instancesToVariables(temp);
	var XL4fXL5f := setOf(liveOnExitX) - XL3i;
	assert XL4fXL5f <= setOf(liveOnExitX);
	temp := setToSeq(XL4fXL5f);
	var X4X5 := vsSSA.instancesToVariables(temp);
	var X4 := setOf(X1X2X4) * setOf(X4X5) * setOf(X);
	var X5 := setOf(X4X5) - X4;

	var X1X2 := setOf(X1X2X4) - X4;
	var X2 := X1X2 * def(Assignment(LHS,RHS));
	var X1 := X1X2 - X2;

	var X6Y1 := setOf(liveOnEntryX) - X4 - X2 - X5;
	var X6 := setOf(X) * X6Y1;
	var Y1 := X6Y1 - X6;

	////////////////////////////////////////
	
	var E1, E2, E3, E4, E5;
	var X4Seq, X2Seq, X5Seq, X6Seq, Y1Seq;
	var indexSeqX4, indexSeqX2, indexSeqX5, indexSeqX6, indexSeqY1;

	X4Seq, E1, indexSeqX4 := GetXandE(LHS, RHS, X4, 0);
	X2Seq, E2, indexSeqX2 := GetXandE(LHS, RHS, X2, 0);
	X5Seq, E3, indexSeqX5 := GetXandE(LHS, RHS, X5, 0);
	X6Seq, E4, indexSeqX6 := GetXandE(LHS, RHS, X6, 0);
	Y1Seq, E5, indexSeqY1 := GetXandE(LHS, RHS, Y1, 0);
	
	////////////////////////////////////////

	assert X4 <= setOf(X);
	temp := setToSeq(X4);
	var X4Instances := vsSSA.getInstancesOfVaribleSeq(temp);
	var XL5f := XL4fXL5f - setOf(X4Instances);
	var XL4f := XL4fXL5f - XL5f;
	
	////////////////////////////////////////

	var E1', E2', E3', E4', E5';
	var XL1iXL2i := XL1iXL2iXL4i - setOf(X4Instances);
	var XL4i := XL1iXL2iXL4i - XL1iXL2i;

	var temp2 := setOf(X2Seq) * setOf(X);
	assert temp2 <= setOf(X);
	X2Seq := setToSeq(temp2);
	var X2Instances := vsSSA.getInstancesOfVaribleSeq(X2Seq);
	var XL1i := XL1iXL2i - setOf(X2Instances);
	var XL2i := XL1iXL2i - XL1i;
	
	E1' := SubstitueExpressionSeq(E1, [X1,X2,X3,X4], [XL1i,XL2i,XL3i,XL4i]);
	E2' := SubstitueExpressionSeq(E2, [X1,X2,X3,X4], [XL1i,XL2i,XL3i,XL4i]);
	E3' := SubstitueExpressionSeq(E3, [X1,X2,X3,X4], [XL1i,XL2i,XL3i,XL4i]);
	E4' := SubstitueExpressionSeq(E4, [X1,X2,X3,X4], [XL1i,XL2i,XL3i,XL4i]);
	E5' := SubstitueExpressionSeq(E5, [X1,X2,X3,X4], [XL1i,XL2i,XL3i,XL4i]);
	
	var XL2XL6 := freshInit(X2Seq + X6Seq, setOf(X)+Y+XLs, vsSSA);
		 
		vsSSA.variablesToSSAVariables(X2Seq + X6Seq, XL2XL6);
		assert forall v :: v in (setOf(X) + Y) ==> vsSSA.existsInstance(v);

	////////////////////////////////////////
	
	var LHS' := GetNewLHS(LHS, XL4f + setOf(XL2XL6[..|X2Seq|]) + XL5f + setOf(XL2XL6[|X2Seq|..]) + Y1, vsSSA);
	var RHS' := GetNewRHS(indexSeqX4 + indexSeqX2 + indexSeqX5 + indexSeqX6 + indexSeqY1, E1' + E2' + E3' + E4' + E5', 0);

	S' := Assignment(LHS', RHS');
}

method {:verify false}SeqCompToSSA(S1: Statement, S2: Statement, X: seq<Variable>, liveOnEntryX: seq<Variable>, liveOnExitX: seq<Variable>, Y: set<Variable>, XLs: set<Variable>, vsSSA: VariablesSSA) returns (S': Statement)
	//requires Valid(SeqComp(S1, S2))
	requires ValidVsSSA(vsSSA)
	requires forall i :: i in liveOnEntryX ==> vsSSA.existsVariable(i)
	requires forall i :: i in liveOnExitX ==> vsSSA.existsVariable(i)
	requires forall v :: v in X ==> vsSSA.existsInstance(v)
	modifies vsSSA
	decreases *
	ensures ValidVsSSA(vsSSA)
	ensures forall i :: i in liveOnEntryX ==> vsSSA.existsVariable(i)
	ensures forall i :: i in liveOnExitX ==> vsSSA.existsVariable(i)
	ensures forall v :: v in X ==> vsSSA.existsInstance(v)
	ensures forall v :: v in old(vsSSA.m) ==> v in vsSSA.m && (forall i :: i in old(vsSSA.m[v]) ==> i in vsSSA.m[v])
	//ensures Valid(S')
{

	// הפונקציה עוברת קימפול! :)
	// 2:06 שעות דרך cmd.


	// defined in thesis:
	// toSSA.(" S1 ; S2 ", X, (XL1i, XL2i, XL3i, XL4i), (XL3i, XL4f, XL5f), Y, XLs) is:
	// " S1' ; S2' "

	var XL3i := setOf(liveOnEntryX) * setOf(liveOnExitX);
	assert XL3i <= setOf(liveOnEntryX) && XL3i <= setOf(liveOnExitX);
	var temp := setToSeq(XL3i);
	var X3Seq := vsSSA.instancesToVariables(temp);
	var X3 := setOf(X3Seq) * setOf(X);
	
	var liveOnEntryXVariables := vsSSA.instancesToVariables(liveOnEntryX);
	var liveOnExitXVariables := vsSSA.instancesToVariables(liveOnExitX);
	var X3X4 := setOf(liveOnEntryXVariables) * setOf(liveOnExitXVariables);
	var X4 := (X3X4 - X3) * setOf(X);
	var X5 := (setOf(liveOnExitXVariables) - X3X4) * setOf(X);

	var X1X2 := setOf(liveOnEntryXVariables) - X3X4;
	var X2 := (X1X2 * (def(S1) + def(S2))) * setOf(X);
	assert X2 <= setOf(X);
	var X1 := (X1X2 - X2) * setOf(X);

	var XL1iXL2iXL4i := setOf(liveOnEntryX) - XL3i;
	
	assert X4 <= setOf(X);
	temp := setToSeq(X4);
	var X4Instances := vsSSA.getInstancesOfVaribleSeq(temp);
	var XL1iXL2i := XL1iXL2iXL4i - setOf(X4Instances);
	var XL4i := XL1iXL2iXL4i - XL1iXL2i;

	assert X5 <= setOf(X);
	temp := setToSeq(X2);
	var X2Instances := vsSSA.getInstancesOfVaribleSeq(temp);
	var XL1i := XL1iXL2i - setOf(X2Instances);
	var XL2i := XL1iXL2i - XL1i;

	var XL4fXL5f := setOf(liveOnExitX) - XL3i;
	var XL5f := XL4fXL5f - setOf(X4Instances);
	var XL4f := XL4fXL5f - XL5f;

	var X6 := (setOf(X) - X3) * (((X4 + X5) - ddef(S2)) + input(S2)); 
	var X11 := X1 * X6; 
	var X21 := (X2 * X6) - def(S1); 
	var X41 := (X4 * X6) - def(S1); 
	var X42 := (X4 * X6) - def(S2); 
	var X51 := (X5 * X6) - def(S2);
	var X61 := X6 - (X11+X21+X41+X42+X51); 

	var X61Seq := setToSeq(X61);
	var XL61Seq := freshInit(X61Seq, setOf(X) + Y + XLs, vsSSA);

		vsSSA.variablesToSSAVariables(X61Seq, XL61Seq);
		assert forall i :: i in XL61Seq ==> vsSSA.existsVariable(i);

	assert forall v :: v in X ==> vsSSA.existsInstance(v);
	assert X1 <= setOf(X) && forall v :: v in X1 ==> vsSSA.existsInstance(v);
	temp := setToSeq(X1);
	var XL11iTemp := vsSSA.getInstancesOfVaribleSeq(temp);
	assert forall i :: i in XL11iTemp ==> vsSSA.existsVariable(i);
	var XL11iSeq := setToSeq(setOf(XL11iTemp) * XL1i);
	assert setOf(XL11iSeq) <= setOf(XL11iTemp) && forall i :: i in XL11iSeq ==> vsSSA.existsVariable(i);

	assert forall v :: v in X ==> vsSSA.existsInstance(v);
	assert X2 <= setOf(X) && forall v :: v in X2 ==> vsSSA.existsInstance(v);
	temp := setToSeq(X2);
	var XL21iTemp := vsSSA.getInstancesOfVaribleSeq(temp);
	assert forall i :: i in XL21iTemp ==> vsSSA.existsVariable(i);
	var XL21iSeq := setToSeq(setOf(XL21iTemp) * XL2i);
	assert setOf(XL21iSeq) <= setOf(XL21iTemp) && forall i :: i in XL21iSeq ==> vsSSA.existsVariable(i);
	
	assert forall v :: v in X ==> vsSSA.existsInstance(v);
	assert X4 <= setOf(X) && forall v :: v in X4 ==> vsSSA.existsInstance(v);
	temp := setToSeq(X4);
	var XL41iTemp := vsSSA.getInstancesOfVaribleSeq(temp);
	assert forall i :: i in XL41iTemp ==> vsSSA.existsVariable(i);
	var XL41iSeq := setToSeq(setOf(XL41iTemp) * XL4i);
	assert setOf(XL41iSeq) <= setOf(XL41iTemp) && forall i :: i in XL41iSeq ==> vsSSA.existsVariable(i);

	assert forall v :: v in X ==> vsSSA.existsInstance(v);
	assert X4 <= setOf(X) && forall v :: v in X4 ==> vsSSA.existsInstance(v);
	temp := setToSeq(X4);
	var XL42fTemp := vsSSA.getInstancesOfVaribleSeq(temp);
	assert forall i :: i in XL42fTemp ==> vsSSA.existsVariable(i);
	var XL42fSeq := setToSeq(setOf(XL42fTemp) * XL4f);
	assert setOf(XL42fSeq) <= setOf(XL42fTemp) && forall i :: i in XL42fSeq ==> vsSSA.existsVariable(i);

	assert forall v :: v in X ==> vsSSA.existsInstance(v);
	assert X5 <= setOf(X) && forall v :: v in X5 ==> vsSSA.existsInstance(v);
	temp := setToSeq(X5);
	var XL51fTemp := vsSSA.getInstancesOfVaribleSeq(temp);
	assert forall i :: i in XL51fTemp ==> vsSSA.existsVariable(i);
	var XL51fSeq := setToSeq(setOf(XL51fTemp) * XL5f);
	assert setOf(XL51fSeq) <= setOf(XL51fTemp) && forall i :: i in XL51fSeq ==> vsSSA.existsVariable(i);
	
	temp := setToSeq(XL3i);
	assert forall i :: i in XL3i ==> vsSSA.existsVariable(i);
	assert forall i :: i in temp ==> vsSSA.existsVariable(i);

	var XL6 := XL11iSeq + XL21iSeq + temp + XL41iSeq + XL42fSeq + XL51fSeq + XL61Seq;
	assert forall i :: i in XL6 ==> vsSSA.existsVariable(i);

	var XLs' := XLs + setOf(XL61Seq);
	var S1' := ToSSA(S1, X, liveOnEntryX, XL6, Y, XLs', vsSSA);

	assert forall i :: i in XL6 ==> vsSSA.existsVariable(i);
	var XLs'' := XLs' + (glob(S1') - Y);
	var S2' := ToSSA(S2, X, XL6, liveOnExitX, Y, XLs'', vsSSA);

	S' := SeqComp(S1', S2');
}

method {:verify false}IfToSSA(B : BooleanExpression, S1 : Statement, S2 : Statement, X: seq<Variable>, liveOnEntryX: seq<Variable>, liveOnExitX: seq<Variable>, Y: set<Variable>, XLs: set<Variable>, vsSSA: VariablesSSA) returns (S': Statement)
	requires ValidVsSSA(vsSSA)
	requires Valid(IF(B, S1, S2))
	requires forall i :: i in liveOnEntryX ==> vsSSA.existsVariable(i)
	requires forall i :: i in liveOnExitX ==> vsSSA.existsVariable(i)
	requires forall v :: v in X ==> vsSSA.existsInstance(v)
	requires forall y :: y in Y ==> vsSSA.existsInstance(y)
	modifies vsSSA
	decreases *
	ensures Valid(S')
	ensures ValidVsSSA(vsSSA)
	ensures forall i :: i in liveOnEntryX ==> vsSSA.existsVariable(i)
	ensures forall i :: i in liveOnExitX ==> vsSSA.existsVariable(i)
	ensures forall v :: v in X ==> vsSSA.existsInstance(v)
	ensures forall v :: v in old(vsSSA.m) ==> v in vsSSA.m && (forall i :: i in old(vsSSA.m[v]) ==> i in vsSSA.m[v])
{
	// defined in thesis:
	// toSSA.(IF ,X, (XL1i, XL2i, XL3i, XL4i), (XL3i, XL4f, XL5f), Y, XLs) is:
	// IF' where:
	// IF := " if B then S1 else S2 fi "
	// IF' := " if B' then S1'; XL4f ,XL5f := XL4t, XL5t else S2'; XL4f ,XL5f := XL4e, XL5e fi "

	var XL3i := setOf(liveOnEntryX) * setOf(liveOnExitX);
	assert XL3i <= setOf(liveOnEntryX) && XL3i <= setOf(liveOnExitX);
	var temp := setToSeq(XL3i);
	var X3Seq := vsSSA.instancesToVariables(temp);
	var X3 := setOf(X3Seq);
	
	var XL4fXL5f := setOf(liveOnExitX) - XL3i;
	assert XL4fXL5f <= setOf(liveOnExitX);
	temp := setToSeq(XL4fXL5f);

	var X4X5 := vsSSA.instancesToVariables(temp);
	var liveOnEntryXVariables := vsSSA.instancesToVariables(liveOnEntryX);
	//var X4 := setOf(liveOnEntryXVariables) * setOf(X4X5);
	var X4 := (setOf(liveOnEntryXVariables) * setOf(X4X5)) * setOf(X);
	var X5Seq := setToSeq(setOf(X4X5) - X4);

	//var X2 := (setOf(liveOnEntryXVariables) - X4) * (def(S1) + def(S2));
	var X2 := ((setOf(liveOnEntryXVariables) - X4) * (def(S1) + def(S2))) * setOf(X);
	assert X2 <= setOf(X);
	var X1 := setOf(liveOnEntryXVariables) - X4 - X3 - X2;
	
	var XL1iXL2iXL4i := setOf(liveOnEntryX) - XL3i;
	assert X4 <= setOf(X);
	temp := setToSeq(X4);
	var X4Instances := vsSSA.getInstancesOfVaribleSeq(temp);
	var XL1iXL2i := XL1iXL2iXL4i - setOf(X4Instances);
	var XL4i := XL1iXL2iXL4i - XL1iXL2i;

	assert X2 <= setOf(X);
	temp := setToSeq(X2);
	var X2Instances := vsSSA.getInstancesOfVaribleSeq(temp);
	var XL1i := XL1iXL2i - setOf(X2Instances);
	var XL2i := XL1iXL2i - XL1i;

	var B' := SubstitueBooleanExpression(B, [X1,X2,X3,X4], [XL1i,XL2i,XL3i,XL4i]);
	
	//var X4d1 := X4 * (def(S1) - def(S2));
	var X4d1 := (X4 * (def(S1) - def(S2))) * setOf(X);
	//var X4d2 := X4 * (def(S2) - def(S1));
	var X4d2 := (X4 * (def(S2) - def(S1))) * setOf(X);
	var X4d1d2 := X4 * def(S1) * def(S2);

	temp := setToSeq(X4d1);
	var temp1 := setToSeq(X4d2);
	var temp2 := setToSeq(X4d1d2);
	var temp3 := setToSeq(X4d1d2);
	var variables := temp + temp1 + temp2 + temp3 + X5Seq + X5Seq;
	var instances := freshInit(variables, setOf(X) + Y + XLs, vsSSA);

		vsSSA.variablesToSSAVariables(variables, instances);
		assert forall v :: v in X ==> vsSSA.existsInstance(v);
		assert forall i :: i in instances ==> vsSSA.existsVariable(i);

	var XL4d1t := instances[0..|X4d1|];
	assert forall i :: i in XL4d1t ==> vsSSA.existsVariable(i);
	assert X4d2 <= setOf(X) && forall v :: v in X4d2 ==> vsSSA.existsInstance(v);
	temp := setToSeq(X4d2);
	var XL4d2iTemp := vsSSA.getInstancesOfVaribleSeq(temp);
	assert forall i :: i in XL4d2iTemp ==> vsSSA.existsVariable(i);
	var XL4d2iSeq := setToSeq(setOf(XL4d2iTemp) * XL4i);
	assert setOf(XL4d2iSeq) <= setOf(XL4d2iTemp) && forall i :: i in XL4d2iSeq ==> vsSSA.existsVariable(i);
	var XL4d1d2t := instances[|X4d1|+|X4d2|..|X4d1|+|X4d2|+|X4d1d2|];
	assert forall i :: i in XL4d1d2t ==> vsSSA.existsVariable(i);
	var XL4t := XL4d1t + XL4d2iSeq + XL4d1d2t;
	assert forall i :: i in XL4t ==> vsSSA.existsVariable(i); // מתקמפל!!!! 8 דקות.

	assert X4d1 <= setOf(X) && forall v :: v in X4d1 ==> vsSSA.existsInstance(v);
	temp := setToSeq(X4d1);
	var XL4d1iTemp := vsSSA.getInstancesOfVaribleSeq(temp);
	assert forall i :: i in XL4d1iTemp ==> vsSSA.existsVariable(i);
	var XL4d1iSeq := setToSeq(setOf(XL4d1iTemp) * XL4i);
	assert setOf(XL4d1iSeq) <= setOf(XL4d1iTemp) && forall i :: i in XL4d1iSeq ==> vsSSA.existsVariable(i);
	var XL4d2e := instances[|X4d1|..|X4d1|+|X4d2|];
	assert forall i :: i in XL4d2e ==> vsSSA.existsVariable(i);
	var XL4d1d2e := instances[|X4d1|+|X4d2|+|X4d1d2|..|X4d1|+|X4d2|+|X4d1d2|+|X4d1d2|];
	assert forall i :: i in XL4d1d2e ==> vsSSA.existsVariable(i);
	var XL4e := XL4d1iSeq + XL4d2e + XL4d1d2e;
	assert forall i :: i in XL4e ==> vsSSA.existsVariable(i); // מתקמפל!!!! 20 דקות עד לפה.
	
	var XL5t := instances[|X4d1|+|X4d2|+|X4d1d2|+|X4d1d2|..|X4d1|+|X4d2|+|X4d1d2|+|X4d1d2|+|X5Seq|];
	assert forall i :: i in XL5t ==> vsSSA.existsVariable(i);
	var XL5e := instances[|X4d1|+|X4d2|+|X4d1d2|+|X4d1d2|+|X5Seq|..|X4d1|+|X4d2|+|X4d1d2|+|X4d1d2|+|X5Seq|+|X5Seq|];
	assert forall i :: i in XL5e ==> vsSSA.existsVariable(i);

	assert forall i :: i in XL4fXL5f ==> vsSSA.existsVariable(i);
	var XL5f := XL4fXL5f - setOf(X4Instances);
	assert forall i :: i in XL5f ==> vsSSA.existsVariable(i);
	temp := setToSeq(XL5f);
	assert forall i :: i in temp ==> vsSSA.existsVariable(i);
	var XL5fSeq := OrganizeVariables(XL5t, temp, vsSSA);

	assert forall i :: i in XL4fXL5f ==> vsSSA.existsVariable(i);
	var XL4f := XL4fXL5f - XL5f;
	assert forall i :: i in XL4f ==> vsSSA.existsVariable(i);
	temp := setToSeq(XL4f);
	assert forall i :: i in temp ==> vsSSA.existsVariable(i);
	assert forall i :: i in XL4t ==> vsSSA.existsVariable(i);
	var XL4fSeqThen := OrganizeVariables(XL4t, temp, vsSSA);

	temp := setToSeq(XL4f);
	assert forall i :: i in temp ==> vsSSA.existsVariable(i);
	assert forall i :: i in XL4e ==> vsSSA.existsVariable(i);
	var XL4fSeqElse := OrganizeVariables(XL4e, temp, vsSSA);
	
	// עד לפה 55 דקות.

	var XLs' := XLs + setOf(instances);
	temp := setToSeq(XL3i);
	assert forall i :: i in temp ==> vsSSA.existsVariable(i);
	assert forall i :: i in XL4t ==> vsSSA.existsVariable(i);
	assert forall i :: i in XL5t ==> vsSSA.existsVariable(i);
	var liveOnExitX' := temp + XL4t + XL5t;
	assert forall i :: i in liveOnExitX' ==> vsSSA.existsVariable(i);
	var S1' := ToSSA(S1, X, liveOnEntryX, liveOnExitX, Y, XLs, vsSSA); 
	// לא מתקמפל כי assert(Valid(S1)) לא עובד
	// האסרט עובד לפני הקריאה לfreshInit אך לא אחריה
	// אותו דבר קורה גם בSeqCompToSSA
	// אין לי מושג למה.
	// כשאפתור את הבעיה הזו הפונקציה אמורה להתקמפל סופית.

	var XLs'' := XLs' + (glob(S1') - Y);
	temp := setToSeq(XL3i);
	assert forall i :: i in temp ==> vsSSA.existsVariable(i);
	assert forall i :: i in XL4e ==> vsSSA.existsVariable(i);
	assert forall i :: i in XL5e ==> vsSSA.existsVariable(i);
	liveOnExitX' := temp + XL4e + XL5e;
	assert forall i :: i in liveOnExitX' ==> vsSSA.existsVariable(i);
	var S2' := ToSSA(S2, X, liveOnEntryX, liveOnExitX', Y, XLs'', vsSSA);

	S' := IF(B', SeqComp(S1', Assignment(XL4fSeqThen + XL5fSeq, XL4t + XL5t)), SeqComp(S2', Assignment(XL4fSeqElse + XL5fSeq, XL4e + XL5e)));
}

method {:verify false}DoToSSA(B : BooleanExpression, S : Statement, X: seq<Variable>, liveOnEntryX: seq<Variable>, liveOnExitX: seq<Variable>, Y: set<Variable>, XLs: set<Variable>, vsSSA: VariablesSSA) returns (S'': Statement)
	requires ValidVsSSA(vsSSA)
	requires forall i :: i in liveOnEntryX ==> vsSSA.existsVariable(i)
	requires forall i :: i in liveOnExitX ==> vsSSA.existsVariable(i)
	requires forall v :: v in X ==> vsSSA.existsInstance(v)
	modifies vsSSA
	decreases *	
	ensures ValidVsSSA(vsSSA)
	ensures forall i :: i in liveOnEntryX ==> vsSSA.existsVariable(i)
	ensures forall i :: i in liveOnExitX ==> vsSSA.existsVariable(i)
	ensures forall v :: v in X ==> vsSSA.existsInstance(v)
	ensures forall v :: v in old(vsSSA.m) ==> v in vsSSA.m && (forall i :: i in old(vsSSA.m[v]) ==> i in vsSSA.m[v])
{

	// הפונקציה עוברת קימפול! :)
	// שעתיים דרך cmd.


	// defined in thesis:
	// toSSA.(DO, X, (XL1i, XL2i, XL3i, XL4i), (XL3i, XL4f), Y ,XLs) is:
	// "XL2, XL4f := XL2i, XL4i; DO'" where:
	// DO := " while B do S1 od ",
	// DO' := " while B' do S1'; XL2, XL4f := XL2b, XL4b od "

	var XL4f := setOf(liveOnExitX) - (setOf(liveOnEntryX) * setOf(liveOnExitX));
	assert XL4f <= setOf(liveOnExitX);
	var XL4fSeq := setToSeq(XL4f);
	var temp := setToSeq(XL4f);
	var X4Seq := vsSSA.instancesToVariables(temp);
	var X4 := setOf(X4Seq) * setOf(X);
	assert X4 <= setOf(X);
	
	var liveOnEntryXVariables := vsSSA.instancesToVariables(liveOnEntryX);
	var X2 := ((setOf(liveOnEntryXVariables) - X4) * def(S)) * setOf(X);
	assert X2 <= setOf(X);
	var X2Seq := setToSeq(X2);

	var XL3i := setOf(liveOnEntryX) * setOf(liveOnExitX);
	assert XL3i <= setOf(liveOnEntryX) && XL3i <= setOf(liveOnExitX);
	var XL3iSeq := setToSeq(XL3i);
	assert setOf(XL3iSeq) == XL3i && XL3i <= setOf(liveOnExitX) ==> setOf(XL3iSeq) <= setOf(liveOnExitX);
	var X3Seq := vsSSA.instancesToVariables(XL3iSeq);
	var X3 := setOf(X3Seq);
	
	var X1 := setOf(liveOnEntryXVariables) - X4 - X3 - X2;

	var variables := X2Seq + X2Seq + X4Seq;
	var instances := freshInit(variables, setOf(X) + Y + XLs, vsSSA);

		vsSSA.variablesToSSAVariables(variables, instances);
		assert forall v :: v in X ==> vsSSA.existsInstance(v);

	var XL2Seq := instances[0..|X2|];
	assert forall i :: i in instances ==> vsSSA.existsVariable(i) && XL2Seq <= instances ==> forall i :: i in XL2Seq ==> vsSSA.existsVariable(i);
	var XL2bSeq := instances[|X2|..|X2|+|X2|];
	assert forall i :: i in instances ==> vsSSA.existsVariable(i) && XL2bSeq <= instances ==> forall i :: i in XL2bSeq ==> vsSSA.existsVariable(i);
	var XL4bSeq := instances[|X2|+|X2|..];
	assert forall i :: i in instances ==> vsSSA.existsVariable(i) && XL4bSeq <= instances ==> forall i :: i in XL4bSeq ==> vsSSA.existsVariable(i);
	
	var XL1iXL2iXL4i := setOf(liveOnEntryX) - (setOf(liveOnEntryX) * setOf(liveOnExitX));
	assert XL1iXL2iXL4i <= setOf(liveOnEntryX);
	assert forall i :: i in XL1iXL2iXL4i ==> vsSSA.existsVariable(i);
	assert X4 <= setOf(X);
	temp := setToSeq(X4);
	var X4Instances := vsSSA.getInstancesOfVaribleSeq(temp);
	var XL1iXL2i := XL1iXL2iXL4i - setOf(X4Instances);
	assert XL1iXL2i <= XL1iXL2iXL4i;
	assert forall i :: i in XL1iXL2i ==> vsSSA.existsVariable(i);
	var XL4i := XL1iXL2iXL4i - XL1iXL2i;
	temp := setToSeq(XL4i);
	assert setOf(temp) <= setOf(liveOnEntryX);
	assert forall i :: i in liveOnEntryX ==> vsSSA.existsVariable(i);
	assert forall i :: i in temp ==> vsSSA.existsVariable(i);
	assert XL4f <= setOf(liveOnExitX) && setOf(XL4fSeq) == XL4f ==> setOf(XL4fSeq) <= setOf(liveOnExitX);
	assert forall i :: i in liveOnExitX ==> vsSSA.existsVariable(i);
	assert forall i :: i in XL4fSeq ==> vsSSA.existsVariable(i);
	var XL4iSeq := OrganizeVariables(XL4fSeq, temp, vsSSA);
	
	assert forall v :: v in X ==> vsSSA.existsInstance(v);
	assert X2 <= setOf(X) && setOf(X2Seq) == X2 ==> setOf(X2Seq) <= setOf(X);
	var X2Instances := vsSSA.getInstancesOfVaribleSeq(X2Seq);
	var XL1i := XL1iXL2i - setOf(X2Instances);
	assert XL1i <= XL1iXL2i;
	var XL2i := XL1iXL2i - XL1i;
	assert XL2i <= XL1iXL2i;
	assert forall i :: i in XL2i ==> vsSSA.existsVariable(i);
	temp := setToSeq(XL2i);
	assert XL2i == setOf(temp);
	 
	assert forall i :: i in instances ==> vsSSA.existsVariable(i);
	assert XL2Seq <= instances;
	assert forall i :: i in instances ==> vsSSA.existsVariable(i) && XL2Seq <= instances ==> forall i :: i in XL2Seq ==> vsSSA.existsVariable(i);
	assert forall i :: i in XL2Seq ==> vsSSA.existsVariable(i);
	
	assert forall i :: i in XL2i ==> vsSSA.existsVariable(i);
	assert XL2i == setOf(temp);
	assert forall i :: i in XL2i ==> vsSSA.existsVariable(i) && XL2i == setOf(temp) ==> forall i :: i in temp ==> vsSSA.existsVariable(i);
	assert forall i :: i in temp ==> vsSSA.existsVariable(i);
	
	var XL2iSeq := OrganizeVariables(XL2Seq, XL2Seq, vsSSA);
	
	////////////////////////////////////////

	var XLs' := XLs + setOf(instances);
	var B' := SubstitueBooleanExpression(B, [X1,X2,X3,X4], [XL1i,setOf(XL2Seq),XL3i,XL4f]);
	temp := setToSeq(XL1i); 
	assert XL4f <= setOf(liveOnExitX) && setOf(XL4fSeq) == XL4f ==> setOf(XL4fSeq) <= setOf(liveOnExitX);
	assert forall i :: i in liveOnExitX ==> vsSSA.existsVariable(i);
	 
	assert forall i :: i in temp ==> vsSSA.existsVariable(i);
	assert forall i :: i in XL2Seq ==> vsSSA.existsVariable(i);
	assert forall i :: i in XL3iSeq ==> vsSSA.existsVariable(i);
	assert forall i :: i in XL4fSeq ==> vsSSA.existsVariable(i);
	var liveOnEntryX' := temp + XL2Seq + XL3iSeq + XL4fSeq;

	assert forall i :: i in XL2bSeq ==> vsSSA.existsVariable(i);
	assert forall i :: i in XL4bSeq ==> vsSSA.existsVariable(i);
	var liveOnExitX' := temp + XL2bSeq + XL3iSeq + XL4bSeq;

	assert forall i :: i in liveOnEntryX' ==> vsSSA.existsVariable(i);
	assert forall i :: i in liveOnExitX' ==> vsSSA.existsVariable(i);
	var S' := ToSSA(S, X, liveOnEntryX', liveOnExitX', Y, XLs', vsSSA);
	var DO' := SeqComp(DO(B', S'), Assignment(XL2Seq + XL4fSeq, XL2bSeq + XL4bSeq));
	S'' := SeqComp(Assignment(XL2Seq + XL4fSeq, XL2iSeq + XL4iSeq), DO');
}

method FromSSA(S': Statement, X: seq<Variable>, XL1i: seq<Variable>, XL2f: seq<Variable>, Y: set<Variable>, XLs: set<Variable>, vsSSA: VariablesSSA) returns( S: Statement)
	requires ValidVsSSA(vsSSA)
	requires Valid(S')
	decreases *
	ensures ValidVsSSA(vsSSA)
	ensures Valid(S)
{
	S := MergeVars(S', XLs, X, XL1i, XL2f, Y, vsSSA);
}

method MergeVars(S': Statement, XLs: set<Variable>, X: seq<Variable>, XL1i: seq<Variable>, XL2f: seq<Variable>, Y: set<Variable>, vsSSA: VariablesSSA) returns( S: Statement)
	requires ValidVsSSA(vsSSA)
	requires Valid(S')
	decreases *
	ensures ValidVsSSA(vsSSA)
	ensures Valid(S)
{
	match S' {
		//case Assignment(LHS,RHS) => S := AssignmentFromSSA(LHS, RHS, XLs, X, XL1i, XL2f, Y, vsSSA);
		case Assignment(LHS,RHS) => S := Skip;
		case SeqComp(S1',S2') => S := SeqCompFromSSA(S1', S2', XLs, X, XL1i, XL2f, Y, vsSSA);
		case IF(B0',Sthen',Selse') => S := IfFromSSA(B0', Sthen', Selse', XLs, X, XL1i, XL2f, Y, vsSSA);
		case DO(B',S') => S := DoFromSSA(B', S', XLs, X, XL1i, XL2f, Y, vsSSA);
		case LocalDeclaration(L,S0) => S := Skip;
		case Skip => S := Skip;
	}
}

/*method {:verify false}AssignmentFromSSA(LHS: seq<Variable>, RHS: seq<Expression>, XLs: set<Variable>, X: seq<Variable>, XLi: seq<Variable>, XLf: seq<Variable>, Y: set<Variable>, vsSSA: VariablesSSA) returns (S: Statement)
	requires ValidVsSSA(vsSSA)
	requires Valid(Assignment(LHS,RHS))
	requires forall i :: i in XLi ==> vsSSA.existsVariable(i)
	requires forall i :: i in XLf ==> vsSSA.existsVariable(i)
	ensures ValidVsSSA(vsSSA)
	ensures Valid(S)
{
	// defined in thesis:
	// merge-vars.(" XL1f,XL2,XL3f,XL4,XL5f,XL6,Y1 := XL1i,XL2i,E1',E2',E3',E4',E5' ",
	// XLs, X, (XL1i, XL2i, XL3i, XL4i, XL7i, XL8i), (XL1f, XL3f, XL5f, XL7i), Y) is:
	// " X3,X4,X5,X6,Y1 := E1,E2,E3,E4,E5 "
	
	var Y1 := Y * def(Assignment(LHS, RHS)); // Y1 חיתוך בין Y ל def
	var Y1Seq, E5' := GetXandE(LHS, RHS, Y1);

	var XL7i := setOf(XLi) * setOf(XLf);
	assert XL7i <= setOf(XLi) && XL7i <= setOf(XLf);
	var temp := setToSeq(XL7i);
	var X7Seq := vsSSA.instancesToVariables(temp);
	var X7 := setOf(X7Seq);

	var XL1iXL2i := setOf(XLi) * setOf(RHS);
	assert XL1iXL2i <= setOf(XLi) && XL1iXL2i <= setOf(RHS);
	temp := setToSeq(XL1iXL2i);
	var X1X2 := vsSSA.instancesToVariables(temp);
	var XL3iXL4iXL8i := setOf(XLi) - XL1iXL2i - XL7i;
	assert XL3iXL4iXL8i <= setOf(XLi);
	temp := setToSeq(XL3iXL4iXL8i);
	var X3X4X8 := vsSSA.instancesToVariables(temp);
	var XL1fXL3fXL5f := setOf(XLf) - XL7i;
	assert XL1fXL3fXL5f <= setOf(XLf);
	temp := setToSeq(XL1fXL3fXL5f);
	assert forall i :: i in temp ==> vsSSA.existsVariable(i);
	var X1X3X5 := vsSSA.instancesToVariables(temp);

	var X3 := setOf(X1X3X5) * setOf(X3X4X8);
	temp := setToSeq(X3);
	var X3Instances := vsSSA.getInstancesOfVaribleSeq(temp);
	var XL3fSeq, E1' := GetXandE(LHS, RHS, setOf(X3Instances));

	var XL1fXL5f := XL1fXL3fXL5f - setOf(XL3fSeq);
	assert XL1fXL5f <= XL1fXL3fXL5f;
	temp := setToSeq(XL1fXL5f);
	var X1X5 := vsSSA.instancesToVariables(temp);
	var X1 := setOf(X1X2) * setOf(X1X5);
	temp := setToSeq(X1);
	var X1Instances := vsSSA.getInstancesOfVaribleSeq(temp);
	var XL1i := setOf(RHS) * setOf(X1Instances);
	var XL1f := setOf(LHS) * setOf(X1Instances);
	var XL5f := XL1fXL5f - XL1f;
	var XL5fSeq, E3' := GetXandE(LHS, RHS, XL5f);
	var X5SeqTemp := vsSSA.instancesToVariables(XL5fSeq);
	var X5 := setOf(X5SeqTemp);

	var XL2XL4XL6 := setOf(LHS) - XL1f - setOf(XL3fSeq) - XL5f - Y1;
	var XL2i := XL1iXL2i - XL1i;
	var X2 := setOf(X1X2) - X1;
	temp := setToSeq(X2);
	var X2Instances := vsSSA.getInstancesOfVaribleSeq(temp);
	var XL2 := setOf(RHS) * setOf(X2Instances);
	var XL4XL6 := XL2XL4XL6 - XL2;
	temp := setToSeq(XL4XL6);
	var X4X6 := vsSSA.instancesToVariables(temp);
	var X4 := setOf(X3X4X8) * setOf(X4X6);
	var X6 := setOf(X4X6) - X4;
	temp := setToSeq(X4);
	var X4Instances := vsSSA.getInstancesOfVaribleSeq(temp);
	var XL4 := setOf(X4Instances) * setOf(LHS);
	var XL6 := XL4XL6 - XL4;
	var XL4Seq, E2' := GetXandE(LHS, RHS, XL4);
	var XL6Seq, E4' := GetXandE(LHS, RHS, XL6);

	var X8 := setOf(X3X4X8) - X3 - X4;
	var XL3i := setOf(X3Instances) * setOf(XLi);
	var XL4i := setOf(X4Instances) * setOf(XLi);
	var XL8i := XL3iXL4iXL8i - XL3i - XL4i;

	////////////////////////////////////////

	var X3Seq := InstancesSetToSeq(X3, XL3fSeq, vsSSA);
	var X4Seq := InstancesSetToSeq(X4, XL4Seq, vsSSA);
	var X5Seq := InstancesSetToSeq(X5, XL5fSeq, vsSSA);
	var X6Seq := InstancesSetToSeq(X6, XL6Seq, vsSSA);

	////////////////////////////////////////

	var E1, E2, E3, E4, E5;

	E1 := SubstitueExpressionSeq(E1', [XL1i, XL2i, XL3i, XL4i, XL7i, XL8i], [X1, X2, X3, X4, X7, X8]);
	E2 := SubstitueExpressionSeq(E2', [XL1i, XL2i, XL3i, XL4i, XL7i, XL8i], [X1, X2, X3, X4, X7, X8]);
	E3 := SubstitueExpressionSeq(E3', [XL1i, XL2i, XL3i, XL4i, XL7i, XL8i], [X1, X2, X3, X4, X7, X8]);
	E4 := SubstitueExpressionSeq(E4', [XL1i, XL2i, XL3i, XL4i, XL7i, XL8i], [X1, X2, X3, X4, X7, X8]);
	E5 := SubstitueExpressionSeq(E5', [XL1i, XL2i, XL3i, XL4i, XL7i, XL8i], [X1, X2, X3, X4, X7, X8]);

	S := Assignment(X3Seq + X4Seq + X5Seq + X6Seq + Y1Seq, E1 + E2 + E3 + E4 + E5);
	//S := Skip;
}*/

method {:verify false}SeqCompFromSSA(S1': Statement, S2': Statement, XLs: set<Variable>, X: seq<Variable>, XLi: seq<Variable>, XLf: seq<Variable>, Y: set<Variable>, vsSSA: VariablesSSA) returns (S: Statement)
	requires ValidVsSSA(vsSSA)
	requires Valid(SeqComp(S1',S2'))
	decreases *
	ensures ValidVsSSA(vsSSA)
	ensures Valid(S)
{
	// defined in thesis:
	// merge-vars.(" S1' ; S2' ", XLs, X, XL1i, XL2f, Y) is:
	// " merge-vars.(S1', XLs, X, XL1i, XL3, Y) ; merge-vars.(S2', XLs, X, XL3, XL2f, Y) "

	var XL3 := XLs * ((setOf(XLf) - ddef(S2')) + input(S2'));
	var XL3Seq := setToSeq(XL3);

	var S1 := MergeVars(S1', XLs, X, XLi, XL3Seq, Y, vsSSA);
	var S2 := MergeVars(S2', XLs, X, XL3Seq, XLf, Y, vsSSA);

	S := SeqComp(S1, S2);
}

method {:verify false}IfFromSSA(B' : BooleanExpression, S1' : Statement, S2' : Statement, XLs: set<Variable>, X: seq<Variable>, XLi: seq<Variable>, XLf: seq<Variable>, Y: set<Variable>, vsSSA: VariablesSSA) returns (S: Statement)
	requires ValidVsSSA(vsSSA)
	requires Valid(IF(B',S1',S2'))
	decreases *
	ensures ValidVsSSA(vsSSA)
	ensures Valid(S)
{
	// defined in thesis:
	// merge-vars.(" if B' then S1' else S2' fi ", XLs, X, XL1i, XL2f, Y) is:
	// " if B' then merge-vars.(S1', XLs, X, XL1i, XL2f ,Y) else merge-vars.(S2', XLs, X, XL1i, XL2f, Y) fi "

	var X1 := {};
	var B := SubstitueBooleanExpression(B', [X1], [setOf(XLi)]);

	var S1 := MergeVars(S1', XLs, X, XLi, XLf, Y, vsSSA);
	var S2 := MergeVars(S2', XLs, X, XLi, XLf, Y, vsSSA);

	S := IF(B, S1, S2);
}

method {:verify false}DoFromSSA(B' : BooleanExpression, S' : Statement, XLs: set<Variable>, X: seq<Variable>, XLi: seq<Variable>, XLf: seq<Variable>, Y: set<Variable>, vsSSA: VariablesSSA) returns (S: Statement)
	requires ValidVsSSA(vsSSA)
	requires Valid(DO(B',S'))
	decreases *
	ensures ValidVsSSA(vsSSA)
	ensures Valid(S)
{
	// defined in thesis:
	// merge-vars.(" while B' do S1' od ", XLs, X, (XL1i, XL2i), XL2i, Y) is:
	// " while B do merge-vars.(S1', XLs, X, (XL1i, XL2i), (XL1i, XL2i), Y) od "

	var XL2i := setOf(XLi) * setOf(XLf);
	var XL1i := setOf(XLi) - XL2i;
	var X1 := {}; // TODO
	var X2 := {}; // TODO
	var B := SubstitueBooleanExpression(B', [X1,X2], [XL1i,XL2i]);

	S := MergeVars(S', XLs, X, XLi, XLi, Y, vsSSA);
	S := DO(B, S);
}