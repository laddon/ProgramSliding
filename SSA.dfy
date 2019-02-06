include "Definitions.dfy"
include "Substitutions.dfy"
include "Util.dfy"
include "CorrectnessSSA.dfy"
include "SlideDG.dfy"
include "VarSlideDG.dfy"
include "Slicing.dfy"
include "ProofUtil.dfy"

class VariablesSSA {

	var instancesOf: map<Variable, seq<Variable>>;
	ghost var variableOf: map<Variable, Variable>;
	var n: int;

	constructor () 
		modifies this
		//requires ValidVsSSA(this)
		ensures ValidVsSSA(this)
		ensures |instancesOf| == 0
		ensures |variableOf| == 0
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
		ensures instancesOf == old(instancesOf)
		ensures variableOf == old(variableOf)
	{
		res := n;
		n := n + 1;
	}

	method variablesToSSAVariables(variables: seq<Variable>, instances: seq<Variable>)
		requires ValidVsSSA(this)
		requires |instances| == |variables|
		requires forall i :: i in instances ==> !existsVariable2(i)
		requires forall i,j :: 0 <= i < |instances| && i < j < |instances| ==> instances[i] != instances[j]
		modifies this
		ensures forall i :: i in instances ==> existsVariable2(i)
		ensures forall v :: v in old(instancesOf) ==> v in instancesOf && (forall i :: i in old(instancesOf[v]) ==> i in instancesOf[v])
		ensures forall i :: i in old(variableOf) ==> i in variableOf
		ensures ValidVsSSA(this)
	{
		if !(variables == [])
		{
			addVariable(variables[0], instances[0]);
			variablesToSSAVariables(variables[1..], instances[1..]);
		}
	}

	method addVariable(v: Variable, vSSA: Variable)
		requires ValidVsSSA(this)
		requires !existsVariable2(vSSA)
		modifies this
		ensures existsInstance(v)
		ensures (v in old(instancesOf) ==> forall i :: i in old(instancesOf[v]) ==> i in instancesOf[v])
		ensures forall v' :: v' in old(instancesOf) && v' != v ==> v' in instancesOf && old(instancesOf[v']) == instancesOf[v']
		ensures forall i' :: i' in old(variableOf) && i' != vSSA ==> i' in variableOf && old(variableOf[i']) == variableOf[i']
		ensures forall i' :: i' !in old(variableOf) && i' != vSSA ==> i' !in variableOf
		ensures existsVariable2(vSSA) && variableOf[vSSA] == v && vSSA in instancesOf[v]
		ensures ValidVsSSA(this)

	{
		if v in instancesOf
		{
			addExistingVariable(v, vSSA);
		}
		else
		{
			addNewVariable(v, vSSA);
		}
	}

	method addExistingVariable(v: Variable, vSSA: Variable)
		requires ValidVsSSA(this)
		requires v in instancesOf 
		requires !existsVariable2(vSSA)
		modifies this
		ensures existsInstance(v) && forall i :: i in old(instancesOf[v]) ==> i in instancesOf[v]
		ensures forall v' :: v' in old(instancesOf) && v' != v ==> v' in instancesOf && old(instancesOf[v']) == instancesOf[v']
		ensures forall i' :: i' in old(variableOf) && i' != vSSA ==> i' in variableOf && old(variableOf[i']) == variableOf[i']
		ensures forall i' :: i' !in old(variableOf) && i' != vSSA ==> i' !in variableOf
		ensures existsVariable2(vSSA) && variableOf[vSSA] == v && vSSA in instancesOf[v]
		ensures ValidVsSSA(this)
	{	
		instancesOf := instancesOf[v := instancesOf[v] + [vSSA]];
		variableOf := variableOf[vSSA := v];
	}

	method addNewVariable(v: Variable, vSSA: Variable)
		requires ValidVsSSA(this)
		requires v !in instancesOf
		requires !existsVariable2(vSSA)
		modifies this
		ensures existsInstance(v)
		ensures forall v' :: v' in old(instancesOf) && v' != v ==> v' in instancesOf && old(instancesOf[v']) == instancesOf[v']
		ensures forall i' :: i' in old(variableOf) && i' != vSSA ==> i' in variableOf && old(variableOf[i']) == variableOf[i'] 
		ensures forall i' :: i' !in old(variableOf) && i' != vSSA ==> i' !in variableOf
		ensures existsVariable2(vSSA) && variableOf[vSSA] == v && vSSA in instancesOf[v]
		ensures ValidVsSSA(this)
	{
		instancesOf := instancesOf[v := [vSSA]];
		variableOf := variableOf[vSSA := v];
	}

	predicate addVariableP(v: Variable, vSSA: Variable, oldInstancesOf: map<Variable, seq<Variable>>, res: seq<Variable>)
		reads this
	{
		if (v in oldInstancesOf) then res == oldInstancesOf[v] + [vSSA]  else  res == [vSSA]
	}

	function method getVariableInRegularFormFunc(vSSA: Variable) : (v: Variable)
		requires ValidVsSSA(this)
		requires existsVariable2(vSSA)
		reads this
		ensures ValidVsSSA(this)
		ensures existsInstance(v)
		ensures v == variableOf[vSSA]
	{
		var v' :| v' in instancesOf && vSSA in instancesOf[v'];
		v'
	}

	predicate existsVariable2(vSSA: Variable)
		reads this
		ensures existsVariable2(vSSA) <==> vSSA in variableOf
	{
		vSSA in variableOf
	}

	predicate existsVariable(vSSA: Variable)
		reads this
	{
		exists v :: v in instancesOf && vSSA in instancesOf[v]
	}

	lemma DistinctVariablesLemma(instances: seq<Variable>, V: seq<Variable>)
		requires ValidVsSSA(this)
		requires forall i :: i in instances ==> existsVariable2(i)
		requires V == instancesToVariables(instances)
		ensures (forall index1,index2 :: 0 <= index1 < index2 < |instances| ==> instances[index1] != instances[index2] && variableOf[instances[index1]] != variableOf[instances[index2]])
			==> (forall index1,index2 :: 0 <= index1 < index2 < |V| ==> V[index1] != V[index2])

	function method instancesToVariables(instances: seq<Variable>) : (V: seq<Variable>)
		reads this
		requires ValidVsSSA(this)
		requires forall i :: i in instances ==> existsVariable2(i)
		ensures |instances| == |V|
		ensures forall index :: 0 <= index < |instances| ==> instances[index] in variableOf && variableOf[instances[index]] == V[index]
		ensures forall v :: v in V ==> existsInstance(v)
		ensures ValidVsSSA(this)
		
	{
		if instances == [] then []
		else 
			var v := getVariableInRegularFormFunc(instances[0]);
			var V' := instancesToVariables(instances[1..]);

			[v] + V'
	}

	/*method instancesToVariablesSet(instances: set<Variable>) returns (V : set<Variable>)
		requires ValidVsSSA(this)
		requires forall i :: i in instances ==> existsVariable2(i)
		requires forall i, j :: i in instances && j in instances && i != j ==> getVariableInRegularFormFunc(i) != getVariableInRegularFormFunc(j)
		decreases instances
		ensures |instances| == |V|
		ensures forall v :: v in V ==> existsInstance(v)
		ensures ValidVsSSA(this)
		
	{
		if instances == {} { V := {}; } 
		else { 
			var i :| i in instances;
			assert |{i}| == 1;
			var v := getVariableInRegularForm(i);
			assert getVariableInRegularFormFunc(i) == v;
			var V' := instancesToVariablesSet(instances - {i});
			assert |V'| == |instances| - 1;

			V := {v} + V';
			assert {v} * V' == {};

			calc {
				|V|;
			==	
				|{v}|+|V'|;
			==	{ assert |V'| == |instances| - 1; }
				|{v}| + |instances| - 1;
			==	{ assert |{v}| == 1; }
				1 + |instances| - 1;
			==
				|instances|;
			}
		}
	}*/

	predicate existsInstance(v: Variable)
		reads this
	{
		v in instancesOf && |instancesOf[v]| >= 1
	}

	function method getInstancesOfVaribleFunc(v : Variable) : seq<Variable>
		requires ValidVsSSA(this)
		requires existsInstance(v)
		//decreases 1
		reads this
		ensures |getInstancesOfVaribleFunc(v)| >= 1
		ensures ValidVsSSA(this)
		ensures forall i :: i in getInstancesOfVaribleFunc(v) ==> existsVariable2(i)
		//ensures forall i :: i in getInstancesOfVaribleFunc(v) ==> getVariableInRegularFormFunc(i) == v
	{
		instancesOf[v]
	}

	method getInstancesOfVarible(v : Variable) returns (instances : seq<Variable>)
		requires ValidVsSSA(this)
		requires existsInstance(v)
		ensures |instances| >= 1
		ensures ValidVsSSA(this)
		ensures forall i :: i in instances ==> existsVariable2(i)
	{
		instances := instancesOf[v];
	}

	method getInstancesOfVaribleSeq(V : seq<Variable>) returns (instances : seq<Variable>)
		requires ValidVsSSA(this)
		requires forall v :: v in V ==> existsInstance(v)
		ensures ValidVsSSA(this)
		ensures forall i :: i in instances ==> existsVariable2(i)
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
		requires forall v :: v in allVars ==> v in instancesOf
	{
		if (allVars == []) then [] else instancesOf[allVars[0]] + getAllInstances(allVars[1..])
	}
}

method Main()
{
	print "hello!";

}


predicate ValidVsSSA(vsSSA: VariablesSSA) reads vsSSA
{
	vsSSA != null && vsSSA.n >= 1 && (forall v :: v in vsSSA.instancesOf ==> |vsSSA.instancesOf[v]| >= 1)
	&& (forall i :: i in vsSSA.variableOf ==> vsSSA.variableOf[i] in vsSSA.instancesOf && i in vsSSA.instancesOf[vsSSA.variableOf[i]])
	&& (forall v :: v in vsSSA.instancesOf ==> (forall i :: i in vsSSA.instancesOf[v] ==> i in vsSSA.variableOf && vsSSA.variableOf[i] == v))
	&& (forall v :: v in vsSSA.instancesOf ==> vsSSA.existsInstance(v)) && (forall i :: i in vsSSA.variableOf ==> vsSSA.existsVariable2(i))
}


/*predicate p(nStr: string, existingInstances: set<seq<string>>)
{
	var i :| i in existingInstances;
	
	if (existingInstances == {}) then true
	else if (i[1] == nStr) then false
	else p(nStr, existingInstances - {i})
}*/


 method freshInit(vars : seq<Variable>, allVars : set<Variable>, vsSSA : VariablesSSA) returns (res: seq<Variable>)
	requires ValidVsSSA(vsSSA)
	requires forall v :: v in vsSSA.instancesOf ==> v in allVars
	requires forall i :: i in vsSSA.variableOf ==> i in allVars
	ensures |res| == |vars|
	modifies vsSSA
	ensures ValidVsSSA(vsSSA)
	ensures vsSSA.instancesOf == old(vsSSA.instancesOf)
	ensures vsSSA.variableOf == old(vsSSA.variableOf)
	ensures forall i :: i in res ==> !vsSSA.existsVariable2(i)
{
	if vars == [] { res := []; } 
	else
	{
		var n := vsSSA.getAndIncN();
		var nStr := intToString(n);
		var newInstance := vars[0] + nStr;
		ghost var existingInstances := {};

		/*var newInstanceStr := vars[0] + nStr;
		var newInstanceSeq := [vars[0], nStr];
		assert newInstanceSeq[0] + newInstanceSeq[1] == newInstanceStr;
		ghost var existingInstancesStr := {};
		ghost var existingInstancesSeq := {};

		while newInstanceStr in allVars
			invariant vsSSA.variableOf == old(vsSSA.variableOf)
			invariant vsSSA.instancesOf == old(vsSSA.instancesOf)
			invariant newInstanceStr !in existingInstancesStr
			invariant newInstanceSeq !in existingInstancesSeq
			invariant ValidVsSSA(vsSSA)
			decreases allVars - existingInstancesStr
		{
			assert newInstanceStr in allVars;
			assert newInstanceStr !in existingInstancesStr;
			assert newInstanceSeq !in existingInstancesSeq;
			existingInstancesStr := existingInstancesStr + {newInstanceStr};
			existingInstancesSeq := existingInstancesSeq + {newInstanceSeq};

			n := vsSSA.getAndIncN();
			nStr := intToString(n);
			//assert !p(nStr, existingInstancesSeq);
			// make sure that nStr is not in existingInstancesSeq
			newInstanceSeq := [vars[0], nStr];

			assume newInstanceSeq !in existingInstancesSeq;
			newInstanceStr := vars[0] + nStr;			
			assert newInstanceSeq[0] + newInstanceSeq[1] == newInstanceStr;
			assert newInstanceStr !in existingInstancesStr;
			
			//newInstanceStr := vars[0] + nStr;			
			//assert newInstanceStr !in existingInstancesStr;
			//assert newInstanceSeq !in existingInstancesSeq;
		}

		assert !vsSSA.existsVariable2(newInstanceStr) by {
			assert forall i :: i in old(vsSSA.variableOf) ==> i in allVars;
			assert vsSSA.variableOf == old(vsSSA.variableOf);
			assert forall i :: i in vsSSA.variableOf ==> i in allVars;
			assert newInstanceStr !in allVars;
			assert newInstanceStr !in vsSSA.variableOf;
		}
		var res' := freshInit(vars[1..], allVars + {newInstanceStr}, vsSSA);
		res := [newInstanceStr] + res';*/

		ghost var originalN := vsSSA.n;
		ghost var i := 0;

		while newInstance in allVars
			invariant vsSSA.variableOf == old(vsSSA.variableOf)
			invariant vsSSA.instancesOf == old(vsSSA.instancesOf)
			invariant newInstance !in existingInstances
			invariant ValidVsSSA(vsSSA)
			invariant forall num :: originalN <= num < vsSSA.n ==> ((vars[0] + intToString(num)) in existingInstances) && (i == |existingInstances|)
			invariant originalN + i == vsSSA.n
			invariant vars[0] + intToString(vsSSA.n) !in existingInstances
			decreases allVars - existingInstances
		{
			assert newInstance in allVars;
			assert newInstance !in existingInstances;
			existingInstances := existingInstances + {newInstance};

			assert vars[0] + intToString(vsSSA.n) !in existingInstances;
			n := vsSSA.getAndIncN();
			assert vars[0] + intToString(vsSSA.n-1) !in existingInstances;
			///???assert vars[0] + intToString(originalN+i-1) !in existingInstances;
			nStr := intToString(n);
			assert vars[0] + nStr !in existingInstances by {
				assert nStr == intToString(originalN+i+1);
			}
			
			newInstance := vars[0] + nStr;			
			assert newInstance !in existingInstances;
			i := i + 1;
		}
		
		assert !vsSSA.existsVariable2(newInstance) by {
			assert forall i :: i in old(vsSSA.variableOf) ==> i in allVars;
			assert vsSSA.variableOf == old(vsSSA.variableOf);
			assert forall i :: i in vsSSA.variableOf ==> i in allVars;
			assert newInstance !in allVars;
			assert newInstance !in vsSSA.variableOf;
		}
		var res' := freshInit(vars[1..], allVars + {newInstance}, vsSSA);
		res := [newInstance] + res';
	}
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
	ensures forall i,j :: 0 <= i < |res| && i < j < |res| ==> res[i] != res[j]
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
	ensures setOf(XSeq) <= setOf(LHS);
{
	if LHS == [] { XSeq:= []; ESeq := []; indexSeq := []; }
	else
	{
		var x, e, i;
		var isVariableInSet := IsVariableInSet(LHS[0], X);
		
		if isVariableInSet == true
		{
			x := [LHS[0]];
			e := [RHS[0]];
			i := [index];
		}
		else
		{
			x := [];
			e := [];
			i := [];
		}
		assert x == [] || x == [LHS[0]];
		assert x <= [LHS[0]];
		var XSeq', ESeq', indexSeq' := GetXandE(LHS[1..], RHS[1..], X, index + 1);

		XSeq := x + XSeq';

		assert setOf(XSeq) <= setOf(LHS) by { calc {
			setOf(XSeq);
		== 
			setOf(x + XSeq');
		<=
			setOf(x + LHS[1..]);
		<= { assert x <= [LHS[0]] && LHS[1..] == LHS[1..] ==> setOf(x + LHS[1..]) <= setOf([LHS[0]] + LHS[1..]); }
			setOf([LHS[0]] + LHS[1..]);
		== 
			setOf(LHS);
		}}

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
	else if i in vsSSA.instancesOf[x] { x' := i; }
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
// ensures |B| == |B'|
	ensures B == B' // FIXME: replace with an appropriate call to one of the functions in the new "Substitutions.dfy"
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
	requires forall v :: v in LHS ==> |instances * setOf(vsSSA.getInstancesOfVaribleFunc(v))| == 1
	ensures |LHS'| == |LHS|
{
	if LHS == [] { LHS' := []; }
	else
	{
		var instancesOfLHS0 := vsSSA.getInstancesOfVaribleFunc(LHS[0]);
		var i := instances * setOf(instancesOfLHS0);	
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

method GetNewRHS(indices: seq<int>, E: seq<Expression>, index: int) returns (RHS': seq<Expression>)
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

/*method GetNewRHS2(indices: seq<int>, E: seq<Expression>) returns (RHS': seq<Variable>)
	requires |indices| == |E|
	requires forall index :: index in indices ==> 0 <= index < |indices|
	//ensures |RHS'| == |indices|
{
	var RHSarray := new Expression[|indices|];
	var i := 0;

	while i < |indices|
		invariant 0 <= i 
	{
		RHSarray[indices[i]] := E[i];
		i := i + 1;
	}

	RHS' := [];
}*/

method OrganizeVariables4(instances: seq<Variable>, vsSSA: VariablesSSA) returns (res: seq<Variable>)
	requires ValidVsSSA(vsSSA)
	requires forall v :: v in instances ==> vsSSA.existsVariable2(v)
	decreases instances
	ensures forall i :: i in res ==> vsSSA.existsInstance(i)
	ensures |instances| == |res|
	ensures ValidVsSSA(vsSSA)	
{
	// For example:
	// instances = [sum2, i2]
	// res = [sum, i]

	if instances == [] { res := []; }
	else
	{
		var v := vsSSA.getVariableInRegularFormFunc(instances[0]);
		var res' := OrganizeVariables4(instances[1..], vsSSA);

		res := [v] + res';

	}
}

predicate matching1(vars: seq<Variable>, instances: seq<Variable>, vsSSA: VariablesSSA)
	requires ValidVsSSA(vsSSA)
	decreases vars
	reads vsSSA
	requires forall i :: i in instances ==> i in vsSSA.variableOf
	//requires forall i :: i in instances ==> vsSSA.existsVariable2(i)
	
{
	if vars == [] then instances == [] else 
	instances != [] &&  vars[0] == vsSSA.variableOf[instances[0]] && matching1(vars[1..], instances[1..], vsSSA)
}

method OrganizeVariables3(vars1: seq<Variable>, instances2: set<Variable>, vsSSA: VariablesSSA) returns (res: seq<Variable>)
	requires ValidVsSSA(vsSSA)
	requires forall v :: v in vars1 ==> vsSSA.existsInstance(v)
	requires forall i :: i in instances2 ==> vsSSA.existsVariable2(i)
	requires forall i,j :: 0 <= i < |vars1| && i < j < |vars1| ==> vars1[i] != vars1[j]
	requires forall v :: v in vars1 ==> |instances2 * setOf(vsSSA.getInstancesOfVaribleFunc(v))| == 1
	//requires forall v1,v2 :: v1 in vars1 && v2 in vars1 && v1 != v2 ==> setOf(vsSSA.getInstancesOfVaribleFunc(v1)) !! setOf(vsSSA.getInstancesOfVaribleFunc(v2))
	decreases vars1
	ensures forall i :: i in res ==> vsSSA.existsVariable2(i)
	ensures matching1(vars1, res, vsSSA)
	ensures |vars1| == |res|
	ensures ValidVsSSA(vsSSA)
{
	// For example:
	// vars1 = [sum, i]
	// instances2 = {i2, sum2}
	// res = [sum2, i2]

	if vars1 == [] { res := []; }
	else
	{
		var instances1 := vsSSA.getInstancesOfVaribleFunc(vars1[0]);				// instances1 := [sum1, sum2, sum3, ...]
		var i1Set := setOf(instances1) * instances2;								// i1Set := {sum2}

		assert |i1Set| == 1 by {
			calc {
				|i1Set|;
			==
				|setOf(instances1) * instances2|;
			==
				|setOf(vsSSA.getInstancesOfVaribleFunc(vars1[0])) * instances2|;
			==	{ assert setOf(vsSSA.getInstancesOfVaribleFunc(vars1[0])) * instances2 ==
						instances2 * setOf(vsSSA.getInstancesOfVaribleFunc(vars1[0])); }
				|instances2 * setOf(vsSSA.getInstancesOfVaribleFunc(vars1[0]))|;
			==
				1;
			}
		}

		var i1 :| i1 in i1Set;														// i1 := sum2
		assert vsSSA.variableOf[i1] == vars1[0];

		var vars1' := vars1[1..];													// vars1' := [i]
		var instances2' := instances2 - i1Set;										// instances2' := {i2}


		forall v' | v' in vars1' ensures |instances2' * setOf(vsSSA.getInstancesOfVaribleFunc(v'))| == 1 {
			assert v' in vars1;
			assert |instances2 * setOf(vsSSA.getInstancesOfVaribleFunc(v'))| == 1;
			assert setOf(vars1') == setOf(vars1) - {vars1[0]};
			calc {
				|instances2' * setOf(vsSSA.getInstancesOfVaribleFunc(v'))|;
			==
				|(instances2 - i1Set) * setOf(vsSSA.getInstancesOfVaribleFunc(v'))|;
			== {
				assert |i1Set * setOf(vsSSA.getInstancesOfVaribleFunc(v'))| == 0 by
				{
					assert i1Set <= setOf(vsSSA.getInstancesOfVaribleFunc(vars1[0]));
					assert i1Set !! setOf(vsSSA.getInstancesOfVaribleFunc(v')) by {
						assert setOf(vsSSA.getInstancesOfVaribleFunc(vars1[0])) !!
							setOf(vsSSA.getInstancesOfVaribleFunc(v')) by {
								assert v' != vars1[0];
							}
						}
					}
				}
				|(instances2 - i1Set) * setOf(vsSSA.getInstancesOfVaribleFunc(v'))|+
				|i1Set * setOf(vsSSA.getInstancesOfVaribleFunc(v'))|;
			==
				|((instances2 - i1Set) * setOf(vsSSA.getInstancesOfVaribleFunc(v')))+
				 (i1Set * setOf(vsSSA.getInstancesOfVaribleFunc(v')))|;
			== { assert forall A:set<Variable>,B:set<Variable>,C:set<Variable> :: ((A*C)+(B*C)) == ((A+B)*C);}
				|((instances2 - i1Set) + i1Set) * setOf(vsSSA.getInstancesOfVaribleFunc(v'))|;
			== { assert (instances2 - i1Set) + i1Set == instances2 by { assert i1Set <= instances2; } }
				|instances2 * setOf(vsSSA.getInstancesOfVaribleFunc(v'))|;
			==
				1;
			}
		}
		var res' := OrganizeVariables3(vars1', instances2', vsSSA);

		res := [i1] + res';
	}
}

method ToSSA(S: Statement, X: seq<Variable>, liveOnEntryX: set<Variable>, liveOnExitX: set<Variable>, Y: set<Variable>, XLs: set<Variable>, vsSSA: VariablesSSA) returns(S': Statement)
	requires Valid(S)
	requires (Core(S))
	requires ValidVsSSA(vsSSA)
	//requires S.Assignment? ==> setOf(S.LHS) <= (setOf(X) + Y)
	requires forall i :: i in liveOnEntryX ==> vsSSA.existsVariable2(i)
	requires forall i :: i in liveOnExitX ==> vsSSA.existsVariable2(i)
	requires forall i1, i2 :: i1 in liveOnEntryX && i2 in liveOnEntryX ==> i1 in vsSSA.variableOf && i2 in vsSSA.variableOf && vsSSA.variableOf[i1] != vsSSA.variableOf[i2]
	requires forall i1, i2 :: i1 in liveOnExitX && i2 in liveOnExitX ==> i1 in vsSSA.variableOf && i2 in vsSSA.variableOf && vsSSA.variableOf[i1] != vsSSA.variableOf[i2]
	requires forall v :: v in X ==> vsSSA.existsInstance(v)
	requires forall v :: v in Y ==> vsSSA.existsInstance(v)
	modifies vsSSA
	decreases *
	ensures Valid(S')
	ensures ValidVsSSA(vsSSA)
	ensures forall i :: i in liveOnEntryX ==> vsSSA.existsVariable2(i)
	ensures forall i :: i in liveOnExitX ==> vsSSA.existsVariable2(i)
	ensures forall v :: v in X ==> vsSSA.existsInstance(v)
	ensures forall v :: v in Y ==> vsSSA.existsInstance(v)
	ensures forall v :: v in old(vsSSA.instancesOf) ==> v in vsSSA.instancesOf && (forall i :: i in old(vsSSA.instancesOf[v]) ==> i in vsSSA.instancesOf[v])
//	ensures CorrectnessOfToSSA(S,S',X,liveOnEntryX,liveOnExitX,Y,XLs,vsSSA)

	/*ensures var slidesS := allSlides(S); var varSlidesS' := allVarSlides(S');
			forall s :: s in slidesS ==> (var s' := VarSlideOf(S, S', slide); s' in varSlidesS'
			&& LabelCorrespondence(assert exists l :: s.0 == CFGNode.Node(l); match s.0 { case Node(l) => l }), VarLabelOfSlide(S, S', s))*/

	//ensures MergedVars1(S', S, XLs from vsSSA - all instances, X)
{
	match S {
		case Assignment(LHS,RHS) => S' := Skip;//AssignmentToSSA(LHS, RHS, X, liveOnEntryX, liveOnExitX, Y, XLs, vsSSA);
		case SeqComp(S1,S2) => S' := Skip;//SeqCompToSSA(S1, S2, X, liveOnEntryX, liveOnExitX, Y, XLs, vsSSA);
		case IF(B0,Sthen,Selse) => S' := Skip;//IfToSSA(B0, Sthen, Selse, X, liveOnEntryX, liveOnExitX, Y, XLs, vsSSA);
		case DO(B,S) => S' := Skip;//DoToSSA(B, S, X, liveOnEntryX, liveOnExitX, Y, XLs, vsSSA);
		case Skip => S' := Skip;
	}
}

function method {:verify false}RenameToSSA(S: Statement, num: int): (Statement,int)  // Should be called with: num == 1
{
	match S {
		case Assignment(LHS,RHS) => RenameAssignmentToSSA(LHS, RHS, num)
									// x,y,z,=1,2,3    x1,y2,z3 = 1,2,3
		case SeqComp(S1,S2) =>		var s1 := RenameToSSA(S1, num);
									var s2 := RenameToSSA(S2, s1.1);
									(SeqComp(s1.0, s2.0), s2.1)
		case IF(B0,Sthen,Selse) =>	var b := RenameBoolExpToSSA(B0, num);
									var st := RenameToSSA(Sthen, num);
									var se := RenameToSSA(Selse, st.1);
									(IF(b, st.0, se.0), se.1)
		case DO(B,S1) =>			var b := RenameBoolExpToSSA(B, num);
									var sloop := RenameToSSA(S1, num);
									(DO(b, sloop.0), sloop.1)
		case Skip =>				(Skip, num)
	}
}

function method {:verify false}RenameBoolExpToSSA(B: BooleanExpression, num: int): (B': BooleanExpression)

function method {:verify false}RenameAssignmentToSSA(LHS: seq<Variable>, RHS: seq<Expression>, num: int): (Statement,int)
/*{
	if LHS == [] then (Skip,num) else
	{
		var numL := num;
		var numStrL := intToString(numL);
		var vL: Variable := LHS[0] + numStrL;

		var numR := numL + 1;
		var numStrR := intToString(numR);
		var vR: Expression := RHS[0] + numStrR;

		var S' := RenameAssignmentToSSA(LHS[1..], RHS[1..], numR+1);

		match S'.0 {
		case Assignment(LHS',RHS') => (Assignment([vL]+LHS',[vR]+RHS'), S'.1)
		}
	}
}*/

method {:verify false}AssignmentToSSA(LHS: seq<Variable>, RHS: seq<Expression>, X: seq<Variable>, liveOnEntryX: set<Variable>, liveOnExitX: set<Variable>, Y: set<Variable>, XLs: set<Variable>, vsSSA: VariablesSSA) returns (S': Statement)
	requires ValidVsSSA(vsSSA)
	requires Valid(Assignment(LHS,RHS))
	requires forall i :: i in liveOnEntryX ==> vsSSA.existsVariable2(i)
	requires forall i :: i in liveOnExitX ==> vsSSA.existsVariable2(i)
	requires forall i1, i2 :: i1 in liveOnEntryX && i2 in liveOnEntryX ==> i1 in vsSSA.variableOf && i2 in vsSSA.variableOf && vsSSA.variableOf[i1] != vsSSA.variableOf[i2]
	requires forall i1, i2 :: i1 in liveOnExitX && i2 in liveOnExitX ==> i1 in vsSSA.variableOf && i2 in vsSSA.variableOf && vsSSA.variableOf[i1] != vsSSA.variableOf[i2]
	requires forall x :: x in X ==> vsSSA.existsInstance(x)
	requires forall y :: y in Y ==> vsSSA.existsInstance(y)
	requires setOf(LHS) <= (setOf(X) + Y)
	modifies vsSSA
	ensures Valid(S')
	ensures ValidVsSSA(vsSSA)
	ensures forall i :: i in liveOnEntryX ==> vsSSA.existsVariable2(i)
	ensures forall i :: i in liveOnExitX ==> vsSSA.existsVariable2(i)
	ensures forall v :: v in X ==> vsSSA.existsInstance(v)
	ensures forall v :: v in Y ==> vsSSA.existsInstance(v)
	ensures forall v :: v in old(vsSSA.instancesOf) ==> v in vsSSA.instancesOf && (forall i :: i in old(vsSSA.instancesOf[v]) ==> i in vsSSA.instancesOf[v])
{
	// הפונקציה עוברת קימפול! :)
	// רק 2 דקות דרך cmd.


	// defined in thesis:
	// toSSA.("X4,X2,X5,X6,Y1 := E1,E2,E3,E4,E5",
	// X, (XL1i, XL2i, XL3i, XL4i), (XL3i, XL4f ,XL5f), Y ,XLs)) is:
	// "XL4f, XL2, XL5f, XL6, Y1 := E1', E2', E3', E4', E5'"

	//// find X1,X2,X3,X4,X5,X6,Y1 SETS ////

	var XL3i := liveOnEntryX * liveOnExitX;
	assert XL3i <= liveOnEntryX && XL3i <= liveOnExitX;
	var temp := setToSeq(XL3i);
	var X3Seq := vsSSA.instancesToVariables(temp);
	var X3 := setOf(X3Seq);

	var XL1iXL2iXL4i := liveOnEntryX - XL3i;
	assert XL1iXL2iXL4i <= liveOnEntryX;
	temp := setToSeq(XL1iXL2iXL4i);
	var X1X2X4 := vsSSA.instancesToVariables(temp);
	var XL4fXL5f := liveOnExitX - XL3i;
	assert XL4fXL5f <= liveOnExitX;
	temp := setToSeq(XL4fXL5f);
	var X4X5 := vsSSA.instancesToVariables(temp);
	var X4 := setOf(X1X2X4) * setOf(X4X5) * setOf(X);
	var X5 := setOf(X4X5) - X4;

	var X1X2 := setOf(X1X2X4) - X4;
	var X2 := X1X2 * def(Assignment(LHS,RHS));
	var X1 := X1X2 - X2;

	var X6Y1 := liveOnEntryX - X4 - X2 - X5;
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
		 
		assume forall i :: i in XL2XL6 ==> !vsSSA.existsVariable2(i);
		assume forall i,j :: 0 <= i < |XL2XL6| && i < j < |XL2XL6| ==> XL2XL6[i] != XL2XL6[j];
		vsSSA.variablesToSSAVariables(X2Seq + X6Seq, XL2XL6);
		assert forall v :: v in (setOf(X) + Y) ==> vsSSA.existsInstance(v);

	////////////////////////////////////////
	
	var instances := XL4f + setOf(XL2XL6[..|X2Seq|]) + XL5f + setOf(XL2XL6[|X2Seq|..]) + Y1;
	assume forall v :: v in LHS ==> |instances * setOf(vsSSA.getInstancesOfVaribleFunc(v))| == 1;
	var LHS' := GetNewLHS(LHS, instances, vsSSA);
	assert |LHS'| == |LHS|;

	var RHS' := GetNewRHS(indexSeqX4 + indexSeqX2 + indexSeqX5 + indexSeqX6 + indexSeqY1, E1' + E2' + E3' + E4' + E5', 0);
	assume |RHS'| == |RHS|;

	S' := Assignment(LHS', RHS');
	assert Valid(S');
}

method {:verify false}SeqCompToSSA(S1: Statement, S2: Statement, X: seq<Variable>, liveOnEntryX: set<Variable>, liveOnExitX: set<Variable>, Y: set<Variable>, XLs: set<Variable>, vsSSA: VariablesSSA) returns (S': Statement)
	requires Valid(SeqComp(S1, S2))
	requires ValidVsSSA(vsSSA)
	requires forall i :: i in liveOnEntryX ==> vsSSA.existsVariable2(i)
	requires forall i :: i in liveOnExitX ==> vsSSA.existsVariable2(i)
	requires forall i1, i2 :: i1 in liveOnEntryX && i2 in liveOnEntryX ==> i1 in vsSSA.variableOf && i2 in vsSSA.variableOf && vsSSA.variableOf[i1] != vsSSA.variableOf[i2]
	requires forall i1, i2 :: i1 in liveOnExitX && i2 in liveOnExitX ==> i1 in vsSSA.variableOf && i2 in vsSSA.variableOf && vsSSA.variableOf[i1] != vsSSA.variableOf[i2]
	requires forall v :: v in X ==> vsSSA.existsInstance(v)
	requires forall v :: v in Y ==> vsSSA.existsInstance(v)
	modifies vsSSA
	decreases *
	ensures Valid(S')
	ensures ValidVsSSA(vsSSA)
	ensures forall i :: i in liveOnEntryX ==> vsSSA.existsVariable2(i)
	ensures forall i :: i in liveOnExitX ==> vsSSA.existsVariable2(i)
	ensures forall v :: v in X ==> vsSSA.existsInstance(v)
	ensures forall v :: v in Y ==> vsSSA.existsInstance(v)
	ensures forall v :: v in old(vsSSA.instancesOf) ==> v in vsSSA.instancesOf && (forall i :: i in old(vsSSA.instancesOf[v]) ==> i in vsSSA.instancesOf[v])
{

	// הפונקציה עוברת קימפול! :)
	// 2:15 שעות דרך cmd.


	// defined in thesis:
	// toSSA.(" S1 ; S2 ", X, (XL1i, XL2i, XL3i, XL4i), (XL3i, XL4f, XL5f), Y, XLs) is:
	// " S1' ; S2' "

	var XL3i := liveOnEntryX * liveOnExitX;
	assert XL3i <= liveOnEntryX && XL3i <= liveOnExitX;
	assert forall i1, i2 :: i1 in XL3i && i2 in XL3i ==> i1 in vsSSA.variableOf && i2 in vsSSA.variableOf && vsSSA.variableOf[i1] != vsSSA.variableOf[i2];
	var temp := setToSeq(XL3i);
	var X3Seq := vsSSA.instancesToVariables(temp);
	var X3 := setOf(X3Seq) * setOf(X);
	
	temp := setToSeq(liveOnEntryX);
	var liveOnEntryXVariables := vsSSA.instancesToVariables(temp);
	temp := setToSeq(liveOnExitX);
	var liveOnExitXVariables := vsSSA.instancesToVariables(temp);
	var X3X4 := setOf(liveOnEntryXVariables) * setOf(liveOnExitXVariables);
	var X4 := (X3X4 - X3) * setOf(X);
	var X5 := (setOf(liveOnExitXVariables) - X3X4) * setOf(X);

	var X1X2 := setOf(liveOnEntryXVariables) - X3X4;
	var X2 := (X1X2 * (def(S1) + def(S2))) * setOf(X);
	assert X2 <= setOf(X);
	var X1 := (X1X2 - X2) * setOf(X);

	var XL1iXL2iXL4i := liveOnEntryX - XL3i;
	
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

	var XL4fXL5f := liveOnExitX - XL3i;
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
	
		assume forall i :: i in XL61Seq ==> !vsSSA.existsVariable2(i);
		assume forall i,j :: 0 <= i < |XL61Seq| && i < j < |XL61Seq| ==> XL61Seq[i] != XL61Seq[j];
		// עובד אבל אולי מיותר? // assert forall i,j :: 0 <= i < |X61Seq| && i < j < |X61Seq| ==> X61Seq[i] != X61Seq[j];
		vsSSA.variablesToSSAVariables(X61Seq, XL61Seq);
		// צריך להוכיח את השורה הבאה:
		assume forall i1, i2 :: i1 in XL61Seq && i2 in XL61Seq ==> i1 in vsSSA.variableOf && i2 in vsSSA.variableOf && vsSSA.variableOf[i1] != vsSSA.variableOf[i2];
		assert forall i :: i in XL61Seq ==> vsSSA.existsVariable2(i);
//0:40
/*	assert forall v :: v in X ==> vsSSA.existsInstance(v);
	assert X1 <= setOf(X) && forall v :: v in X1 ==> vsSSA.existsInstance(v);
	temp := setToSeq(X1);
	var XL11iTemp := vsSSA.getInstancesOfVaribleSeq(temp);
	assert forall i :: i in XL11iTemp ==> vsSSA.existsVariable2(i);
	var XL11iSeq := setToSeq(setOf(XL11iTemp) * XL1i);
	assert setOf(XL11iSeq) <= setOf(XL11iTemp) && forall i :: i in XL11iSeq ==> vsSSA.existsVariable2(i);
	assert forall i1, i2 :: i1 in XL11iSeq && i2 in XL11iSeq ==> i1 in vsSSA.variableOf && i2 in vsSSA.variableOf && vsSSA.variableOf[i1] != vsSSA.variableOf[i2];
//1:30
	assert forall v :: v in X ==> vsSSA.existsInstance(v);
	assert X2 <= setOf(X) && forall v :: v in X2 ==> vsSSA.existsInstance(v);
	temp := setToSeq(X2);
	var XL21iTemp := vsSSA.getInstancesOfVaribleSeq(temp);
	assert forall i :: i in XL21iTemp ==> vsSSA.existsVariable2(i);
	var XL21iSeq := setToSeq(setOf(XL21iTemp) * XL2i);
	assert setOf(XL21iSeq) <= setOf(XL21iTemp) && forall i :: i in XL21iSeq ==> vsSSA.existsVariable2(i);
	assert forall i1, i2 :: i1 in XL21iSeq && i2 in XL21iSeq ==> i1 in vsSSA.variableOf && i2 in vsSSA.variableOf && vsSSA.variableOf[i1] != vsSSA.variableOf[i2];
//2:40	
	assert forall v :: v in X ==> vsSSA.existsInstance(v);
	assert X4 <= setOf(X) && forall v :: v in X4 ==> vsSSA.existsInstance(v);
	temp := setToSeq(X4);
	var XL41iTemp := vsSSA.getInstancesOfVaribleSeq(temp);
	assert forall i :: i in XL41iTemp ==> vsSSA.existsVariable2(i);
	var XL41iSeq := setToSeq(setOf(XL41iTemp) * XL4i);
	assert setOf(XL41iSeq) <= setOf(XL41iTemp) && forall i :: i in XL41iSeq ==> vsSSA.existsVariable2(i);
	assert forall i1, i2 :: i1 in XL41iSeq && i2 in XL41iSeq ==> i1 in vsSSA.variableOf && i2 in vsSSA.variableOf && vsSSA.variableOf[i1] != vsSSA.variableOf[i2];
//5:40
	assert forall v :: v in X ==> vsSSA.existsInstance(v);
	assert X4 <= setOf(X) && forall v :: v in X4 ==> vsSSA.existsInstance(v);
	temp := setToSeq(X4);
	var XL42fTemp := vsSSA.getInstancesOfVaribleSeq(temp);
	assert forall i :: i in XL42fTemp ==> vsSSA.existsVariable2(i);
	var XL42fSeq := setToSeq(setOf(XL42fTemp) * XL4f);
	assert setOf(XL42fSeq) <= setOf(XL42fTemp) && forall i :: i in XL42fSeq ==> vsSSA.existsVariable2(i);
	assert forall i1, i2 :: i1 in XL42fSeq && i2 in XL42fSeq ==> i1 in vsSSA.variableOf && i2 in vsSSA.variableOf && vsSSA.variableOf[i1] != vsSSA.variableOf[i2];
//10:00
	assert forall v :: v in X ==> vsSSA.existsInstance(v);
	assert X5 <= setOf(X) && forall v :: v in X5 ==> vsSSA.existsInstance(v);
	temp := setToSeq(X5);
	var XL51fTemp := vsSSA.getInstancesOfVaribleSeq(temp);
	assert forall i :: i in XL51fTemp ==> vsSSA.existsVariable2(i);
	var XL51fSeq := setToSeq(setOf(XL51fTemp) * XL5f);
	assert setOf(XL51fSeq) <= setOf(XL51fTemp) && forall i :: i in XL51fSeq ==> vsSSA.existsVariable2(i);
	assert forall i1, i2 :: i1 in XL51fSeq && i2 in XL51fSeq ==> i1 in vsSSA.variableOf && i2 in vsSSA.variableOf && vsSSA.variableOf[i1] != vsSSA.variableOf[i2];
//18:30	
	temp := setToSeq(XL3i);
	assert forall i :: i in XL3i ==> vsSSA.existsVariable2(i);
	assert forall i :: i in temp ==> vsSSA.existsVariable2(i);

	var XL6 := setOf(XL11iSeq) + setOf(XL21iSeq) + setOf(temp) + setOf(XL41iSeq) + setOf(XL42fSeq) + setOf(XL51fSeq) + setOf(XL61Seq);

	assert forall i :: i in XL6 ==> vsSSA.existsVariable2(i);
	assert forall i1, i2 :: i1 in XL6 && i2 in XL6 ==> i1 in vsSSA.variableOf && i2 in vsSSA.variableOf && vsSSA.variableOf[i1] != vsSSA.variableOf[i2];
	var XLs' := XLs + setOf(XL61Seq);
	var S1' := ToSSA(S1, X, liveOnEntryX, XL6, Y, XLs', vsSSA);

	assert forall i :: i in XL6 ==> vsSSA.existsVariable2(i);
	assert forall i1, i2 :: i1 in XL6 && i2 in XL6 ==> i1 in vsSSA.variableOf && i2 in vsSSA.variableOf && vsSSA.variableOf[i1] != vsSSA.variableOf[i2];
	var XLs'' := XLs' + (glob(S1') - Y);
	var S2' := ToSSA(S2, X, XL6, liveOnExitX, Y, XLs'', vsSSA);

	S' := SeqComp(S1', S2');
	assert Valid(S');
	// עד לפה התקמפל בערך 40 דקות
	*/
	S' := Skip;
	assume Valid(S');
}

method {:verify false}IfToSSA(B : BooleanExpression, S1 : Statement, S2 : Statement, X: seq<Variable>, liveOnEntryX: set<Variable>, liveOnExitX: set<Variable>, Y: set<Variable>, XLs: set<Variable>, vsSSA: VariablesSSA) returns (S': Statement)
	requires ValidVsSSA(vsSSA)
	requires Valid(IF(B, S1, S2))
	requires forall i :: i in liveOnEntryX ==> vsSSA.existsVariable2(i)
	requires forall i :: i in liveOnExitX ==> vsSSA.existsVariable2(i)
	requires forall i1, i2 :: i1 in liveOnEntryX && i2 in liveOnEntryX ==> i1 in vsSSA.variableOf && i2 in vsSSA.variableOf && vsSSA.variableOf[i1] != vsSSA.variableOf[i2]
	requires forall i1, i2 :: i1 in liveOnExitX && i2 in liveOnExitX ==> i1 in vsSSA.variableOf && i2 in vsSSA.variableOf && vsSSA.variableOf[i1] != vsSSA.variableOf[i2]
	requires forall v :: v in X ==> vsSSA.existsInstance(v)
	requires forall y :: y in Y ==> vsSSA.existsInstance(y)
	modifies vsSSA
	decreases *
	ensures Valid(S')
	ensures ValidVsSSA(vsSSA)
	ensures forall i :: i in liveOnEntryX ==> vsSSA.existsVariable2(i)
	ensures forall i :: i in liveOnExitX ==> vsSSA.existsVariable2(i)
	ensures forall v :: v in X ==> vsSSA.existsInstance(v)
	ensures forall v :: v in Y ==> vsSSA.existsInstance(v)
	ensures forall v :: v in old(vsSSA.instancesOf) ==> v in vsSSA.instancesOf && (forall i :: i in old(vsSSA.instancesOf[v]) ==> i in vsSSA.instancesOf[v])
	//ensures CorrectnessOfToSSA(IF(B,S1,S2),S',X1,X2,X3,X4,X5,XL1i,XL2i,XL3i,XL4i,XL4f,XL5f,Y,XLs)
{
	// defined in thesis:
	// toSSA.(IF ,X, (XL1i, XL2i, XL3i, XL4i), (XL3i, XL4f, XL5f), Y, XLs) is:
	// IF' where:
	// IF := " if B then S1 else S2 fi "
	// IF' := " if B' then S1'; XL4f ,XL5f := XL4t, XL5t else S2'; XL4f ,XL5f := XL4e, XL5e fi "

	var XL3i := liveOnEntryX * liveOnExitX;
	assert XL3i <= liveOnEntryX && XL3i <= liveOnExitX;
	var temp := setToSeq(XL3i);
	var X3Seq := vsSSA.instancesToVariables(temp);
	var X3 := setOf(X3Seq);
	
	var XL4fXL5f := liveOnExitX - XL3i;
	assert XL4fXL5f <= liveOnExitX;
	temp := setToSeq(XL4fXL5f);

	var X4X5 := vsSSA.instancesToVariables(temp);
	temp := setToSeq(liveOnEntryX);
	var liveOnEntryXVariables := vsSSA.instancesToVariables(temp);
	//var X4 := setOf(liveOnEntryXVariables) * setOf(X4X5);
	var X4 := (setOf(liveOnEntryXVariables) * setOf(X4X5)) * setOf(X);
	var X5Seq := setToSeq(setOf(X4X5) - X4);

	//var X2 := (setOf(liveOnEntryXVariables) - X4) * (def(S1) + def(S2));
	var X2 := ((setOf(liveOnEntryXVariables) - X4) * (def(S1) + def(S2))) * setOf(X);
	assert X2 <= setOf(X);
	var X1 := setOf(liveOnEntryXVariables) - X4 - X3 - X2;
	
	var XL1iXL2iXL4i := liveOnEntryX - XL3i;
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
	var variables := temp + temp1 + temp2 + temp2 + X5Seq + X5Seq;
	var instances := freshInit(variables, setOf(X) + Y + XLs, vsSSA);

		assert forall i :: i in instances ==> !vsSSA.existsVariable2(i);
		assert forall i,j :: 0 <= i < |instances| && i < j < |instances| ==> instances[i] != instances[j];
		vsSSA.variablesToSSAVariables(variables, instances);
		assert forall v :: v in X ==> vsSSA.existsInstance(v);
		assert forall i :: i in instances ==> vsSSA.existsVariable2(i);

	var XL4d1t := instances[0..|X4d1|];
	assert forall i :: i in XL4d1t ==> vsSSA.existsVariable2(i);
	assert X4d2 <= setOf(X);// && forall v :: v in X4d2 ==> vsSSA.existsInstance(v);
	assert forall v :: v in X4d2 ==> vsSSA.existsInstance(v);
	temp := setToSeq(X4d2);
	var XL4d2iTemp := vsSSA.getInstancesOfVaribleSeq(temp);
	assert forall i :: i in XL4d2iTemp ==> vsSSA.existsVariable2(i);
	var XL4d2iSeq := setToSeq(setOf(XL4d2iTemp) * XL4i);
	assert setOf(XL4d2iSeq) <= setOf(XL4d2iTemp) && forall i :: i in XL4d2iSeq ==> vsSSA.existsVariable2(i);
	var XL4d1d2t := instances[|X4d1|+|X4d2|..|X4d1|+|X4d2|+|X4d1d2|];
	assert forall i :: i in XL4d1d2t ==> vsSSA.existsVariable2(i);
	var XL4t := XL4d1t + XL4d2iSeq + XL4d1d2t;
	assert forall i :: i in XL4t ==> vsSSA.existsVariable2(i);

	assert X4d1 <= setOf(X) && forall v :: v in X4d1 ==> vsSSA.existsInstance(v);
	temp := setToSeq(X4d1);
	var XL4d1iTemp := vsSSA.getInstancesOfVaribleSeq(temp);
	assert forall i :: i in XL4d1iTemp ==> vsSSA.existsVariable2(i);
	var XL4d1iSeq := setToSeq(setOf(XL4d1iTemp) * XL4i);
	assert setOf(XL4d1iSeq) <= setOf(XL4d1iTemp) && forall i :: i in XL4d1iSeq ==> vsSSA.existsVariable2(i);
	var XL4d2e := instances[|X4d1|..|X4d1|+|X4d2|];
	assert forall i :: i in XL4d2e ==> vsSSA.existsVariable2(i);
	var XL4d1d2e := instances[|X4d1|+|X4d2|+|X4d1d2|..|X4d1|+|X4d2|+|X4d1d2|+|X4d1d2|];
	assert forall i :: i in XL4d1d2e ==> vsSSA.existsVariable2(i);
	var XL4e := XL4d1iSeq + XL4d2e + XL4d1d2e;
	assert forall i :: i in XL4e ==> vsSSA.existsVariable2(i);
	
	var XL5t := instances[|X4d1|+|X4d2|+|X4d1d2|+|X4d1d2|..|X4d1|+|X4d2|+|X4d1d2|+|X4d1d2|+|X5Seq|];
	assert forall i :: i in XL5t ==> vsSSA.existsVariable2(i);
	var XL5e := instances[|X4d1|+|X4d2|+|X4d1d2|+|X4d1d2|+|X5Seq|..|X4d1|+|X4d2|+|X4d1d2|+|X4d1d2|+|X5Seq|+|X5Seq|];
	assert forall i :: i in XL5e ==> vsSSA.existsVariable2(i);
	
	assert forall i :: i in XL4fXL5f ==> vsSSA.existsVariable2(i);
	var XL5f := XL4fXL5f - setOf(X4Instances);
	assert forall v :: v in X5Seq ==> vsSSA.existsInstance(v);
	assert forall i :: i in XL5f ==> vsSSA.existsVariable2(i);
	assert forall i,j :: 0 <= i < |X5Seq| && i < j < |X5Seq| ==> X5Seq[i] != X5Seq[j];
	assert forall v :: v in X5Seq ==> |XL5f * setOf(vsSSA.getInstancesOfVaribleFunc(v))| == 1;
	var XL5fSeq := OrganizeVariables3(X5Seq, XL5f, vsSSA);
	assert |XL5fSeq| == |XL5t| == |XL5e|;

	/*assert forall i :: i in XL4fXL5f ==> vsSSA.existsVariable2(i);
	var XL5f := XL4fXL5f - setOf(X4Instances);
	assert forall i :: i in XL5f ==> vsSSA.existsVariable2(i);
	temp := setToSeq(XL5f);
	assert forall i :: i in temp ==> vsSSA.existsVariable2(i);
	var XL5fSeq := OrganizeVariables(XL5t, temp, vsSSA);*/

	var XL4f := XL4fXL5f - XL5f;
	assert forall i :: i in XL4f ==> vsSSA.existsVariable2(i);

	var XL4tVariables := vsSSA.instancesToVariables(XL4t);
	assert forall v :: v in XL4tVariables ==> vsSSA.existsInstance(v);
	assert forall i :: i in XL4f ==> vsSSA.existsVariable2(i);
	assert forall i,j :: 0 <= i < |XL4tVariables| && i < j < |XL4tVariables| ==> XL4tVariables[i] != XL4tVariables[j];
	assert forall v :: v in XL4tVariables ==> |XL4f * setOf(vsSSA.getInstancesOfVaribleFunc(v))| == 1;
	var XL4fThenSeq := OrganizeVariables3(XL4tVariables, XL4f, vsSSA);
	assert |XL4fThenSeq| == |XL4t| == |XL4e|;

	/*temp := setToSeq(XL4f);
	assert forall i :: i in temp ==> vsSSA.existsVariable2(i);
	assert forall i :: i in XL4t ==> vsSSA.existsVariable2(i);
	var XL4fSeqThen := OrganizeVariables(XL4t, temp, vsSSA);*/

	var XL4eVariables := vsSSA.instancesToVariables(XL4e);
	assert forall v :: v in XL4eVariables ==> vsSSA.existsInstance(v);
	assert forall i :: i in XL4f ==> vsSSA.existsVariable2(i);
	assert forall i,j :: 0 <= i < |XL4eVariables| && i < j < |XL4eVariables| ==> XL4eVariables[i] != XL4eVariables[j];
	assert forall v :: v in XL4eVariables ==> |XL4f * setOf(vsSSA.getInstancesOfVaribleFunc(v))| == 1;
	var XL4fElseSeq := OrganizeVariables3(XL4eVariables, XL4f, vsSSA);
	assert |XL4fElseSeq| == |XL4t| == |XL4e|;

	/*temp := setToSeq(XL4f);
	assert forall i :: i in temp ==> vsSSA.existsVariable2(i);
	assert forall i :: i in XL4e ==> vsSSA.existsVariable2(i);
	var XL4fSeqElse := OrganizeVariables(XL4e, temp, vsSSA);*/

	var XLs' := XLs + setOf(instances);
	temp := setToSeq(XL3i);
	assert forall i :: i in temp ==> vsSSA.existsVariable2(i);
	assert forall i :: i in XL4t ==> vsSSA.existsVariable2(i);
	assert forall i :: i in XL5t ==> vsSSA.existsVariable2(i);
	var liveOnExitX' := setOf(temp) + setOf(XL4t) + setOf(XL5t);
	assert forall i :: i in liveOnExitX' ==> vsSSA.existsVariable2(i);
	var S1' := ToSSA(S1, X, liveOnEntryX, liveOnExitX', Y, XLs', vsSSA); 

	var globS1' := def(S1') + input(S1');
	var XLs'' := XLs' + (globS1' - Y);
	temp := setToSeq(XL3i);
	assert forall i :: i in temp ==> vsSSA.existsVariable2(i);
	assert forall i :: i in XL4e ==> vsSSA.existsVariable2(i);
	assert forall i :: i in XL5e ==> vsSSA.existsVariable2(i);
	liveOnExitX' := setOf(temp) + setOf(XL4e) + setOf(XL5e);
	assert forall i :: i in liveOnExitX' ==> vsSSA.existsVariable2(i);
	var S2' := ToSSA(S2, X, liveOnEntryX, liveOnExitX', Y, XLs'', vsSSA);

	var tempAssignment1 := Assignment(XL4fThenSeq + XL5fSeq, seqVarToSeqExpr(XL4t + XL5t));
	var tempAssignment2 := Assignment(XL4fElseSeq + XL5fSeq, seqVarToSeqExpr(XL4e + XL5e));
	assert Valid(tempAssignment1);
	assert Valid(tempAssignment2);
	var tempSeqComp1 := SeqComp(S1', tempAssignment1);
	var tempSeqComp2 := SeqComp(S2', tempAssignment2);
	assert Valid(tempSeqComp1);
	assert Valid(tempSeqComp2);
	S' := IF(B', tempSeqComp1, tempSeqComp2);
	//S' := IF(B', SeqComp(S1', Assignment(XL4fSeqThen + XL5fSeq, XL4t + XL5t)), SeqComp(S2', Assignment(XL4fSeqElse + XL5fSeq, XL4e + XL5e)));
	assert Valid(S');
/*
	assert CorrectnessOfToSSA(IF(B,S1,S2),S',X1,X2,X3,X4,X5,XL1i,XL2i,XL3i,XL4i,XL4f,XL5f,Y,XLs) by
	{
		assume CorrectnessOfToSSA(IF(B,S1,S2),S',X1,X2,X3,X4,X5,XL1i,XL2i,XL3i,XL4i,XL4f,XL5f,Y,XLs,vsSSA);
/*		
		var S1' := tempSeqComp1;
		assert CorrectnessOfToSSA(IF(B,S1,S2),S',X,XL1i+XL2i+XL3i+XL4i,XL3i+XL4f+XL5f,Y,XLs,vsSSA) by
		{
			var X5 := ???;
			LemmaIfToSSAIsCorrect(B,S1,S2,X,XL1i,XL2i,XL3i,XL4i,XL4f,XL5f,Y,XLs,X1,X2,X3,X4,X5,S1',
				XL4t,XL5t,XL4e,XL5e,X4d1,X4d2,X4d1d2,XL4d1t,XL4d1e,XL4d1d2t,XL4d1d2e,XL4d2i,XL4d1i,XL4d2e,XLs',XLs'',S2',vsSSA);
		}*/
		assert liveOnEntryX == XL1i+XL2i+XL3i+XL4i;
		assert liveOnExitX == XL3i+XL4f+XL5f;
	}*/
}

method {:verify false}DoToSSA(B : BooleanExpression, S : Statement, X: seq<Variable>, liveOnEntryX: set<Variable>, liveOnExitX: set<Variable>, Y: set<Variable>, XLs: set<Variable>, vsSSA: VariablesSSA) returns (S'': Statement)
	requires Valid(DO(B, S))
	requires ValidVsSSA(vsSSA)
	requires forall i :: i in liveOnEntryX ==> vsSSA.existsVariable2(i)
	requires forall i :: i in liveOnExitX ==> vsSSA.existsVariable2(i)
	requires forall i1, i2 :: i1 in liveOnEntryX && i2 in liveOnEntryX ==> i1 in vsSSA.variableOf && i2 in vsSSA.variableOf && vsSSA.variableOf[i1] != vsSSA.variableOf[i2]
	requires forall i1, i2 :: i1 in liveOnExitX && i2 in liveOnExitX ==> i1 in vsSSA.variableOf && i2 in vsSSA.variableOf && vsSSA.variableOf[i1] != vsSSA.variableOf[i2]
	requires forall v :: v in X ==> vsSSA.existsInstance(v)
	requires forall v :: v in Y ==> vsSSA.existsInstance(v)
	modifies vsSSA
	decreases *	
	ensures Valid(S'')
	ensures ValidVsSSA(vsSSA)
	ensures forall i :: i in liveOnEntryX ==> vsSSA.existsVariable2(i)
	ensures forall i :: i in liveOnExitX ==> vsSSA.existsVariable2(i)
	ensures forall v :: v in X ==> vsSSA.existsInstance(v)
	ensures forall v :: v in Y ==> vsSSA.existsInstance(v)
	ensures forall v :: v in old(vsSSA.instancesOf) ==> v in vsSSA.instancesOf && (forall i :: i in old(vsSSA.instancesOf[v]) ==> i in vsSSA.instancesOf[v])
{
	// defined in thesis:
	// toSSA.(DO, X, (XL1i, XL2i, XL3i, XL4i), (XL3i, XL4f), Y ,XLs) is:
	// "XL2, XL4f := XL2i, XL4i; DO'" where:
	// DO := " while B do S1 od ",
	// DO' := " while B' do S1'; XL2, XL4f := XL2b, XL4b od "

	var XL4f := liveOnExitX - (liveOnEntryX * liveOnExitX);
	assert XL4f <= liveOnExitX;
	var XL4fSeq := setToSeq(XL4f);
	var X4Seq := vsSSA.instancesToVariables(XL4fSeq);
	assert forall i,j :: 0 <= i < |X4Seq| && i < j < |X4Seq| ==> X4Seq[i] != X4Seq[j] by {
		vsSSA.DistinctVariablesLemma(XL4fSeq, X4Seq);
		assert (forall index1,index2 :: 0 <= index1 < index2 < |XL4fSeq| ==> XL4fSeq[index1] != XL4fSeq[index2] && vsSSA.variableOf[XL4fSeq[index1]] != vsSSA.variableOf[XL4fSeq[index2]]);
	}
	assert forall v :: v in X4Seq ==> vsSSA.existsInstance(v);
	var X4 := setOf(X4Seq) * setOf(X);
	assert X4 <= setOf(X);
	assert X4 <= setOf(X4Seq);
	
	var temp := setToSeq(liveOnEntryX);
	var liveOnEntryXVariables := vsSSA.instancesToVariables(temp);
	var X2 := ((setOf(liveOnEntryXVariables) - X4) * def(S)) * setOf(X);
	assert X2 <= setOf(X);
	var X2Seq := setToSeq(X2);
	assert setOf(X2Seq) == X2;
	assert forall i,j :: 0 <= i < |X2Seq| && i < j < |X2Seq| ==> X2Seq[i] != X2Seq[j];
	
	var XL3i := liveOnEntryX * liveOnExitX;
	assert XL3i <= liveOnEntryX && XL3i <= liveOnExitX;
	var XL3iSeq := setToSeq(XL3i);
	assert setOf(XL3iSeq) == XL3i && XL3i <= liveOnExitX ==> setOf(XL3iSeq) <= liveOnExitX;
	var X3Seq := vsSSA.instancesToVariables(XL3iSeq);
	var X3 := setOf(X3Seq);
	
	var X1 := setOf(liveOnEntryXVariables) - X4 - X3 - X2;

	var variables := X2Seq + X2Seq + X4Seq;
	var instances := freshInit(variables, setOf(X) + Y + XLs, vsSSA);
	assert forall i :: i in liveOnEntryX ==> vsSSA.existsVariable2(i);
	assert forall i :: i in liveOnExitX ==> vsSSA.existsVariable2(i);
		assert forall i :: i in instances ==> !vsSSA.existsVariable2(i);
		assert forall i,j :: 0 <= i < |instances| && i < j < |instances| ==> instances[i] != instances[j];
		vsSSA.variablesToSSAVariables(variables, instances);
		assert forall v :: v in X ==> vsSSA.existsInstance(v);
	
	var XL2Seq := instances[0..|X2|];
	assert forall i :: i in instances ==> vsSSA.existsVariable2(i) && XL2Seq <= instances ==> forall i :: i in XL2Seq ==> vsSSA.existsVariable2(i);
	var XL2bSeq := instances[|X2|..|X2|+|X2|];
	assert |XL2Seq| == |XL2bSeq|;
	assert forall i :: i in instances ==> vsSSA.existsVariable2(i) && XL2bSeq <= instances ==> forall i :: i in XL2bSeq ==> vsSSA.existsVariable2(i);
	var XL4bSeq := instances[|X2|+|X2|..];
	assert |XL4bSeq| == |XL4fSeq|;
	assert forall i :: i in instances ==> vsSSA.existsVariable2(i) && XL4bSeq <= instances ==> forall i :: i in XL4bSeq ==> vsSSA.existsVariable2(i);
	
	var XL1iXL2iXL4i := liveOnEntryX - (liveOnEntryX * liveOnExitX);
	assert XL1iXL2iXL4i <= liveOnEntryX;
	assert forall i :: i in XL1iXL2iXL4i ==> vsSSA.existsVariable2(i);
	assert X4 <= setOf(X);
	 temp := setToSeq(X4);
	var X4Instances := vsSSA.getInstancesOfVaribleSeq(temp);
	assert forall i :: i in X4Instances ==> vsSSA.existsVariable2(i);
	var XL1iXL2i := XL1iXL2iXL4i - setOf(X4Instances);
	assert XL1iXL2i <= XL1iXL2iXL4i;
	assert forall i :: i in XL1iXL2i ==> vsSSA.existsVariable2(i);
	var XL4i := (XL1iXL2iXL4i - XL1iXL2i) * setOf(X4Instances);

	assert X4 <= setOf(X4Seq); // Actually, X4 is exactly X4Seq - only a set.
	assert forall v :: v in X4Seq ==> |XL4i * setOf(vsSSA.getInstancesOfVaribleFunc(v))| == 1;
	assert forall v :: v in X4Seq ==> vsSSA.existsInstance(v);
	assert forall i :: i in XL4i ==> vsSSA.existsVariable2(i);

	var XL4iSeq := OrganizeVariables3(X4Seq, XL4i, vsSSA); // עובר קימפול!!!!!!!
	assert |XL4iSeq| == |XL4fSeq|;

	assert forall v :: v in X ==> vsSSA.existsInstance(v);
	assert X2 <= setOf(X) && setOf(X2Seq) == X2 ==> setOf(X2Seq) <= setOf(X);
	var X2Instances := vsSSA.getInstancesOfVaribleSeq(X2Seq);
	var XL1i := XL1iXL2i - setOf(X2Instances);
	assert XL1i <= XL1iXL2i;
	var XL2i := XL1iXL2i - XL1i;
	assert XL2i <= XL1iXL2i;
	
	assert forall v :: v in X2Seq ==> |XL2i * setOf(vsSSA.getInstancesOfVaribleFunc(v))| == 1;
	assert forall v :: v in X2Seq ==> vsSSA.existsInstance(v);
	assert forall i :: i in XL2i ==> vsSSA.existsVariable2(i);

	var XL2iSeq := OrganizeVariables3(X2Seq, XL2i, vsSSA);
	assert |XL2iSeq| == |XL2Seq|;

	////////////////////////////////////////
	
	var XLs' := XLs + setOf(instances);
	var B' := SubstitueBooleanExpression(B, [X1,X2,X3,X4], [XL1i,setOf(XL2Seq),XL3i,XL4f]);
	temp := setToSeq(XL1i); 
	assert XL4f <= liveOnExitX && setOf(XL4fSeq) == XL4f ==> setOf(XL4fSeq) <= liveOnExitX;
	assert forall i :: i in liveOnExitX ==> vsSSA.existsVariable2(i);
	 
	assert forall i :: i in temp ==> vsSSA.existsVariable2(i);
	assert forall i :: i in XL2Seq ==> vsSSA.existsVariable2(i);
	assert forall i :: i in XL3iSeq ==> vsSSA.existsVariable2(i);
	assert forall i :: i in XL4fSeq ==> vsSSA.existsVariable2(i);
	var liveOnEntryX' := temp + XL2Seq + XL3iSeq + XL4fSeq;

	assert forall i :: i in XL2bSeq ==> vsSSA.existsVariable2(i);
	assert forall i :: i in XL4bSeq ==> vsSSA.existsVariable2(i);
	var liveOnExitX' := temp + XL2bSeq + XL3iSeq + XL4bSeq;

	assert forall i :: i in liveOnEntryX' ==> vsSSA.existsVariable2(i);
	assert forall i :: i in liveOnExitX' ==> vsSSA.existsVariable2(i);
	var S' := ToSSA(S, X, setOf(liveOnEntryX'), setOf(liveOnExitX'), Y, XLs', vsSSA);

	//var tempDO := DO(B', S');
	var tempAssignment := Assignment(XL2Seq + XL4fSeq, seqVarToSeqExpr(XL2bSeq + XL4bSeq));
	var DO' := DO(B', SeqComp(S', tempAssignment));
	
	assert Valid(DO');
	assert Valid(tempAssignment);
	//var DO' := SeqComp(tempDO, tempAssignment);
	//var DO' := SeqComp(DO(B', S'), Assignment(XL2Seq + XL4fSeq, XL2bSeq + XL4bSeq));
	tempAssignment := Assignment(XL2Seq + XL4fSeq, seqVarToSeqExpr(XL2iSeq + XL4iSeq));
	assert Valid(tempAssignment);
	S'' := SeqComp(tempAssignment, DO');
	//S'' := SeqComp(Assignment(XL2Seq + XL4fSeq, XL2iSeq + XL4iSeq), DO');
	assert Valid(S'');
}

method {:verify false}FromSSA(SV': Statement, X: seq<Variable>, XL1i: seq<Variable>, XL2f: seq<Variable>, Y: set<Variable>, XLs: set<Variable>, vsSSA: VariablesSSA, ghost V: set<Variable>, ghost S': Statement, ghost V': set<Variable>, ghost varSlideDG: VarSlideDG) returns (res: Statement)
	//requires var varSlidesSV: set<VarSlide> := varSlidesOf(SV', V'); forall Sm :: Sm in varSlidesSV <==> (Sm.0 in V' || (exists Sn: VarSlide :: Sn.0 in V' && VarSlideDGReachable(Sm, Sn, varSlideDG'.1)))	 // Implement VarSlideDGReachable
	///////////////requires Substatement(SV', S') 
		
	requires ValidVsSSA(vsSSA)
	requires Valid(SV')
	requires SV'.Assignment? ==> forall i :: i in SV'.LHS ==> vsSSA.existsVariable2(i)
	requires forall i :: i in XL1i ==> vsSSA.existsVariable2(i)
	requires forall i :: i in XL2f ==> vsSSA.existsVariable2(i)
	requires forall i :: i in XLs ==> vsSSA.existsVariable2(i)
	decreases *
	ensures ValidVsSSA(vsSSA)
	ensures Valid(res)

	ensures MergedVars1(SV', res, XLsToSeq(X, XLs, vsSSA), X)
	/////////////////ensures forall l :: l in allLabelsOf(S) ==> LabelOf2(VarLabelOf(S,S', l))==l
	//ensures var varSlidesRes: set<VarSlide> := varSlidesOf(res, V); forall Sm :: Sm in varSlidesRes <==> (Sm.0 in V || (exists Sn: VarSlide :: Sn.0 in V && VarSlideDGReachable(Sm, Sn, varSlideDG.1)))	 // Implement VarSlideDGReachable
	//ensures Substatement(res, S) 
{
	var XLsSeq := XLsToSeq(X, XLs, vsSSA);
	res := MergeVars1(SV', XLsSeq, X, XL1i, XL2f, Y, vsSSA);
	/*assert Substatement(res, S) by {
		L20(S, S', SV', res, /*XLsToSSA*/, [], []);
	}*/
}

function method {:verify false}XLsToSeq(X: seq<Variable>, XLs: set<Variable>, vsSSA: VariablesSSA): seq<set<Variable>>
{
	if X == [] then [] else 
	
		var instancesSeq := vsSSA.getInstancesOfVaribleFunc(X[0]);
		var instances := setOf(instancesSeq) * XLs;

		[instances] + XLsToSeq(X[1..], XLs, vsSSA)
}

function method {:verify false}SeqOfSetToSet(seqOfSet: seq<set<Variable>>): set<Variable>
/*{
	if seqOfSet == [] then {} else 
	{
		seqOfSet[0] + SeqOfSetToSet(seqOfSet[1..])
	}
}*/

method {:verify false}MergeVars1(S': Statement, XLs: seq<set<Variable>>, X: seq<Variable>, XL1i: seq<Variable>, XL2f: seq<Variable>, Y: set<Variable>, vsSSA: VariablesSSA) returns( S: Statement)
	requires ValidVsSSA(vsSSA)
	requires Valid(S')
	requires S'.Assignment? ==> forall i :: i in S'.LHS ==> vsSSA.existsVariable2(i)
	requires forall i :: i in XL1i ==> vsSSA.existsVariable2(i)
	requires forall i :: i in XL2f ==> vsSSA.existsVariable2(i)
	requires forall i,j :: j in XLs && i in j ==> vsSSA.existsVariable2(i)
	//requires forall i :: i in XLs ==> vsSSA.existsVariable2(i)
	decreases *
	ensures ValidVsSSA(vsSSA)
	ensures Valid(S)

	ensures MergedVars1(S', S, XLs, X)
{
	S := MergeVars(S', XLs, X, XL1i, XL2f, Y, vsSSA);
	
	assert RemoveEmptyAssignments(S) == RemoveEmptyAssignments(Rename(S', XLs, X)) by {
		assert S == Rename(S', XLs, X) by {
			assert MergedVars(S', S, XLs, X);
		}
	}

	S := RemoveEmptyAssignments(S);
	assert S == RemoveEmptyAssignments(Rename(S', XLs, X));
}

function method {:verify false} RemoveEmptyAssignments(S: Statement): Statement
	requires Core(S) && Valid(S)
{
	match S {
		case Assignment(LHS,RHS) => 
			if |LHS| == 0 then Skip else S
		case SeqComp(S1,S2) =>
			if IsEmptyAssignmentFunc(S1) then
				RemoveEmptyAssignments(S2)
			else if IsEmptyAssignmentFunc(S2) then
				RemoveEmptyAssignments(S1) 
			else
				SeqComp(RemoveEmptyAssignments(S1), RemoveEmptyAssignments(S2))
		case IF(B0,Sthen,Selse) => 
			IF(B0, RemoveEmptyAssignments(Sthen), RemoveEmptyAssignments(Selse))
		case DO(B,S1) => 
			DO(B, RemoveEmptyAssignments(S1))
		case Skip => Skip
	}
}

lemma L80(S: Statement /*Original SV'*/, XLs: seq<set<Variable>>, X: seq<Variable>)
	requires forall l :: l in allLabelsOf(S) ==> ValidLabel(l, S)
	ensures var selfEmptyLabelsSV' := selfEmptyLabelsOf(Rename(S, XLs, X), allLabelsOf(S)); forall l :: l in allLabelsOf(S) - selfEmptyLabelsSV' ==>
		RemoveEmptyAssignments(Rename(slipOf(S, l), XLs, X)) == slipOf(RemoveEmptyAssignments(Rename(S, XLs, X)), LabelOf(selfEmptyLabelsSV', l))
{
	var selfEmptyLabelsSV' := selfEmptyLabelsOf(Rename(S, XLs, X), allLabelsOf(S));
	forall l | l in allLabelsOf(S) - selfEmptyLabelsSV' ensures RemoveEmptyAssignments(Rename(slipOf(S, l), XLs, X)) == slipOf(RemoveEmptyAssignments(Rename(S, XLs, X)), LabelOf(selfEmptyLabelsSV', l)) {
		L81(S, XLs, X, l, LabelOf(selfEmptyLabelsSV', l));
	}
}

lemma L81(S: Statement /*Original SV'*/, XLs: seq<set<Variable>>, X: seq<Variable>, varLabel: Label, l: Label)
	requires var selfEmptyLabelsSV' := selfEmptyLabelsOf(Rename(S, XLs, X), allLabelsOf(S)); varLabel in allLabelsOf(S) - selfEmptyLabelsSV'
	requires var selfEmptyLabelsSV' := selfEmptyLabelsOf(Rename(S, XLs, X), allLabelsOf(S)); l == LabelOf(selfEmptyLabelsSV', varLabel)
	ensures RemoveEmptyAssignments(Rename(slipOf(S, varLabel), XLs, X)) == slipOf(RemoveEmptyAssignments(Rename(S, XLs, X)), l)
{
	if l == [] {
		assert RemoveEmptyAssignments(Rename(slipOf(S, varLabel), XLs, X)) == slipOf(RemoveEmptyAssignments(Rename(S, XLs, X)), []) by {
			assert varLabel == (if IsDO(slipOf(RemoveEmptyAssignments(Rename(S, XLs, X)), [])) then [2] else []);
			if varLabel == [] {
				calc {
					RemoveEmptyAssignments(Rename(slipOf(S, varLabel), XLs, X));
				==
					RemoveEmptyAssignments(Rename(slipOf(S, []), XLs, X));
				==
					RemoveEmptyAssignments(Rename(S, XLs, X));
				==
					slipOf(RemoveEmptyAssignments(Rename(S, XLs, X)), []);
				}
			} else {
				assert varLabel == [2];
				assert IsSeqComp(S);
				assert IsDO(slipOf(S, [2]));
				match S {
				case SeqComp(S1, S2) =>
					assert RemoveEmptyAssignments(Rename(slipOf(S, [2]), XLs, X)) == slipOf(RemoveEmptyAssignments(Rename(S, XLs, X)), []) by {
						calc {
							slipOf(RemoveEmptyAssignments(Rename(S, XLs, X)), []);
						==
							RemoveEmptyAssignments(Rename(S, XLs, X));
						== { assert S == SeqComp(S1, S2); }
							RemoveEmptyAssignments(Rename(SeqComp(S1, S2), XLs, X));
						== { L82(S1, S2, XLs, X); }
							RemoveEmptyAssignments(SeqComp(Rename(S1, XLs, X), Rename(S2, XLs, X)));
						==
							RemoveEmptyAssignments(SeqComp(Assignment([], []), Rename(S2, XLs, X)));
						== { assert !IsEmptyAssignment(Rename(S2, XLs, X)); }
							RemoveEmptyAssignments(Rename(S2, XLs, X));
						==
							RemoveEmptyAssignments(Rename(slipOf(SeqComp(S1, S2), [2]), XLs, X));
						== { assert S == SeqComp(S1, S2); }
							RemoveEmptyAssignments(Rename(slipOf(S, [2]), XLs, X));
						}
					}
				}
			}
		}
	}
	else {
		assert l != [] ==> varLabel != [];
		match S {
		case Assignment(LHS,RHS) => assert false;
		case SeqComp(S1,S2) =>		if IsDO(S2) {
										assert RemoveEmptyAssignments(Rename(slipOf(S, varLabel), XLs, X)) == slipOf(RemoveEmptyAssignments(Rename(S, XLs, X)), l) by {
											calc {
												RemoveEmptyAssignments(Rename(slipOf(S, varLabel), XLs, X));
											== { assert S == SeqComp(S1, S2); }
												RemoveEmptyAssignments(Rename(slipOf(SeqComp(S1, S2), varLabel), XLs, X));
											== { assert varLabel == [2] + varLabel[1..]; } // first part of [2,1,1]
												RemoveEmptyAssignments(Rename(slipOf(SeqComp(S1, S2), [2] + varLabel[1..]), XLs, X));
											==
												RemoveEmptyAssignments(Rename(slipOf(S2, varLabel[1..]), XLs, X));
											== { assert IsDO(S2); }
												RemoveEmptyAssignments(Rename(slipOf(DO(GetLoopBool(S2), GetLoopBody(S2)), varLabel[1..]), XLs, X));
											== { assert varLabel[1..] == [1] + varLabel[2..]; } // second part of [2,1,1]
												RemoveEmptyAssignments(Rename(slipOf(DO(GetLoopBool(S2), GetLoopBody(S2)), [1] + varLabel[2..]), XLs, X));
											==
												RemoveEmptyAssignments(Rename(slipOf(GetLoopBody(S2), varLabel[2..]), XLs, X));
											== { assert IsSeqComp(GetLoopBody(S2)); }
												RemoveEmptyAssignments(Rename(slipOf(SeqComp(GetS1(GetLoopBody(S2)), GetS2(GetLoopBody(S2))), varLabel[2..]), XLs, X));
											== 	{ assert varLabel[2..] == [1] + varLabel[3..]; } // third part of [2,1,1]
												RemoveEmptyAssignments(Rename(slipOf(SeqComp(GetS1(GetLoopBody(S2)), GetS2(GetLoopBody(S2))), [1] + varLabel[3..]), XLs, X));
											==
												RemoveEmptyAssignments(Rename(slipOf(GetS1(GetLoopBody(S2)), varLabel[3..]), XLs, X));
											== { L81(GetS1(GetLoopBody(S2)) , XLs, X, varLabel[3..], l[1..]); 
												 assert RemoveEmptyAssignments(Rename(slipOf(GetS1(GetLoopBody(S2)), varLabel[3..]), XLs, X)) == slipOf(RemoveEmptyAssignments(Rename(GetS1(GetLoopBody(S2)), XLs, X)), l[1..]); }
												slipOf(RemoveEmptyAssignments(Rename(GetS1(GetLoopBody(S2)), XLs, X)), l[1..]);
											==
												slipOf(RemoveEmptyAssignments(SeqComp(Rename(GetS1(GetLoopBody(S2)), XLs, X), Assignment([], []))), l[1..]);
											==
												slipOf(RemoveEmptyAssignments(SeqComp(Rename(GetS1(GetLoopBody(S2)), XLs, X), Rename(GetS2(GetLoopBody(S2)), XLs, X))), l[1..]);
											==	{ L82(GetS1(GetLoopBody(S2)), GetS2(GetLoopBody(S2)), XLs, X); }
												slipOf(RemoveEmptyAssignments(Rename(SeqComp(GetS1(GetLoopBody(S2)), GetS2(GetLoopBody(S2))), XLs, X)), l[1..]);
											== { assert IsSeqComp(GetLoopBody(S2)); }
												slipOf(RemoveEmptyAssignments(Rename(GetLoopBody(S2), XLs, X)), l[1..]);
											==
												slipOf(RemoveEmptyAssignments(Rename(DO(GetLoopBool(S2), GetLoopBody(S2)), XLs, X)), [1] + l[1..]);
											== { assert l == [1] + l[1..]; }
												slipOf(RemoveEmptyAssignments(Rename(DO(GetLoopBool(S2), GetLoopBody(S2)), XLs, X)), l);
											== { assert IsDO(S2); }
												slipOf(RemoveEmptyAssignments(Rename(S2, XLs, X)), l);
											==
												slipOf(RemoveEmptyAssignments(SeqComp(Assignment([], []), Rename(S2, XLs, X)), l);
											==
												slipOf(RemoveEmptyAssignments(SeqComp(Rename(S1, XLs, X), Rename(S2, XLs, X)), l);
											== { L82(S1, S2, XLs, X); }
												slipOf(RemoveEmptyAssignments(Rename(SeqComp(S1, S2), XLs, X)), l);
											== { assert S == SeqComp(S1, S2); }
												slipOf(RemoveEmptyAssignments(Rename(S, XLs, X)), l);
											}
										}
									}
									else {
										if varLabel[0] == 1 {
											assert RemoveEmptyAssignments(Rename(slipOf(S, varLabel), XLs, X)) == slipOf(RemoveEmptyAssignments(Rename(S, XLs, X)), l) by {
												calc {
													RemoveEmptyAssignments(Rename(slipOf(S, varLabel), XLs, X));
												== { assert S == SeqComp(S1, S2); }
													RemoveEmptyAssignments(Rename(slipOf(SeqComp(S1, S2), varLabel), XLs, X));
												== { assert varLabel == [1] + varLabel[1..]; }
													RemoveEmptyAssignments(Rename(slipOf(SeqComp(S1, S2), [1] + varLabel[1..]), XLs, X));
												==
													RemoveEmptyAssignments(Rename(slipOf(S1, varLabel[1..]), XLs, X));
												== { L81(S1, XLs, X, varLabel[1..], l[1..]);
													 assert RemoveEmptyAssignments(Rename(slipOf(S1, varLabel[1..]), XLs, X)) == slipOf(RemoveEmptyAssignments(Rename(S1, XLs, X)), l[1..]); }
													slipOf(RemoveEmptyAssignments(Rename(S1, XLs, X)), l[1..]);
												==
													slipOf(RemoveEmptyAssignments(Rename(SeqComp(S1, S2), XLs, X)), [1] + l[1..]);
												== { assert l == [1] + l[1..]; }
													slipOf(RemoveEmptyAssignments(Rename(SeqComp(S1, S2), XLs, X)), l);
												==
													slipOf(RemoveEmptyAssignments(Rename(S, XLs, X)), l);
												}
											}
										} else {
											assert RemoveEmptyAssignments(Rename(slipOf(S, varLabel), XLs, X)) == slipOf(RemoveEmptyAssignments(Rename(S, XLs, X)), l) by {
												calc {
													RemoveEmptyAssignments(Rename(slipOf(S, varLabel), XLs, X));
												== { assert S == SeqComp(S1, S2); }
													RemoveEmptyAssignments(Rename(slipOf(SeqComp(S1, S2), varLabel), XLs, X));
												==	{ assert varLabel == [2] + varLabel[1..]; }
													RemoveEmptyAssignments(Rename(slipOf(SeqComp(S1, S2), [2] + varLabel[1..]), XLs, X));
												==
													RemoveEmptyAssignments(Rename(slipOf(S2, varLabel[1..]), XLs, X));
												== { L81(S2, XLs, X, varLabel[1..], l[1..]);
													 assert RemoveEmptyAssignments(Rename(slipOf(S2, varLabel[1..]), XLs, X)) == slipOf(RemoveEmptyAssignments(Rename(S2, XLs, X)), l[1..]); }
													slipOf(RemoveEmptyAssignments(Rename(S2, XLs, X)), l[1..]);
												==
													slipOf(RemoveEmptyAssignments(Rename(SeqComp(S1, S2), XLs, X)), [2] + l[1..]);
												== { assert l == [2] + l[1..]; }
													slipOf(RemoveEmptyAssignments(Rename(SeqComp(S1, S2), XLs, X)), l);
												==
													slipOf(RemoveEmptyAssignments(Rename(S, XLs, X)), l);
												}
											}
										}
									}
		case IF(B0,Sthen,Selse) =>	if varLabel[0] == 1 {
										assert IsSeqComp(Sthen);
										assert RemoveEmptyAssignments(Rename(slipOf(S, varLabel), XLs, X)) == slipOf(RemoveEmptyAssignments(Rename(S, XLs, X)), l) by {
											calc {
												RemoveEmptyAssignments(Rename(slipOf(S, varLabel), XLs, X));
											== { assert S == IF(B0,Sthen,Selse); }
												RemoveEmptyAssignments(Rename(slipOf(IF(B0,Sthen,Selse), varLabel), XLs, X));
											==	{ assert varLabel == [1,1] + varLabel[2..]; }
												RemoveEmptyAssignments(Rename(slipOf(IF(B0,Sthen,Selse), [1,1] + varLabel[2..]), XLs, X));
											==
												RemoveEmptyAssignments(Rename(slipOf(Sthen, [1] + varLabel[2..]), XLs, X)); // in else - it's [1] + varLabel[2..]
											==
												RemoveEmptyAssignments(Rename(slipOf(GetS1(Sthen), varLabel[2..]), XLs, X));
											== { L81(GetS1(Sthen), XLs, X, varLabel[2..], l[1..]);
												 assert RemoveEmptyAssignments(Rename(slipOf(GetS1(Sthen), varLabel[2..]), XLs, X)) == slipOf(RemoveEmptyAssignments(Rename(GetS1(Sthen), XLs, X)), l[1..]); }
												slipOf(RemoveEmptyAssignments(Rename(GetS1(Sthen), XLs, X)), l[1..]);
											==
												slipOf(RemoveEmptyAssignments(SeqComp(Rename(GetS1(Sthen), XLs, X), Assignment([],[]))), l[1..]);
											== { assert IsEmptyAssignment(GetS2(Sthen)); }
												slipOf(RemoveEmptyAssignments(SeqComp(Rename(GetS1(Sthen), XLs, X), Rename(GetS2(Sthen), XLs, X))), l[1..]);
											== { L82(GetS1(Sthen), GetS2(Sthen), XLs, X); }
												slipOf(RemoveEmptyAssignments(Rename(SeqComp(GetS1(Sthen), GetS2(Sthen)), XLs, X)), l[1..]);
											== { assert IsSeqComp(Sthen); }
												slipOf(RemoveEmptyAssignments(Rename(Sthen, XLs, X)), l[1..]);
											==
												slipOf(RemoveEmptyAssignments(Rename(IF(B0,Sthen,Selse), XLs, X)), [1] + l[1..]);
											== { assert l == [1] + l[1..]; }
												slipOf(RemoveEmptyAssignments(Rename(IF(B0,Sthen,Selse), XLs, X)), l);
											== { assert S == IF(B0,Sthen,Selse); }
												slipOf(RemoveEmptyAssignments(Rename(S, XLs, X)), l);
											}
										}
									}
									else {
										assert IsSeqComp(Selse);
										assert RemoveEmptyAssignments(Rename(slipOf(S, varLabel), XLs, X)) == slipOf(RemoveEmptyAssignments(Rename(S, XLs, X)), l) by {
											calc {
												RemoveEmptyAssignments(Rename(slipOf(S, varLabel), XLs, X));
											== { assert S == IF(B0,Sthen,Selse); }
												RemoveEmptyAssignments(Rename(slipOf(IF(B0,Sthen,Selse), varLabel), XLs, X));
											==	{ assert varLabel == [2,1] + varLabel[2..]; }
												RemoveEmptyAssignments(Rename(slipOf(IF(B0,Sthen,Selse), [2,1] + varLabel[2..]), XLs, X));
											==
												RemoveEmptyAssignments(Rename(slipOf(Selse, [1] + varLabel[2..]), XLs, X));
											==
												RemoveEmptyAssignments(Rename(slipOf(GetS1(Selse), varLabel[2..]), XLs, X));
											== { L81(GetS1(Selse), XLs, X, varLabel[2..], l[1..]);
												 assert RemoveEmptyAssignments(Rename(slipOf(GetS1(Selse), varLabel[2..]), XLs, X)) == slipOf(RemoveEmptyAssignments(Rename(GetS1(Selse), XLs, X)), l[1..]); }
												slipOf(RemoveEmptyAssignments(Rename(GetS1(Selse), XLs, X)), l[1..]);
											==
												slipOf(RemoveEmptyAssignments(SeqComp(Rename(GetS1(Selse), XLs, X), Assignment([],[]))), l[1..]);
											== { assert IsEmptyAssignment(GetS2(Selse)); }
												slipOf(RemoveEmptyAssignments(SeqComp(Rename(GetS1(Selse), XLs, X), Rename(GetS2(Selse), XLs, X))), l[1..]);
											== { L82(GetS1(Selse), GetS2(Selse), XLs, X); }
												slipOf(RemoveEmptyAssignments(Rename(SeqComp(GetS1(Selse), GetS2(Selse)), XLs, X)), l[1..]);
											== { assert IsSeqComp(Selse); }
												slipOf(RemoveEmptyAssignments(Rename(Selse, XLs, X)), l[1..]);
											==
												slipOf(RemoveEmptyAssignments(Rename(IF(B0,Sthen,Selse), XLs, X)), [2] + l[1..]);
											== { assert l == [2] + l[1..]; }
												slipOf(RemoveEmptyAssignments(Rename(IF(B0,Sthen,Selse), XLs, X)), l);
											== { assert S == IF(B0,Sthen,Selse); }
												slipOf(RemoveEmptyAssignments(Rename(S, XLs, X)), l);
											}
										}
									}
		case DO(B,S1) =>			assert false;
		case Skip =>				assert false;
		}
	}
}

lemma L82(S1: Statement, S2: Statement, XLs: seq<set<Variable>>, X: seq<Variable>)
	ensures Rename(SeqComp(S1, S2), XLs, X) == SeqComp(Rename(S1, XLs, X), Rename(S2, XLs, X))

function method {:verify false}IsEmptyAssignmentFunc(S: Statement): bool // changed from predicate to function method, because called in RemoveEmptyAssignments
	requires Core(S) && Valid(S)
{
	match S {
		case Assignment(LHS,RHS) => |LHS| == 0
		case SeqComp(S1,S2) => false
		case IF(B0,Sthen,Selse) => false
		case DO(B,S1) => false
		case Skip => false
	}	
}

method {:verify false}MergeVars(S': Statement, XLs: seq<set<Variable>>, X: seq<Variable>, XL1i: seq<Variable>, XL2f: seq<Variable>, Y: set<Variable>, vsSSA: VariablesSSA) returns( S: Statement)
	requires ValidVsSSA(vsSSA)
	requires Valid(S')
	requires S'.Assignment? ==> forall i :: i in S'.LHS ==> vsSSA.existsVariable2(i)
	requires forall i :: i in XL1i ==> vsSSA.existsVariable2(i)
	requires forall i :: i in XL2f ==> vsSSA.existsVariable2(i)
	requires forall i,j :: j in XLs && i in j ==> vsSSA.existsVariable2(i)
	decreases *
	ensures ValidVsSSA(vsSSA)
	ensures Valid(S)
	ensures MergedVars(S', S, XLs, X)
{	
	match S' {
		case Assignment(LHS',RHS') => S := Skip;//AssignmentFromSSA(LHS', RHS', XLs, X, XL1i, XL2f, Y, vsSSA);
		case SeqComp(S1',S2') => S := Skip;//SeqCompFromSSA(S1', S2', XLs, X, XL1i, XL2f, Y, vsSSA);
		case IF(B0',Sthen',Selse') => S := Skip;//IfFromSSA(B0', Sthen', Selse', XLs, X, XL1i, XL2f, Y, vsSSA);
		case DO(B',S') => S := Skip;//DoFromSSA(B', S', XLs, X, XL1i, XL2f, Y, vsSSA);
		case LocalDeclaration(L,S0) => S := Skip;
		case Live(L,S0) => S := Skip; // TODO?
		case Assert(B) => S := Skip; // TODO?
		case Skip => S := Skip;
	}
}
/*
int t;
{
	int x,y;
	y:=0;	live {y}-{x}+{} = live {y}
	x:=1;	live {y}-{y}+{y} = live {y} // the problem
	y:=y+1; live {t}-{t}+{y} = live {y}
	t:=y;	live {x,t}-{x}+{} = live {t}
	x:=2;	live {t}-{t}+{x,t} = live {x,t}
	t:=x+t; live {t}
}
print t; // 3


After merge-vars {x,y} to z:

int t;
{
	int z;
	z:=0;	
	z:=1;	
	z:=z+1; 
	t:=z;	
	z:=2;	
	t:=z+t; 
}
print t; // 4


Illegal merge!
*/

predicate {:verify false}MergedVars1(S: Statement, T: Statement, XLs: seq<set<Variable>>, X: seq<Variable>)
	requires NoSelfAssignments(S)
	// ensures that each label of original S is the same label of T (res)
	// S=SV', T=res
{
	var R := Rename(S, XLs, X);

	T == RemoveEmptyAssignments(R)
}

predicate {:verify false}MergedVars(S: Statement, T: Statement, XLs: seq<set<Variable>>, X: seq<Variable>)
	requires NoSelfAssignments(S)
	requires NoSelfAssignments(T) // there is RemoveSelfAssignments in MergeVars
{
	T == Rename(S, XLs, X)
}

function method {:verify true}Rename(S: Statement, XLs: seq<set<Variable>>, X: seq<Variable>): (S': Statement)
	requires Core(S) && Valid(S)
	ensures Core(S') && Valid(S')
	ensures allLabelsOf(S) == allLabelsOf(S') 
{ 
	match S {
		case Assignment(LHS,RHS) => RenameAssignment(LHS, RHS, XLs, X)
									//x1,y2,z3 = 1,2,z4   x,y,z,=1,2,z    x,y=1,2  
		case SeqComp(S1,S2) =>		SeqComp(Rename(S1, XLs, X), Rename(S2, XLs, X))	
		case IF(B0,Sthen,Selse) =>	IF(RenameBoolExp(B0, XLs, X), Rename(Sthen, XLs, X), Rename(Selse, XLs, X))
		case DO(B,S1) =>			DO(RenameBoolExp(B, XLs, X), Rename(S1, XLs, X))
		case Skip =>				Skip 
	}
}

function method {:verify true}RenameAssignment(LHS: seq<Variable>, RHS: seq<Expression>, XLs: seq<set<Variable>>, X: seq<Variable>): (S: Statement)
	requires forall v1,v2 :: v1 in LHS && v2 in LHS && v1 != v2 ==> instanceToVariable(v1, XLs, X) != instanceToVariable(v2, XLs, X)
	ensures IsAssignment(S)
// rename and remove self assignments
//x1,y2,z3 = 1,2,z4   x,y,z,=1,2,z    x,y=1,2  
/*{
	if LHS == [] then Assignment([], []) else
	{
		var lhsX := instanceToVariable(LHS[0], XLs, X);
		var rhsX := instanceToVariable(RHS[0], XLs, X);
		var S' := RenameAssignment(LHS[1..], RHS[1..], XLs, X);

		if lhsX == rhsX then
		{
			S'
		}
		else
		{
			match S' {
				case Assignment(LHS',RHS') => Assignment([lhsX] + LHS', [rhsX] + RHS')
			}
		}
	}
}*/

function {:verify true}instanceToVariable(i: Variable, XLs: seq<set<Variable>>, X: seq<Variable>): Variable
{
	if i in XLs[0] then X[0]
	else
		instanceToVariable(i, XLs[1..], X[1..])
}

function method {:verify false}RenameBoolExp(B: BooleanExpression, XLs: seq<set<Variable>>, X: seq<Variable>): (B': BooleanExpression)

function method {:verify false}RemoveSelfAssignments(S: Statement): (S': Statement) // CHECK!
	ensures NoSelfAssignments(S')
{
	if SelfAssignmentsOnly(S) then Skip // convert to empty assignment NOT skip ?
	else
	match S {
		case Assignment(LHS,RHS) => RemoveSelfAssignment(LHS, RHS)
		case SeqComp(S1,S2) =>		if SelfAssignmentsOnly(S1) then
										RemoveSelfAssignments(S2)
									else if SelfAssignmentsOnly(S2) then
										RemoveSelfAssignments(S1)
									else
										SeqComp(RemoveSelfAssignments(S1), RemoveSelfAssignments(S2))
		case IF(B0,Sthen,Selse) =>	IF(B0, RemoveSelfAssignments(Sthen), RemoveSelfAssignments(Selse))
		case DO(B,S1) =>			DO(B, RemoveSelfAssignments(S1))
		case Skip =>				Skip
	}	
}

function method {:verify false}RemoveSelfAssignment(LHS: seq<Variable>, RHS: seq<Expression>): (S: Statement)
	requires !SelfAssignmentsOnly(Assignment(LHS,RHS))
	requires |LHS| == |RHS| && |LHS| >= 1
/*{
	if |LHS| == 1 then
		if LHS[0] == RHS[0] then
}*/

function method {:verify false}SelfAssignmentsOnly(S: Statement): bool
{
	match S {
		case Assignment(LHS,RHS) => SelfAssignmentOnly(LHS, RHS)
		case SeqComp(S1,S2) =>		SelfAssignmentsOnly(S1) && SelfAssignmentsOnly(S2)
		case IF(B0,Sthen,Selse) =>	SelfAssignmentsOnly(Sthen) && SelfAssignmentsOnly(Selse)
		case DO(B,S1) =>			SelfAssignmentsOnly(S1)
		case Skip =>				false
	}
}

function method {:verify false}SelfAssignmentOnly(LHS: seq<Variable>, RHS: seq<Expression>): bool
/*{
	if LHS == [] then true
	else
		if LHS[0] != RHS[0] then false
		else
			SelfAssignmentOnly(LHS[1..], RHS[1..])
}*/

predicate NoEmptyAssignments(S: Statement)
{
	match S {
		case Assignment(LHS,RHS) => LHS != [] && RHS != []
		case SeqComp(S1,S2) =>		NoEmptyAssignments(S1) && NoEmptyAssignments(S2)
		case IF(B0,Sthen,Selse) =>	NoEmptyAssignments(Sthen) && NoEmptyAssignments(Selse)
		case DO(B,S1) =>			NoEmptyAssignments(S1)
		case Skip =>				true
	}
}

predicate NoSelfAssignments(S: Statement)
{
	match S {
		case Assignment(LHS,RHS) => NoSelfAssignmentsInAssignment(LHS, RHS)
		case SeqComp(S1,S2) =>		NoSelfAssignments(S1) && NoSelfAssignments(S2)
		case IF(B0,Sthen,Selse) =>	NoSelfAssignments(Sthen) && NoSelfAssignments(Selse)
		case DO(B,S1) =>			NoSelfAssignments(S1)
		case Skip =>				true
	}
}

predicate NoSelfAssignmentsInAssignment(LHS: seq<Variable>, RHS: seq<Expression>)
/*{
	if LHS == [] then true
	else
		if LHS[0] == RHS[0] then false
		else
			SelfAssignmentOnly(LHS[1..], RHS[1..])
}*/

method {:verify false}AssignmentFromSSA(LHS': seq<Variable>, RHS': seq<Expression>, XLs: seq<set<Variable>>, X: seq<Variable>, XLi: seq<Variable>, XLf: seq<Variable>, Y: set<Variable>, vsSSA: VariablesSSA) returns (S: Statement)
	requires ValidVsSSA(vsSSA)
	requires Valid(Assignment(LHS',RHS'))
	requires forall i :: i in LHS' ==> vsSSA.existsVariable2(i)
	requires forall i :: i in XLi ==> vsSSA.existsVariable2(i)
	requires forall i :: i in XLf ==> vsSSA.existsVariable2(i)
	requires forall i :: i in SeqOfSetToSet(XLs) ==> vsSSA.existsVariable2(i)
	ensures ValidVsSSA(vsSSA)
	ensures Valid(S)
{
	// defined in thesis:
	// merge-vars.(" XL1f,XL2,XL3f,XL4,XL5f,XL6,Y1 := XL1i,XL2i,E1',E2',E3',E4',E5' ",
	// XLs, X, (XL1i, XL2i, XL3i, XL4i, XL7i, XL8i), (XL1f, XL3f, XL5f, XL7i), Y) is:
	// " X3,X4,X5,X6,Y1 := E1,E2,E3,E4,E5 "
	
	var Y1 := Y * def(Assignment(LHS', RHS'));
	var Y1Seq, E5', indexSeqY1 := GetXandE(LHS', RHS', Y1, 0);

	var XL7i := setOf(XLi) * setOf(XLf);
	assert XL7i <= setOf(XLi);
	var temp := setToSeq(XL7i);
	var X7Seq := vsSSA.instancesToVariables(temp);
	var X7 := setOf(X7Seq);
	
	var XL1iXL2i := setOf(XLi) * varsInExps(RHS');
	assert XL1iXL2i <= setOf(XLi);
	temp := setToSeq(XL1iXL2i);
	var X1X2 := vsSSA.instancesToVariables(temp);

	var XL3iXL4iXL8i := setOf(XLi) - XL1iXL2i - XL7i;
	assert XL3iXL4iXL8i <= setOf(XLi);
	temp := setToSeq(XL3iXL4iXL8i);
	var X3X4X8 := vsSSA.instancesToVariables(temp);

	var XL1fXL3fXL5f := setOf(XLf) - XL7i;
	assert XL1fXL3fXL5f <= setOf(XLf);
	temp := setToSeq(XL1fXL3fXL5f);
	var X1X3X5 := vsSSA.instancesToVariables(temp);

	var X3 := setOf(X1X3X5) * setOf(X3X4X8);
	temp := setToSeq(X3);
	var X3Instances := vsSSA.getInstancesOfVaribleSeq(temp);
	var XL3fSeq, E1', indexSeqXL3f := GetXandE(LHS', RHS', setOf(X3Instances), 0);

	var XL1fXL5f := XL1fXL3fXL5f - setOf(XL3fSeq);
	assert XL1fXL5f <= XL1fXL3fXL5f;
	temp := setToSeq(XL1fXL5f);
	var X1X5 := vsSSA.instancesToVariables(temp);

	var X1 := setOf(X1X2) * setOf(X1X5);
	temp := setToSeq(X1);
	var X1Instances := vsSSA.getInstancesOfVaribleSeq(temp);
	var XL1i := varsInExps(RHS') * setOf(X1Instances);
	var XL1f := setOf(LHS') * setOf(X1Instances);

	var XL5f := XL1fXL5f - XL1f;
	var XL5fSeq, E3', indexSeqXL5f := GetXandE(LHS', RHS', XL5f, 0);
	temp := setToSeq(XL5f);
	var X5SeqTemp := vsSSA.instancesToVariables(temp);
	var X5 := setOf(X5SeqTemp);

	var X2 := setOf(X1X2) - X1;
	temp := setToSeq(X2);
	var X2Instances := vsSSA.getInstancesOfVaribleSeq(temp);
	var XL2 := varsInExps(RHS') * setOf(X2Instances);

	var XL2XL4XL6 := setOf(LHS') - XL1f - setOf(XL3fSeq) - XL5f - Y1;
	assert XL2XL4XL6 <= setOf(LHS');
	var XL4XL6 := XL2XL4XL6 - XL2;
	assert XL4XL6 <= XL2XL4XL6;
	temp := setToSeq(XL4XL6);
	var X4X6 := vsSSA.instancesToVariables(temp);
	var X4 := setOf(X3X4X8) * setOf(X4X6);
	var X6 := setOf(X4X6) - X4;
	temp := setToSeq(X4);
	var X4Instances := vsSSA.getInstancesOfVaribleSeq(temp);
	var XL4 := setOf(X4Instances) * setOf(LHS');
	var XL6 := XL4XL6 - XL4;
	var XL4Seq, E2', indexSeqXL4 := GetXandE(LHS', RHS', XL4, 0);
	var XL6Seq, E4', indexSeqXL6 := GetXandE(LHS', RHS', XL6, 0);

	var X8 := setOf(X3X4X8) - X3 - X4;
	var XL3i := setOf(X3Instances) * setOf(XLi);
	var XL4i := setOf(X4Instances) * setOf(XLi);
	var XL8i := XL3iXL4iXL8i - XL3i - XL4i;
	var XL2i := XL1iXL2i - XL1i;

	////////////////////////////////////////

	var X3Seq := OrganizeVariables4(XL3fSeq, vsSSA);
	var X4Seq := OrganizeVariables4(XL4Seq, vsSSA);
	var X5Seq := OrganizeVariables4(XL5fSeq, vsSSA);
	var X6Seq := OrganizeVariables4(XL6Seq, vsSSA);
	
	/*var X3Seq := InstancesSetToSeq(X3, XL3fSeq, vsSSA);
	var X4Seq := InstancesSetToSeq(X4, XL4Seq, vsSSA);
	var X5Seq := InstancesSetToSeq(X5, XL5fSeq, vsSSA);
	var X6Seq := InstancesSetToSeq(X6, XL6Seq, vsSSA);*/

	////////////////////////////////////////

	var E1, E2, E3, E4, E5;

	E1 := SubstitueExpressionSeq(E1', [XL1i, XL2i, XL3i, XL4i, XL7i, XL8i], [X1, X2, X3, X4, X7, X8]);
	E2 := SubstitueExpressionSeq(E2', [XL1i, XL2i, XL3i, XL4i, XL7i, XL8i], [X1, X2, X3, X4, X7, X8]);
	E3 := SubstitueExpressionSeq(E3', [XL1i, XL2i, XL3i, XL4i, XL7i, XL8i], [X1, X2, X3, X4, X7, X8]);
	E4 := SubstitueExpressionSeq(E4', [XL1i, XL2i, XL3i, XL4i, XL7i, XL8i], [X1, X2, X3, X4, X7, X8]);
	E5 := SubstitueExpressionSeq(E5', [XL1i, XL2i, XL3i, XL4i, XL7i, XL8i], [X1, X2, X3, X4, X7, X8]);

	assert |E1| == |E1'| == |XL3fSeq| == |X3Seq|;
	assert |E2| == |E2'| == |XL4Seq| == |X4Seq|;
	assert |E3| == |E3'| == |XL5fSeq| == |X5Seq|;
	assert |E4| == |E4'| == |XL6Seq| == |X6Seq|;
	assert |E5| == |E5'| == |Y1Seq|;

	var LHS := X3Seq + X4Seq + X5Seq + X6Seq + Y1Seq;
	var RHS := E1 + E2 + E3 + E4 + E5;

	S := Assignment(LHS, RHS);
	assert |LHS| == |RHS|; // Works!
	assume Valid(S); // Fails due to new line 37 in Definitions.dfy.

	// About 40 minutes.
}

method {:verify false}SeqCompFromSSA(S1': Statement, S2': Statement, XLs: seq<set<Variable>>, X: seq<Variable>, XLi: seq<Variable>, XLf: seq<Variable>, Y: set<Variable>, vsSSA: VariablesSSA) returns (S: Statement)
	requires ValidVsSSA(vsSSA)
	requires Valid(SeqComp(S1',S2'))
	requires forall i :: i in XLi ==> vsSSA.existsVariable2(i)
	requires forall i :: i in XLf ==> vsSSA.existsVariable2(i)
	requires forall i :: i in SeqOfSetToSet(XLs) ==> vsSSA.existsVariable2(i)
	decreases *
	ensures ValidVsSSA(vsSSA)
	ensures Valid(S)

	ensures MergedVars(SeqComp(S1', S2'), S, XLs, X)
{
	// defined in thesis:
	// merge-vars.(" S1' ; S2' ", XLs, X, XL1i, XL2f, Y) is:
	// " merge-vars.(S1', XLs, X, XL1i, XL3, Y) ; merge-vars.(S2', XLs, X, XL3, XL2f, Y) "

	var XL3 := SeqOfSetToSet(XLs) * ((setOf(XLf) - ddef(S2')) + input(S2'));
	var XL3Seq := setToSeq(XL3);
	assert setOf(XL3Seq) <= SeqOfSetToSet(XLs);

	var S1 := MergeVars(S1', XLs, X, XLi, XL3Seq, Y, vsSSA);
	assert MergedVars(S1', S1, XLs, X);
	var S2 := MergeVars(S2', XLs, X, XL3Seq, XLf, Y, vsSSA);
	assert MergedVars(S2', S2, XLs, X);

	assert MergedVars(S1', S1, XLs, X); // from above
	
	L1SSA(S1, S1', S2, S2', XLs, X);

	assert MergedVars(SeqComp(S1', S2'), SeqComp(S1, S2), XLs, X);
	S := SeqComp(S1, S2);
	assert MergedVars(SeqComp(S1', S2'), S, XLs, X);
}

lemma L1SSA(S1: Statement, S1': Statement, S2: Statement, S2': Statement, XLs: seq<set<Variable>>, X: seq<Variable>)
	requires MergedVars(S1', S1, XLs, X)
	requires MergedVars(S2', S2, XLs, X)
	ensures MergedVars(SeqComp(S1', S2'), SeqComp(S1, S2), XLs, X)

method {:verify false}IfFromSSA(B' : BooleanExpression, S1' : Statement, S2' : Statement, XLs: seq<set<Variable>>, X: seq<Variable>, XLi: seq<Variable>, XLf: seq<Variable>, Y: set<Variable>, vsSSA: VariablesSSA) returns (S: Statement)
	requires ValidVsSSA(vsSSA)
	requires Valid(IF(B',S1',S2'))
	requires forall i :: i in XLi ==> vsSSA.existsVariable2(i)
	requires forall i :: i in XLf ==> vsSSA.existsVariable2(i)
	requires forall i :: i in SeqOfSetToSet(XLs) ==> vsSSA.existsVariable2(i)
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

method {:verify false}DoFromSSA(B' : BooleanExpression, S' : Statement, XLs: seq<set<Variable>>, X: seq<Variable>, XLi: seq<Variable>, XLf: seq<Variable>, Y: set<Variable>, vsSSA: VariablesSSA) returns (S: Statement)
	requires ValidVsSSA(vsSSA)
	requires Valid(DO(B',S'))
	requires forall i :: i in XLi ==> vsSSA.existsVariable2(i)
	requires forall i :: i in XLf ==> vsSSA.existsVariable2(i)
	requires forall i :: i in SeqOfSetToSet(XLs) ==> vsSSA.existsVariable2(i)
	decreases *
	ensures ValidVsSSA(vsSSA)
	ensures Valid(S)
{
	// defined in thesis:
	// merge-vars.(" while B' do S1' od ", XLs, X, (XL1i, XL2i), XL2i, Y) is:
	// " while B do merge-vars.(S1', XLs, X, (XL1i, XL2i), (XL1i, XL2i), Y) od "

	var XL2i := setOf(XLi) * setOf(XLf);
	assert XL2i <= setOf(XLi);
	var XL1i := setOf(XLi) - XL2i;
	assert XL1i <= setOf(XLi);

	var X1 := {};
	/* Is it: (compiles)
		var XL1iSeq := setToSeq(XL1i);
		assert forall i :: i in XL1iSeq ==> vsSSA.existsVariable2(i);
		var X1Seq := vsSSA.instancesToVariables(XL1iSeq);
		var X1 := setOf(X1Seq);
	?
	If so, I should change it in IfFromSSA also.
	*/

	var X2 := {};
	/* Is it: (compiles)
		var XL2iSeq := setToSeq(XL2i);
		assert forall i :: i in XL2iSeq ==> vsSSA.existsVariable2(i);
		var X2Seq := vsSSA.instancesToVariables(XL2iSeq);
		var X2 := setOf(X2Seq);
	?
	If so, I should change it in IfFromSSA also.
	*/

	var B := SubstitueBooleanExpression(B', [X1,X2], [XL1i,XL2i]);

	S := MergeVars(S', XLs, X, XLi, XLi, Y, vsSSA);
	S := DO(B, S);
}


///////////////////////////////////////////////////////////////////////////////////////////////////


/*function FlowInsensitiveSlice(S: Statement, V: set<Variable>): Statement
	// FIXME: generalize
	requires S == Assignment(["i","sum", "prod"],["i+1","sum+i","prod*i"])
{
	if V == {"sum"} then Assignment(["sum"],["sum+i"])
	else Assignment(["i","prod"],["i+1","prod*i"])
}

function method GetAssignmentsOfV(LHS : seq<Variable>, RHS : seq<Expression>, V: set<Variable>) : Statement

{
	if LHS == [] then Skip
	else if LHS[0] in V then 
	var tempRes := GetAssignmentsOfV(LHS[1..], RHS[1..], V);
	match tempRes {
		case Assignment(LHS1,RHS1) => Assignment([LHS[0]]+LHS1, [RHS[0]]+RHS1)
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
	}
}

function method ComputeSlidesDepRtc(S: Statement, V: set<Variable>) : set<Variable>

{
	var slidesSV := ComputeSlides(S, V);
	var U := glob(slidesSV) * def(S);

	if U <= V then V else ComputeSlidesDepRtc(S, V + U)
}


method ComputeFISlice(S: Statement, V: set<Variable>) returns (SV: Statement)
	ensures SV == FlowInsensitiveSlice(S,V)
{
	var Vstar := ComputeSlidesDepRtc(S, V);

	SV := ComputeSlides(S, Vstar);
}*/