include "Definitions.dfy"
include "Substitutions.dfy"
include "Util.dfy"
include "Laws.dfy"

class VariablesSSA {

	var instancesOf: map<Variable, seq<Variable>>;
	ghost var variableOf: map<Variable, Variable>;
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

 method freshInit(vars : seq<Variable>, ghost allVars : set<Variable>, vsSSA : VariablesSSA) returns (res: seq<Variable>)
	requires ValidVsSSA(vsSSA)
	ensures |res| == |vars|
	modifies vsSSA
	ensures ValidVsSSA(vsSSA)
	ensures vsSSA.instancesOf == old(vsSSA.instancesOf)
	ensures vsSSA.variableOf == old(vsSSA.variableOf)
{
	if vars == [] { res := []; } 
	else
	{
		var n := vsSSA.getAndIncN();
		var nStr := intToString(n);
		var newInstance := vars[0] + nStr;
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

method {:verify false}FindVariableIndexInVariableSequence2(v: Variable, V: seq<Variable>) returns (i: int)
	requires v in V
	ensures i >= 0 && i < |V|
{
	if |V| == 1 { i := 0; }
	else if V[0] == v { i := 0; }
	else
	{
		i := FindVariableIndexInVariableSequence2(v, V[1..]);
		i := i + 1;
	}
}

method {:verify false}FindVariableIndexInVariableSequence(v: Variable, V: seq<Variable>) returns (i: int)
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


method {:verify false}OrganizeVariables2(vars1: seq<Variable>, instances2: seq<Variable>, vars2: seq<Variable>, vsSSA: VariablesSSA) returns (res: seq<Variable>)
	requires ValidVsSSA(vsSSA)
	requires forall v :: v in vars1 ==> vsSSA.existsInstance(v)
	requires forall v :: v in vars2 ==> vsSSA.existsInstance(v)
	requires forall i :: i in instances2 ==> vsSSA.existsVariable2(i)
	requires |vars2| == |instances2|
	requires forall v :: v in vars1 ==> v in vars2
	ensures ValidVsSSA(vsSSA)
	ensures |vars1| == |res|
{
	if vars1 == [] { res := []; }
	else
	{
		var index := FindVariableIndexInVariableSequence2(vars1[0], vars2);
		assert index >= 0 && index < |vars2|;
		var res' := OrganizeVariables2(vars1[1..], instances2, vars2, vsSSA);

		res := [instances2[index]] + res';
	}
}


method {:verify false}OrganizeVariables(vars1: seq<Variable>, vars2: seq<Variable>, vsSSA: VariablesSSA) returns (res: seq<Variable>)
	requires ValidVsSSA(vsSSA)
	requires forall i :: i in vars1 ==> vsSSA.existsVariable2(i)
	requires forall i :: i in vars2 ==> vsSSA.existsVariable2(i)
	ensures ValidVsSSA(vsSSA)
	//ensures |vars1| == |res|
{
	if vars1 == [] { res := []; }
	else
	{
		var v1 := vsSSA.getVariableInRegularFormFunc(vars1[0]);
		var vars2Variables := vsSSA.instancesToVariables(vars2);
		var index := FindVariableIndexInVariableSequence(v1, vars2Variables);
		var res' := OrganizeVariables(vars1[1..], vars2, vsSSA);

		res := res';

		if index != -1 { res := [vars2[index]] + res'; }
	}
}

/*method OrganizeVariables(vars1: seq<Variable>, vars2: seq<Variable>, vsSSA: VariablesSSA) returns (res: seq<Variable>)
	requires ValidVsSSA(vsSSA)
	requires forall i :: i in vars1 ==> vsSSA.existsVariable2(i)
	requires forall i :: i in vars2 ==> vsSSA.existsVariable2(i)
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

function InstancesAndVariablesBreakdown(S: Statement, X: seq<Variable>, 
	liveOnEntry: set<Variable>, liveOnExit: set<Variable>, XLs: set<Variable>, vsSSA: VariablesSSA): 
	(seq<Variable>,seq<Variable>,seq<Variable>,seq<Variable>,seq<Variable>,seq<Variable>,
	seq<Variable>,seq<Variable>,seq<Variable>,seq<Variable>,seq<Variable>)
/*	requires ValidVsSSA(vsSSA)
	reads vsSSA
{
	var XL3iSet := liveOnEntry * liveOnExit;
	assert XL3i <= liveOnEntry && XL3i <= liveOnExitX;
	var XL3i := setToSeq(XL3i);
	var X3 := vsSSA.instancesToVariables(XL3i);
	var X3Set := setOf(X3);

	var XL1iXL2iXL4i := liveOnEntry - XL3iSet;
	assert XL1iXL2iXL4i <= liveOnEntry;
	var temp := setToSeq(XL1iXL2iXL4i);
	var X1X2X4 := vsSSA.instancesToVariables(temp);
	var XL4fXL5f := liveOnExitX - XL3i;
	assert XL4fXL5f <= liveOnExitX;
	var temp2 := setToSeq(XL4fXL5f);
	var X4X5 := vsSSA.instancesToVariables(temp2);
	var X4Set := setOf(X1X2X4) * setOf(X4X5) * setOf(X);
	//var X4 := vsSSA.instancesToVariables(X4Set)
	var X5Set := setOf(X4X5) - X4Set;
	var X5 := setToSeq(X5Set);
	var XL5f := vsSSA.getInstancesOfVaribleSeq
	
	var X1X2 := setOf(X1X2X4) - X4;
	var X2 := X1X2 * def(Assignment(LHS,RHS));
	var X1 := X1X2 - X2;

	(XL1i,XL2i,XL3i,XL4i,XL4f,XL5f,X1,X2,X3,X4,X5)
}*/

function ToSSALeft(S: Statement, XL3i: seq<Variable>, XL4f: seq<Variable>, XL5f: seq<Variable>, 
	X3: seq<Variable>, X4: seq<Variable>, X5: seq<Variable>, Y: seq<Variable>): Statement
{
	Live(XL3i+XL4f+XL5f+Y,SeqComp(S,Assignment(XL3i+XL4f+XL5f,seqVarToSeqExpr(X3+X4+X5))))
}

function ToSSARight(XL1i: seq<Variable>, XL2i: seq<Variable>, XL3i: seq<Variable>, XL4i: seq<Variable>,	
	X1: seq<Variable>, X2: seq<Variable>, X3: seq<Variable>, X4: seq<Variable>, 
	S': Statement, XL4f: seq<Variable>, XL5f: seq<Variable>, Y: seq<Variable>): Statement
{
	Live(XL3i+XL4f+XL5f+Y,SeqComp(Assignment(XL1i+XL2i+XL3i+XL4i,seqVarToSeqExpr(X1+X2+X3+X4)),S'))
}

// TODO: move to a more central/reusable location: Util? Definitions?
predicate mutuallyDisjoint3<T>(s1: seq<T>, s2: seq<T>, s3: seq<T>)
{
	|setOf(s1+s2+s3)| == |s1|+|s2|+|s3|
}

predicate mutuallyDisjoint4<T>(s1: seq<T>, s2: seq<T>, s3: seq<T>, s4: seq<T>)
{
	|setOf(s1+s2+s3+s4)| == |s1|+|s2|+|s3|+|s4|
}

predicate mutuallyDisjoint5<T>(s1: seq<T>, s2: seq<T>, s3: seq<T>, s4: seq<T>, s5: seq<T>)
{
	|setOf(s1+s2+s3+s4+s5)| == |s1|+|s2|+|s3|+|s4|+|s5|
}

predicate mutuallyDisjoint6<T>(s1: seq<T>, s2: seq<T>, s3: seq<T>, s4: seq<T>, s5: seq<T>, s6: seq<T>)
{
	|setOf(s1+s2+s3+s4+s5+s6)| == |s1|+|s2|+|s3|+|s4|+|s5|+|s6|
}

predicate PreconditionsOfToSSA(S: Statement, S': Statement, X: seq<Variable>, 
	XL1i: seq<Variable>, XL2i: seq<Variable>, XL3i: seq<Variable>, XL4i: seq<Variable>, 
	XL4f: seq<Variable>, XL5f: seq<Variable>, 
	X1: seq<Variable>, X2: seq<Variable>, X3: seq<Variable>, X4: seq<Variable>, X5: seq<Variable>, 
	Y: set<Variable>, XLs: set<Variable>)
{
	glob(S) <= setOf(X)+Y                                                                                    // P1
	&& mutuallyDisjoint5(X1,X2,X3,X4,X5) && setOf(X1+X2+X3+X4+X5) <= setOf(X)                                // P2
	&& mutuallyDisjoint6(XL1i,XL2i,XL3i,XL4i,XL4f,XL5f) && setOf(XL1i+XL2i+XL3i+XL4i+XL4f+XL5f) <= XLs       // P3
	&& setOf(X) !! Y && XLs !! setOf(X)+Y                                                                    // P4
	&& setOf(X1) !! setOf(X3) && setOf(X1+X3) !! def(S)                                                      // P5
	&& mutuallyDisjoint3(X2,X4,X5) && setOf(X2+X4+X5) <= def(S)                                              // P6
	&& mutuallyDisjoint4(X1,X2,X3,X4) && setOf(X) * (setOf(X3+X4+X5)-ddef(S)+input(S)) <= setOf(X1+X2+X3+X4) // P7
}

predicate CorrectnessOfToSSA(S: Statement, S': Statement, X: seq<Variable>, liveOnEntryX: set<Variable>, liveOnExitX: set<Variable>, Y: set<Variable>, XLs: set<Variable>, vsSSA: VariablesSSA)
	reads * //vsSSA
	requires ValidVsSSA(vsSSA)
{
	var xs := InstancesAndVariablesBreakdown(S,X,liveOnEntryX,liveOnExitX,XLs,vsSSA);
	var XL1i,XL2i,XL3i,XL4i,XL4f,XL5f,X1,X2,X3,X4,X5 := xs.0,xs.1,xs.2,xs.3,xs.4,xs.5,xs.6,xs.7,xs.8,xs.9,xs.10;
	var Y' := fSetToSeq(Y);
	PreconditionsOfToSSA(S,S',X,XL1i,XL2i,XL3i,XL4i,XL4f,XL5f,X1,X2,X3,X4,X5,Y,XLs) ==>
	Valid(ToSSALeft(S,XL3i,XL4f,XL5f,X3,X4,X5,Y')) && Valid(ToSSARight(XL1i,XL2i,XL3i,XL4i,X1,X2,X3,X4,S',XL4f,XL5f,Y')) &&
	EquivalentStatments(ToSSALeft(S,XL3i,XL4f,XL5f,X3,X4,X5,Y'),ToSSARight(XL1i,XL2i,XL3i,XL4i,X1,X2,X3,X4,S',XL4f,XL5f,Y')) // Q1
	&& setOf(X) !! glob(S') // Q2
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
{
	//var vsSSA := new VariablesSSA(); // Create in main!

	match S {
		/*case Assignment(LHS,RHS) => S' := AssignmentToSSA(LHS, RHS, X, liveOnEntryX, liveOnExitX, Y, XLs, vsSSA);
		case SeqComp(S1,S2) => S' := SeqCompToSSA(S1, S2, X, liveOnEntryX, liveOnExitX, Y, XLs, vsSSA);
		case IF(B0,Sthen,Selse) => S' := IfToSSA(B0, Sthen, Selse, X, liveOnEntryX, liveOnExitX, Y, XLs, vsSSA);
		case DO(B,S) => S' := DoToSSA(B, S, X, liveOnEntryX, liveOnExitX, Y, XLs, vsSSA);
		case LocalDeclaration(L,S0) => S' := Skip;
		case Skip => S' := Skip;*/

		case Assignment(LHS,RHS) => S' := Skip;//AssignmentToSSA(LHS, RHS, X, liveOnEntryX, liveOnExitX, Y, XLs, vsSSA);
		case SeqComp(S1,S2) => S' := SeqCompToSSA(S1, S2, X, liveOnEntryX, liveOnExitX, Y, XLs, vsSSA);
		case IF(B0,Sthen,Selse) => S' := Skip;//IfToSSA(B0, Sthen, Selse, X, liveOnEntryX, liveOnExitX, Y, XLs, vsSSA);
		case DO(B,S) => S' := Skip;//DoToSSA(B, S, X, liveOnEntryX, liveOnExitX, Y, XLs, vsSSA);
		case Skip => S' := Skip;
	}
}


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

method {:verify true}SeqCompToSSA(S1: Statement, S2: Statement, X: seq<Variable>, liveOnEntryX: set<Variable>, liveOnExitX: set<Variable>, Y: set<Variable>, XLs: set<Variable>, vsSSA: VariablesSSA) returns (S': Statement)
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
	ensures CorrectnessOfToSSA(IF(B,S1,S2),S',X,liveOnEntryX,liveOnExitX,Y,XLs,vsSSA)
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
	assert CorrectnessOfToSSA(IF(B,S1,S2),S',X,liveOnEntryX,liveOnExitX,Y,XLs,vsSSA) by
	{
		assume CorrectnessOfToSSA(IF(B,S1,S2),S',X,XL1i+XL2i+XL3i+XL4i,XL3i+XL4f+XL5f,Y,XLs,vsSSA);
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
	}
}

lemma LemmaIfToSSAIsCorrect(B: BooleanExpression, S1: Statement, S2: Statement,
		X: seq<Variable>, XL1i: seq<Variable>, XL2i: seq<Variable>, XL3i: seq<Variable>, XL4i: seq<Variable>,
		XL4f: seq<Variable>, XL5f: seq<Variable>, Y: seq<Variable>, XLs: set<Variable>,
		X1: seq<Variable>, X2: seq<Variable>, X3: seq<Variable>, X4: seq<Variable>, X5: seq<Variable>,
		S1': Statement,	XL4t: seq<Variable>, XL5t: seq<Variable>, XL4e: seq<Variable>, XL5e: seq<Variable>,
		X4d1: seq<Variable>, X4d2: seq<Variable>, X4d1d2: seq<Variable>,
		XL4d1t: seq<Variable>, XL4d1e: seq<Variable>, XL4d1d2t: seq<Variable>, XL4d1d2e: seq<Variable>, XL4d2i: seq<Variable>,
		XL4d1i: seq<Variable>, XL4d2e: seq<Variable>, XLs': set<Variable>, XLs'': set<Variable>,
		S2': Statement, vsSSA: VariablesSSA)
	requires ValidVsSSA(vsSSA)
	requires |X1+X2+X3+X4| == |XL1i+XL2i+XL3i+XL4i| && setOf(X1+X2+X3+X4) !! setOf(XL1i+XL2i+XL3i+XL4i)
	requires var B' := BSubstitute(B,X1+X2+X3+X4,XL1i+XL2i+XL3i+XL4i);
		PreconditionsOfToSSA(IF(B,S1,S2),IF(B',S1',S2'),X,XL1i,XL2i,XL3i,XL4i,XL4f,XL5f,X1,X2,X3,X4,X5,setOf(Y),XLs) &&
		Valid(ToSSALeft(IF(B,S1,S2),XL3i,XL4f,XL5f,X3,X4,X5,Y)) &&
		Valid(ToSSARight(XL1i,XL2i,XL3i,XL4i,X1,X2,X3,X4,IF(B',S1',S2'),XL4f,XL5f,Y))
	ensures var B' := BSubstitute(B,X1+X2+X3+X4,XL1i+XL2i+XL3i+XL4i);
		CorrectnessOfToSSA(IF(B,S1,S2),IF(B',S1',S2'),X,setOf(XL1i+XL2i+XL3i+XL4i),setOf(XL3i+XL4f+XL5f),setOf(Y),XLs,vsSSA)
/*{
	var B' := BSubstitute(B,X1+X2+X3+X4,XL1i+XL2i+XL3i+XL4i);
	var S,S' := IF(B,S1,S2),IF(B',S1',S2');
	// TODO: Be sure first that the breakdown is the same; is it???
	var liveOnEntryX,liveOnExitX := setOf(XL1i+XL2i+XL3i+XL4i),setOf(XL3i+XL4f+XL5f);
	var xs := InstancesAndVariablesBreakdown(S,X,liveOnEntryX,liveOnExitX,XLs,vsSSA);
	var XL1i',XL2i',XL3i',XL4i',XL4f',XL5f',X1',X2',X3',X4',X5' := xs.0,xs.1,xs.2,xs.3,xs.4,xs.5,xs.6,xs.7,xs.8,xs.9,xs.10;
	//and then...
	assume Valid(ToSSALeft(S,XL3i',XL4f',XL5f',X3',X4',X5',Y)) && Valid(ToSSARight(XL1i,XL2i,XL3i,XL4i,X1,X2,X3,X4,S',XL4f,XL5f,Y)) &&
		EquivalentStatments(ToSSALeft(S,XL3i,XL4f,XL5f,X3,X4,X5,Y),ToSSARight(XL1i,XL2i,XL3i,XL4i,X1,X2,X3,X4,S',XL4f,XL5f,Y));// by {
}/
/*
/*	
not sure about the parameters to D3, should figure it out and fix; and then
should show that the preconditions above indeed guarantee that the preconditions of D3 (below, after the appropriate parameter substitutions) all hold;
and finally show that the postcondition of D3 (again, with the appropriate substitution) guarantee that our postconditions hold.

D.3:
	Live(XL2f+Y,SeqComp(IF(B,S1,S2),Assignment(XL2f,seqVarToSeqExpr(X2))))
==
	Live(XL2f+Y,SeqComp(Assignment(XL1i,seqVarToSeqExpr(X1)),IF(B',S1',S2')))


*/
		var XL1i',XL2f',X1',X2' := setOf(XL1i+XL2i+XL3i+XL4i),X1+X2+X3+X4,
		assert TransformationD3Left(B,S1,S2,X2,XL2f,Y),TransformationD3Right(B',S1',S2',X1,XL1i,XL2f,Y) && 
			EquivalentStatments(TransformationD3Left(B,S1,S2,X2,XL2f,Y),TransformationD3Right(B',S1',S2',X1,XL1i,XL2f,Y)) by {
		TransformationD3(B,B',S1,S2,S1',S2',X1,X2,XL1i,XL2i,XL2f,Y);

/*
requires Valid(Live(XL2f+Y,SeqComp(S2,Assignment(XL2f,seqVarToSeqExpr(X2)))))
	requires Valid(Live(XL2f+Y,SeqComp(Assignment(XL1i,seqVarToSeqExpr(X1)),S2')))
	requires EquivalentStatments(Live(XL2f+Y,SeqComp(S2,Assignment(XL2f,seqVarToSeqExpr(X2)))),
		Live(XL2f+Y,SeqComp(Assignment(XL1i,seqVarToSeqExpr(X1)),S2'))) // P5
	requires Valid(Live(XL2f+Y,SeqComp(S1,Assignment(XL2f,seqVarToSeqExpr(X2)))))
	requires Valid(Live(XL2f+Y,SeqComp(Assignment(XL1i,seqVarToSeqExpr(X1)),S1')))
	requires EquivalentStatments(Live(XL2f+Y,SeqComp(S1,Assignment(XL2f,seqVarToSeqExpr(X2)))),
		Live(XL2f+Y,SeqComp(Assignment(XL1i,seqVarToSeqExpr(X1)),S1'))) // P4
	requires setOf(XL1i) !! B.1 // P3
	requires setOf(XL1i) !! setOf(X1) // P2
	requires |X1| == |XL1i|
	requires EquivalentBooleanExpressions(B',BSubstitute(B,X1,XL1i)) // P1

	requires Valid(TransformationD3Left(B,S1,S2,X2,XL2f,Y))
	requires Valid(TransformationD3Right(B',S1',S2',X1,XL1i,XL2f,Y))
	ensures EquivalentStatments(TransformationD3Left(B,S1,S2,X2,XL2f,Y),
			TransformationD3Right(B',S1',S2',X1,XL1i,XL2f,Y))
			*/
	}	
	assert setOf(X) !! glob(S'); // Q2
}*/
*/

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

	var tempDO := DO(B', S');
	var tempAssignment := Assignment(XL2Seq + XL4fSeq, seqVarToSeqExpr(XL2bSeq + XL4bSeq));
	assert Valid(tempDO);
	assert Valid(tempAssignment);
	var DO' := SeqComp(tempDO, tempAssignment);
	assert Valid(DO');
	//var DO' := SeqComp(DO(B', S'), Assignment(XL2Seq + XL4fSeq, XL2bSeq + XL4bSeq));
	tempAssignment := Assignment(XL2Seq + XL4fSeq, seqVarToSeqExpr(XL2iSeq + XL4iSeq));
	assert Valid(tempAssignment);
	S'' := SeqComp(tempAssignment, DO');
	//S'' := SeqComp(Assignment(XL2Seq + XL4fSeq, XL2iSeq + XL4iSeq), DO');
	assert Valid(S'');
}

method {:verify false}FromSSA(S': Statement, X: seq<Variable>, XL1i: seq<Variable>, XL2f: seq<Variable>, Y: set<Variable>, XLs: set<Variable>, vsSSA: VariablesSSA) returns( S: Statement)
	requires ValidVsSSA(vsSSA)
	requires Valid(S')
	decreases *
	ensures ValidVsSSA(vsSSA)
	ensures Valid(S)
{
	S := MergeVars(S', XLs, X, XL1i, XL2f, Y, vsSSA);
}

method {:verify false}MergeVars(S': Statement, XLs: set<Variable>, X: seq<Variable>, XL1i: seq<Variable>, XL2f: seq<Variable>, Y: set<Variable>, vsSSA: VariablesSSA) returns( S: Statement)
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
	requires forall i :: i in XLi ==> vsSSA.existsVariable2(i)
	requires forall i :: i in XLf ==> vsSSA.existsVariable2(i)
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
	assert forall i :: i in temp ==> vsSSA.existsVariable2(i);
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

function TransformationD3Left(B: BooleanExpression, 
		S1: Statement, S2: Statement,
		X2: seq<Variable>,
		XL2f: seq<Variable>, Y: seq<Variable>): Statement
{
	Live(XL2f+Y,SeqComp(IF(B,S1,S2),Assignment(XL2f,seqVarToSeqExpr(X2))))
}

function TransformationD3Right(B': BooleanExpression, 
		S1': Statement, S2': Statement,
		X1: seq<Variable>,
		XL1i: seq<Variable>, XL2f: seq<Variable>, Y: seq<Variable>): Statement
{
	Live(XL2f+Y,SeqComp(Assignment(XL1i,seqVarToSeqExpr(X1)),IF(B',S1',S2')))
}

lemma TransformationD3(B: BooleanExpression, B': BooleanExpression, 
		S1: Statement, S2: Statement, S1': Statement, S2': Statement,
		X1: seq<Variable>, X2: seq<Variable>,
		XL1i: seq<Variable>, XL2i: seq<Variable>, XL2f: seq<Variable>, Y: seq<Variable>)
	requires Valid(Live(XL2f+Y,SeqComp(S2,Assignment(XL2f,seqVarToSeqExpr(X2)))))
	requires Valid(Live(XL2f+Y,SeqComp(Assignment(XL1i,seqVarToSeqExpr(X1)),S2')))
	requires EquivalentStatments(Live(XL2f+Y,SeqComp(S2,Assignment(XL2f,seqVarToSeqExpr(X2)))),
		Live(XL2f+Y,SeqComp(Assignment(XL1i,seqVarToSeqExpr(X1)),S2'))) // P5
	requires Valid(Live(XL2f+Y,SeqComp(S1,Assignment(XL2f,seqVarToSeqExpr(X2)))))
	requires Valid(Live(XL2f+Y,SeqComp(Assignment(XL1i,seqVarToSeqExpr(X1)),S1')))
	requires EquivalentStatments(Live(XL2f+Y,SeqComp(S1,Assignment(XL2f,seqVarToSeqExpr(X2)))),
		Live(XL2f+Y,SeqComp(Assignment(XL1i,seqVarToSeqExpr(X1)),S1'))) // P4
	requires setOf(XL1i) !! B.1 // P3
	requires setOf(XL1i) !! setOf(X1) // P2
	requires |X1| == |XL1i|
	requires EquivalentBooleanExpressions(B',BSubstitute(B,X1,XL1i)) // P1

	requires Valid(TransformationD3Left(B,S1,S2,X2,XL2f,Y))
	requires Valid(TransformationD3Right(B',S1',S2',X1,XL1i,XL2f,Y))
	ensures EquivalentStatments(TransformationD3Left(B,S1,S2,X2,XL2f,Y),
			TransformationD3Right(B',S1',S2',X1,XL1i,XL2f,Y))
{
	var T1 := TransformationD3Left(B,S1,S2,X2,XL2f,Y);
	var T2 := TransformationD3Right(B',S1',S2',X1,XL1i,XL2f,Y);
	forall P: Predicate ensures EquivalentPredicates(wp(T1,P),wp(T2,P)) {
		var P1 := wp(T1,P);
		var P2 := wp(T2,P);
		forall s: State | P1.0.requires(s) && P2.0.requires(s) ensures P1.0(s) == P2.0(s) {
			calc {
				wp(T2,P).0(s);
			== // def. of T2 and of TransformationD3Right
				wp(Live(XL2f+Y,SeqComp(Assignment(XL1i,seqVarToSeqExpr(X1)),IF(B',S1',S2'))),P).0(s);
			== { assert B'.0(s) == BSubstitute(B,X1,XL1i).0(s); // from P1
						var IF1,IF1',V := IF(BSubstitute(B,X1,XL1i),S1',S2'),IF(B',S1',S2'),XL2f+Y;
						assert EquivalentStatments(IF1',IF1);
						var A1 := Assignment(XL1i,seqVarToSeqExpr(X1));
						var SC1,SC1' := SeqComp(A1,IF1),SeqComp(A1,IF1');
						assert EquivalentStatments(SC1',SC1) by { assert EquivalentStatments(IF1',IF1); Leibniz4(A1,IF1,IF1'); }
						assert EquivalentStatments(Live(V,SC1'),Live(V,SC1));
						}
				wp(Live(XL2f+Y,SeqComp(Assignment(XL1i,seqVarToSeqExpr(X1)),IF(BSubstitute(B,X1,XL1i),S1',S2'))),P).0(s);
			== { assert setOf(XL1i) !! setOf(X1); // P2
						Law18b(S1',S2',BSubstitute(B,X1,XL1i),[],XL1i,[],seqVarToSeqExpr(X1)); }
				wp(Live(XL2f+Y,SeqComp(Assignment(XL1i,seqVarToSeqExpr(X1)),IF(BSubstituteVbyE(BSubstitute(B,X1,XL1i),XL1i,seqVarToSeqExpr(X1)),S1',S2'))),P).0(s);
			== {// remove redundant (reversed) double sub.
					var B'' := BSubstituteVbyE(BSubstitute(B,X1,XL1i),XL1i,seqVarToSeqExpr(X1));
					assert EquivalentBooleanExpressions(B,B'') by { assert setOf(XL1i) !! B.1; /* P3 */ ReversedDoubleSubstitutions(B,X1,XL1i); }
					assert EquivalentStatments(IF(B,S1',S2'),IF(B'',S1',S2'));
					var A1,IF1,IF1',V := Assignment(XL1i,seqVarToSeqExpr(X1)),IF(B,S1',S2'),IF(B'',S1',S2'),XL2f+Y;
					var SC1,SC2 := SeqComp(A1,IF1'),SeqComp(A1,IF1);
					assert EquivalentStatments(SC1,SC2) by { assert EquivalentStatments(IF1',IF1); Leibniz4(A1,IF1',IF1); }
					assert EquivalentStatments(Live(V,SC1),Live(V,SC2));
					}
				wp(Live(XL2f+Y,SeqComp(Assignment(XL1i,seqVarToSeqExpr(X1)),IF(B,S1',S2'))),P).0(s);
			== { assert setOf(XL1i) !! B.1; // P3
						Law3(Assignment(XL1i,seqVarToSeqExpr(X1)),S1',S2',B); } // distribute statement over IF
				wp(Live(XL2f+Y,IF(B,SeqComp(Assignment(XL1i,seqVarToSeqExpr(X1)),S1'),SeqComp(Assignment(XL1i,seqVarToSeqExpr(X1)),S2'))),P).0(s);
			== { Law21(B,SeqComp(Assignment(XL1i,seqVarToSeqExpr(X1)),S1'),SeqComp(Assignment(XL1i,seqVarToSeqExpr(X1)),S2'),XL2f+Y); } // propagate liveness info.
				wp(Live(XL2f+Y,IF(B,Live(XL2f+Y,SeqComp(Assignment(XL1i,seqVarToSeqExpr(X1)),S1')),
					Live(XL2f+Y,SeqComp(Assignment(XL1i,seqVarToSeqExpr(X1)),S2')))),P).0(s);
			== { var V := XL2f+Y;
						var T1 := Live(V,SeqComp(S1,Assignment(XL2f,seqVarToSeqExpr(X2))));
						var T1' := Live(V,SeqComp(Assignment(XL1i,seqVarToSeqExpr(X1)),S1'));
						assert EquivalentStatments(T1,T1'); // P4
						var T2 := Live(V,SeqComp(S2,Assignment(XL2f,seqVarToSeqExpr(X2))));
						var T2' := Live(V,SeqComp(Assignment(XL1i,seqVarToSeqExpr(X1)),S2'));
						assert EquivalentStatments(T2,T2'); // P5
						var IF1,IF1' := IF(B,T1,T2),IF(B,T1',T2');
						assert EquivalentStatments(IF1',IF1);
						assert EquivalentStatments(Live(V,IF1'),Live(V,IF1));
					}
				wp(Live(XL2f+Y,IF(B,Live(XL2f+Y,SeqComp(S1,Assignment(XL2f,seqVarToSeqExpr(X2)))),
					Live(XL2f+Y,SeqComp(S2,Assignment(XL2f,seqVarToSeqExpr(X2)))))),P).0(s);
			== { Law21(B,SeqComp(S1,Assignment(XL2f,seqVarToSeqExpr(X2))),SeqComp(S2,Assignment(XL2f,seqVarToSeqExpr(X2))),XL2f+Y); } // remove liveness info.
				wp(Live(XL2f+Y,IF(B,SeqComp(S1,Assignment(XL2f,seqVarToSeqExpr(X2))),SeqComp(S2,Assignment(XL2f,seqVarToSeqExpr(X2))))),P).0(s);
			== { Law4(S1,S2,Assignment(XL2f,seqVarToSeqExpr(X2)),B); } // dist. IF over ";"
				wp(Live(XL2f+Y,SeqComp(IF(B,S1,S2),Assignment(XL2f,seqVarToSeqExpr(X2)))),P).0(s);
			== // def. of T1 and of TransformationD3Left
				wp(T1,P).0(s);
			}
		}
	}
}

//method TransformationD5(S: Statement, X: seq<Variable>, X: seq<Variable>) returns (S': Statement)

function IfToSSACorrectnessLeft(B: BooleanExpression, S1: Statement, S2: Statement,
		X3: seq<Variable>, X4: seq<Variable>, X5: seq<Variable>, // live-on-exit variables (the X2 of D.3)
		XL3i: seq<Variable>, XL4f: seq<Variable>, XL5f: seq<Variable>, // live-on-exit instances (the XL2f of D.3)
		Y: seq<Variable>): Statement
{
//	Live(XL3i+XL4f+XL5f+Y,SeqComp(IF(B,S1,S2),Assignment(XL3i+XL4f+XL5f,seqVarToSeqExpr(X3+X4+X5))))
	TransformationD3Left(B,S1,S2,X3+X4+X5,XL3i+XL4f+XL5f,Y)
//	Live(XL2f          +Y,SeqComp(IF(B,S1,S2),Assignment(XL2f          ,seqVarToSeqExpr(X2      ))))
}

function IfToSSACorrectnessRight(B': BooleanExpression, S1': Statement, S2': Statement,
		X1: seq<Variable>, X2: seq<Variable>, X3: seq<Variable>, X4: seq<Variable>, // live-on-entry variables (the X1 of D.3)
		XL1i: seq<Variable>, XL2i: seq<Variable>, XL3i: seq<Variable>, XL4i: seq<Variable>, // live-on-entry instances (the XL1i of D.3)
		XL4f: seq<Variable>, XL5f: seq<Variable>, // along with XL1i: live-on-exit instances (the XL2f of D.3)
		Y: seq<Variable>): Statement
{
//	Live(XL3i+XL4f+XL5f+Y,SeqComp(Assignment(XL1i+XL2i+XL3i+XL4i,seqVarToSeqExpr(X1+X2+X3+X4)),IF(B',S1',S2')))
	TransformationD3Right(B',S1',S2',X1+X2+X3+X4,XL1i+XL2i+XL3i+XL4i,XL3i+XL4f+XL5f,Y)
//	Live(XL2f          +Y,SeqComp(Assignment(XL1i               ,seqVarToSeqExpr(X1         )),IF(B',S1',S2')))
}

lemma IfToSSACorrectness(B: BooleanExpression, S1: Statement, S2: Statement, B': BooleanExpression, S1': Statement, S2': Statement,
		X1: seq<Variable>, X2: seq<Variable>, X3: seq<Variable>, X4: seq<Variable>, // live-on-entry variables (the X1 of D.3)
		X5: seq<Variable>, // along with X3,X4: live-on-exit variables (the X2 of D.3)
		XL1i: seq<Variable>, XL2i: seq<Variable>, XL3i: seq<Variable>, XL4i: seq<Variable>, // live-on-entry instances (the XL1i of D.3)
		XL4f: seq<Variable>, XL5f: seq<Variable>, // along with XL1i: live-on-exit instances (the XL2f of D.3)
		Y: seq<Variable>)
	requires Valid(IfToSSACorrectnessLeft(B,S1,S2,X3,X4,X5,XL3i,XL4f,XL5f,Y))
	requires Valid(IfToSSACorrectnessRight(B',S1',S2',X1,X2,X3,X4,XL1i,XL2i,XL3i,XL4i,XL4f,XL5f,Y))
	ensures EquivalentStatments(IfToSSACorrectnessLeft(B,S1,S2,X3,X4,X5,XL3i,XL4f,XL5f,Y),
			IfToSSACorrectnessRight(B',S1',S2',X1,X2,X3,X4,XL1i,XL2i,XL3i,XL4i,XL4f,XL5f,Y))
