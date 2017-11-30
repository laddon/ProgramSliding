include "SliceRefinements.dfy"

//============================================================
//		      *** TEST  ***
//============================================================

// Check if both statement are swap equivalent
method ComputeStatments(s1: string, s2: string) returns (b: bool)  
//ensures b ==> fib(n)
{
	var S1,S2;
	var valid1,valid2;
	
	S1 := StringToStatement(s1);
	S2 := StringToStatement(s2);
	
	valid1 := ValidStatement(S1);
	valid2 := ValidStatement(S2);

	
	if (valid1 && valid2) 
	{
		if ( (def(S1) !! def(S2)) && (input(S1) !! def(S2)) && (def(S1) !! input(S2)))
		{
			return true;
		}
		else 
		{
			return false;
		}
	}
	else
	{
		return false;
	}
	/*
	var S: Statement;
	if (Valid(S) == true)
	{}

	if (true)
	{

	return true;
	} 
	else 
	{
	return false;
	}*/
}


// Convert string to DO Statement
method StringToDo(s1: string) returns (s2: Statement)
//ensures valid ==> Valid(s2)
{
	var sc: string;
	var st: string;

	// TODO: cut the Condition and THEN and ELSE from 's1' into 'sc' and 'st' and 'se'

	var condition:= StringToCondition(sc);
	var do := StringToStatement(st);
	
	s2 := DO(condition,do);
}

method StringToCondition(sc: string) returns (B0: BooleanExpression)
{
	// TODO
}


// Convert string to IF Statement
method StringToIf(s1: string) returns (s2: Statement)
{
	var sc: string;
	var st: string;
	var se: string;

	// TODO: cut the Condition and THEN and ELSE from 's1' into 'sc' and 'st' and 'se'

	var condition:= StringToCondition(sc);
	var sthen := StringToStatement(st);
	var selse := StringToStatement(se);

	s2 := IF(condition,sthen, selse);
}

// Convert string to Assignment Statement
method StringToAssignment(s1: string) returns (s2: Statement)
{
	var sl: string;
	var sr: string;

	// TODO: cut the left and right sides from 's1' into 'sl' and 'sr'

	var left := StringToLHS(sl);
	var right := StringToRHS(sr);

	s2 := Assignment(left, right);
}

method StringToLHS(sl: string) returns (LHS: seq<Variable>)
{
	// TODO
}

method StringToRHS(sr: string) returns (RHS: seq<Expression>)
{
	// TODO
}


method isValid(S: Statement) returns (b: bool)
ensures b == ValidStatement(S)
{
	return ValidStatement(S);
}

function method ValidStatement(S: Statement) : bool 
{
	// TODO: FIX THIS - Need to change valid from predicate into method/function
	//if (Valid(S)) then true else false
	true
}

// Convert string to Statement
method StringToStatement(s1: string) returns (s2: Statement)
//ensures valid ==> Valid(s2)
{


	/*	
		TODO:

		match s1 {
		case "" => Skip
		case ";" => SeqComp(s2, StringToStatement(s1[1]))
		case "IF" => StringToIf(s1[1])
		case "WHILE" => StringToDo(s1[1])
		case "ASM" => StringToAssignment(s1[1])

		}
	*/
}