include "SliceRefinements.dfy"

//============================================================
//		      *** TEST  ***
//============================================================

// Check if both statement are swap equivalent
method ComputeStatments(s1: string, s2: string) returns (b: bool)  
//ensures b ==> EquivalentStatments(SeqComp(StringToStatement(s1),StringToStatement(s2)),SeqComp(StringToStatement(s2),StringToStatement(s1)))
{
	var S1,S2;
	var valid1,valid2;
	
	S1 := StringToStatement(s1);
	S2 := StringToStatement(s2);
	
	valid1 := isValid(S1);
	valid2 := isValid(S2);

	print "test";
	b:=true;

	if (!valid1) 
	{
		print "Invalid Statment 1\n";
		b:= false;
	}
	if (!valid2) 
	{
		print "Invalid Statment 2\n";
		b:= false;
	}
	if(!(def(S1) !! def(S2)))
	{
		print "def(S1) is not stranger to def(S2)\n";
		b:= false;
	}
	if (!(input(S1) !! def(S2)))
	{
		print "input(S1) is not stranger to def(S2)\n";
		b:= false;
	}
	if(!(def(S1) !! input(S2)))
	{	
		print "def(S1) is not stranger to input(S2)\n";
		b:= false;
	}
	
	
}

method isValid(S: Statement) returns (b: bool)
ensures b == ValidStatement(S)
{
	b:= ValidStatement(S);
}

function method ValidStatement(S: Statement) : bool 
{
	match S {
		case Skip => true
		case Assignment(LHS,RHS) => ValidAssignment(LHS,RHS) 
		case SeqComp(S1,S2) => ValidStatement(S1) && ValidStatement(S2)
		case IF(B0,Sthen,Selse) => 
			/*(forall state: State :: B0.0.requires(state) /*&& B.0(state).Bool?*/) && */
			ValidStatement(Sthen) && ValidStatement(Selse)
		case DO(B,Sloop) =>
			/*(forall state: State :: B.0.requires(state) /*&& B.0(state).Bool?*/) &&*/ ValidStatement(Sloop)
		case LocalDeclaration(L,S0) => ValidStatement(S0)
		case Live(L, S0) => ValidStatement(S0)
		case Assert(B) => true
	}
}

// Convert string to Statement
method StringToStatement(s1: string) returns (s2: Statement)
//ensures valid ==> Valid(s2)
{

	if (|s1| == 0 || |s1| == 1 )
	{
		return Skip;
	}

	var commandType := (s1[0],s1[1]);

	/*
	if (commandType == "SK")
	{
		retrun Skip;
	}

	if (commandType == "AS")
	{
		retrun StringToAssignment(s1[3]);
	}
	*/

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
	if (|sl| > 0)  
	{  
		var i := 0;
		while i < |sl| - 4
		{
			if(sl[i] == 'V' && sl[i+1] == 'A') 
			{
				var str :="";
				var j := i+2;
				while j < |sl| - 1
				{
					if (!(sl[j] == 'V' && sl[j+1] == 'E')) 
					{ 
						var varChar := [sl[j]]; // convert to string == seq<char>
						str := str + varChar;
					}
					else
					{
						j := |sl|;
					}
					j := j + 1;
				}
				var varName := [str]; // convert to seq<Variable> == seq<string>
				LHS := LHS + varName;
			}
			i := i + 1;
		}
	}
	else 
	{
		LHS := [];
	}
}

method StringToRHS(sr: string) returns (RHS: seq<Expression>)
{
	// TODO
}

//============================================================
//		      *** OPERATOR ***
//============================================================

method EqualToBoolExpr(ELeft: Expression,ERight: Expression,Text: string) returns (b: BooleanExpression)
{
	 var func := (state reads * requires ELeft.0.requires(state) && ERight.0.requires(state) => (  match ELeft.0(state) { case Bool(bl) => (match ERight.0(state) { 	case Bool(br) => bl == br
																																												case Int(ir) => false
																																											})
																																  case Int(il) => (match ERight.0(state) {	case Bool(br) => false 
																																											case Int(ir) => il == ir		
																																											})}));
	 var vars := ELeft.1 + ERight.1;
	b := (func,vars ,Text);
}

method GreaterThanToBoolExpr(ELeft: Expression,ERight: Expression,Text: string) returns (b: BooleanExpression)
{
	 var func := (state reads * requires ELeft.0.requires(state) && ERight.0.requires(state) => (var i1 := match ELeft.0(state) { case Bool(b) => 0 case Int(i) => i};var i2 := match ERight.0(state) { case Bool(b) => 0 case Int(i) => i};i1 > i2));
	 var vars := ELeft.1 + ERight.1;
	b := (func,vars ,Text);
}

method GreaterThanOrEqualToBoolExpr(ELeft: Expression,ERight: Expression,Text: string) returns (b: BooleanExpression)
{
	 var func := (state reads * requires ELeft.0.requires(state) && ERight.0.requires(state) => (var i1 := match ELeft.0(state) { case Bool(b) => 0 case Int(i) => i};var i2 := match ERight.0(state) { case Bool(b) => 0 case Int(i) => i};i1 >= i2));
	 var vars := ELeft.1 + ERight.1;
	b := (func,vars ,Text);
}

method LesserThanToBoolExpr(ELeft: Expression,ERight: Expression,Text: string) returns (b: BooleanExpression)
{
	 var func := (state reads * requires ELeft.0.requires(state) && ERight.0.requires(state) => (var i1 := match ELeft.0(state) { case Bool(b) => 0 case Int(i) => i};var i2 := match ERight.0(state) { case Bool(b) => 0 case Int(i) => i};i1 < i2));
	 var vars := ELeft.1 + ERight.1;
	b := (func,vars ,Text);
}

method LesserThanOrEqualToBoolExpr(ELeft: Expression,ERight: Expression,Text: string) returns (b: BooleanExpression)
{
	 var func := (state reads * requires ELeft.0.requires(state) && ERight.0.requires(state) => (var i1 := match ELeft.0(state) { case Bool(b) => 0 case Int(i) => i};var i2 := match ERight.0(state) { case Bool(b) => 0 case Int(i) => i};i1 <= i2));
	 var vars := ELeft.1 + ERight.1;
	b := (func,vars ,Text);
}

method AddToExpr(ELeft: Expression,ERight: Expression,Text: string) returns (e: Expression)
{
	 var func := (state reads * requires ELeft.0.requires(state) && ERight.0.requires(state) => (var i1 := match ELeft.0(state) { case Bool(b) => 0 case Int(i) => i};var i2 := match ERight.0(state) { case Bool(b) => 0 case Int(i) => i};Int(i1 + i2)));
	 var vars := ELeft.1 + ERight.1;
	e := (func,vars ,Text);
}

method SubToExpr(ELeft: Expression,ERight: Expression,Text: string) returns (e: Expression)
{
	 var func := (state reads * requires ELeft.0.requires(state) && ERight.0.requires(state) => (var i1 := match ELeft.0(state) { case Bool(b) => 0 case Int(i) => i};var i2 := match ERight.0(state) { case Bool(b) => 0 case Int(i) => i};Int(i1 - i2)));
	 var vars := ELeft.1 + ERight.1;
	e := (func,vars ,Text);
}

method MulToExpr(ELeft: Expression,ERight: Expression,Text: string) returns (e: Expression)
{
	 var func := (state reads * requires ELeft.0.requires(state) && ERight.0.requires(state) => (var i1 := match ELeft.0(state) { case Bool(b) => 0 case Int(i) => i};var i2 := match ERight.0(state) { case Bool(b) => 0 case Int(i) => i};Int(i1 * i2)));
	 var vars := ELeft.1 + ERight.1;
	e := (func,vars ,Text);
}

method DevToExpr(ELeft: Expression,ERight: Expression,Text: string) returns (e: Expression)
{
	 var func := (state reads * requires ELeft.0.requires(state) && ERight.0.requires(state) => (var i1 := match ELeft.0(state) { case Bool(b) => 0 case Int(i) => i};var i2 := match ERight.0(state) { case Bool(b) => 0 case Int(i) => i};if(i2 == 0) then Int(0) else Int(i1 / i2)));
	 var vars := ELeft.1 + ERight.1;
	e := (func,vars ,Text);
}

method OrToBoolExpr(ELeft: Expression,ERight: Expression,Text: string) returns (b: BooleanExpression)
{
	 var func := (state reads * requires ELeft.0.requires(state) && ERight.0.requires(state) => (var b1 := match ELeft.0(state) { case Bool(b) => b case Int(i) => false};var b2 := match ERight.0(state) { case Bool(b) => b case Int(i) => false};b1 || b2));
	 var vars := ELeft.1 + ERight.1;
	b := (func,vars ,Text);
}

method AndToBoolExpr(ELeft: Expression,ERight: Expression,Text: string) returns (b: BooleanExpression)
{
	 var func := (state reads * requires ELeft.0.requires(state) && ERight.0.requires(state) => (var b1 := match ELeft.0(state) { case Bool(b) => b case Int(i) => false};var b2 := match ERight.0(state) { case Bool(b) => b case Int(i) => false};b1 && b2));
	 var vars := ELeft.1 + ERight.1;
	b := (func,vars ,Text);
}

method NotToBoolExpr(ELeft: Expression,Text: string) returns (b: BooleanExpression)
{
	 var func := (state reads * requires ELeft.0.requires(state) => (var b1 := match ELeft.0(state) { case Bool(b) => b case Int(i) => false};!b1));
	 var vars := ELeft.1;
	b := (func,vars ,Text);
}