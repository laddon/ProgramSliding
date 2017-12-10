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
		print "Invalid Statement 1\n";
		b:= false;
	}
	if (!valid2) 
	{
		print "Invalid Statement 2\n";
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
{}

method StringToExpression(sc: string) returns (B0: Expression)
{
	if (|sc| < 3)
	{
		//ERROR
		B0:=StringToExpressionERROR();
	}

	else
	{
	
		// FIND OPERATOR INDEX
		var i:= 0;
		var x := 0;
		var opIndex := -1;
		
		while  i < (|sc|-1)
		{
			if (sc[i] == 'E' && sc[i+1] == 'X')
			{
				x := x + 1;
			}
			else if (sc[i] == 'E' && sc[i+1] == 'E')
			{
				x := x - 1;
			}
			if (( sc[i] == '+' || sc[i] == '-' || sc[i] == '*' || sc[i] == '/' || sc[i] == '>' || sc[i] == '<' || sc[i] == '=') && opIndex < 0 && x == 1)
			{
				opIndex := i;
			}
			i := i +1;
		}
		
		// PARSE THE EXPRESSION
		i := 0;
		x := 0;
		var Bl:Expression;
		var Br:Expression;
		
		while  i < (|sc|-1)
		{
			// If left side is an Expression
			if (sc[i] == 'E' && sc[i+1] == 'X')
			{
				x := x + 1;
				if (x>1)
				{
					var i2 := i + 2;
					var end := false;
			
					while (!end) && (i2 < |sc| - 1)
						invariant  i2 + 1 > i
					{
						if ( sc[i2] == 'E' && sc[i2+1] == 'X')
						{
							x := x + 1;
							i2 := i2 + 1;							
						}
						else if ( sc[i2] == 'E' && sc[i2+1] == 'E')
						{
							x := x - 1; 
							i2 := i2 + 1;
						}
						else if (x == 1)
						{
							i2 := i2 - 3;
							end := true;
						}
				
						i2 := i2 + 1;
					}
					
					if (i2 > |sc| -1 )
					{
						i2 := |sc| -1;
					}
					if (i + 2 < i2)
					{
						Bl := StringToExpression(sc[i+2..i2]);
					}
					else
					{
						// ERROR
						Bl := StringToExpressionERROR();
					}
					
					//Now handle the right side
					while ( i2 < (|sc|-1))
						decreases |sc|-i2+4
					{
						if ( sc[i2] == 'E' && sc[i2+1] == 'X')
						{
							x := x + 1;
							var i3 := i2 + 2;
							var end := false;
					
							while (!end) && (i3 < |sc| - 1)
								invariant  i3 + 1 > i2  
							{
								if ( sc[i3] == 'E' && sc[i3+1] == 'X')
								{
									x := x + 1;
									i3 := i3 + 1;							
								}
								else if ( sc[i3] == 'E' && sc[i3+1] == 'E')
								{
									x := x - 1; 
									i3 := i3 + 1;
								}
								else if (x == 1)
								{
									i3 := i3 - 3;
									end := true;
								}
						
								i3 := i3 + 1;
							}
					
							if (i3 > |sc| -1 )
							{
								i3 := |sc| -1;
							}
							if (i2 + 2 < i3)
							{
								Br := StringToExpression(sc[i2+2..i3]);
							}
							else
							{
								// ERROR
								Br := StringToExpressionERROR();
							}
							
							// Move the index Forward
							i2:= i3;
						}
						else if ( sc[i2] == 'V' && sc[i2+1] == 'A')
						{
							var name := "";
							var k:= i2 + 3;
							var end:= false;
							while (!end) && k < (|sc|-1)
								invariant k>i2
							{
								if ( sc[k] == 'V' && sc[k+1] == 'E')
								{
									end := true;
								}
								else
								{
									name := name + [sc[k]];
								}
								k := k + 1;
							}
							Br := StringToExpressionVA(name);
							assert k+2>i2;
							i2 := k + 2;
						}
						else if ( sc[i2] == 'V' && sc[i2+1] == 'N')
						{
							var name := "";
							var k:= i2 + 3;
							var end:= false;
							while (!end) && k < (|sc|-1)
								invariant k>i2
							{
								if ( sc[k] == 'V' && sc[k+1] == 'E')
								{
									end := true;
								}
								else
								{
									name := name + [sc[k]];
								}
								k := k + 1;
							}
							Br := StringToExpressionVN(name);
							assert k+2>i2;
							i2 := k + 2;
						}
																	
						i2 := i2 + 1;
					}
				
					// Move the index Forward
					i:= i2;				
				}
			}
			
			// If left side is variable
			else if ( sc[i] == 'V' && sc[i+1] == 'A')
			{
				var name := "";
				var j:= i + 3;
				var end:= false;
				
				while (!end) && j < (|sc|-1)
				{
					if ( sc[j] == 'V' && sc[j+1] == 'E')
					{
						end := true;
					}
					else
					{
						name := name + [sc[j]];
					}
					j := j + 1;
				}
				Bl:= StringToExpressionVA(name);
				var i2 := j + 2;
				
				// Now parse the right side
				while ( i2 < (|sc|-1))
					decreases |sc|-i2+4
				{
					if ( sc[i2] == 'E' && sc[i2+1] == 'X')
					{
						x := x + 1;
						var i3 := i2 + 2;
						var end := false;
				
						while (!end) && (i3 < |sc| - 1)
							invariant  i3 + 1 > i2  
						{
							if ( sc[i3] == 'E' && sc[i3+1] == 'X')
							{
								x := x + 1;
								i3 := i3 + 1;							
							}
							else if ( sc[i3] == 'E' && sc[i3+1] == 'E')
							{
								x := x - 1; 
								i3 := i3 + 1;
							}
							else if (x == 1)
							{
								i3 := i3 - 3;
								end := true;
							}
					
							i3 := i3 + 1;
						}
				
						if (i3 > |sc| -1 )
						{
							i3 := |sc| -1;
						}
						if (i2 + 2 < i3)
						{
							Br := StringToExpression(sc[i2+2..i3]);
						}
						else
						{
							// ERROR
							Br := StringToExpressionERROR();
						}
						
						// Move the index Forward
						i2:= i3;
					}
					else if ( sc[i2] == 'V' && sc[i2+1] == 'A')
					{
						var name := "";
						var k:= i2 + 3;
						var end:= false;
						while (!end) && k < (|sc|-1)
							invariant k>i2
						{
							if ( sc[k] == 'V' && sc[k+1] == 'E')
							{
								end := true;
							}
							else
							{
								name := name + [sc[k]];
							}
							k := k + 1;
						}
						Br := StringToExpressionVA(name);
						assert k+2>i2;
						i2 := k + 2;
					}
					else if ( sc[i2] == 'V' && sc[i2+1] == 'N')
					{
						var name := "";
						var k:= i2 + 3;
						var end:= false;
						while (!end) && k < (|sc|-1)
							invariant k>i2
						{
							if ( sc[k] == 'V' && sc[k+1] == 'E')
							{
								end := true;
							}
							else
							{
								name := name + [sc[k]];
							}
							k := k + 1;
						}
						Br := StringToExpressionVN(name);
						assert k+2>i2;
						i2 := k + 2;
					}
					
					/* FOR "BE" ONLY
					else if ( sc[i2] == 'V' && sc[i2+1] == 'T')
					{
						var name := "";
						var k:= i2 + 3;
						var end:= false;
						while (!end) && k < (|sc|-1)
							invariant k>i2
						{
							if ( sc[k] == 'V' && sc[k+1] == 'E')
							{
								end := true;
							}
							else
							{
								name := name + [sc[k]];
							}
							k := k + 1;
						}
					
						if (name == "TRUE" || name == "true")
						{
							Br := StringToExpressionVT(name,true);
						}
						else
						{
							Br := StringToExpressionVT(name,false);
						}
					
						assert k+2>i2;
						i2 := k + 2;
					}
					*/
					
					i2 := i2 + 1;
				}
				
				//Move the Index Forward
				i := i2;		
			}
			
			// If left side is number
			else if (sc[i] == 'V' && sc[i+1] == 'N')
			{
				var name := "";
				var i2:= i + 3;
				var end:= false;
				while (!end) && i2 < (|sc|-1)
					invariant i2>i
				{
					if ( sc[i2] == 'V' && sc[i2+1] == 'E')
					{
						end := true;
					}
					else
					{
						name := name + [sc[i2]];
					}
					i2 := i2 + 1;
				}
				Bl := StringToExpressionVN(name);
				assert i2+2>i;
				i := i2 + 2;
				i2 := i;
				
				// Now parse the right side
				while ( i2 < (|sc|-1))
					decreases |sc|-i2+4
				{
					if ( sc[i2] == 'E' && sc[i2+1] == 'X')
					{
						x := x + 1;
						var i3 := i2 + 2;
						var end := false;
				
						while (!end) && (i3 < |sc| - 1)
							invariant  i3 + 1 > i2  
						{
							if ( sc[i3] == 'E' && sc[i3+1] == 'X')
							{
								x := x + 1;
								i3 := i3 + 1;							
							}
							else if ( sc[i3] == 'E' && sc[i3+1] == 'E')
							{
								x := x - 1; 
								i3 := i3 + 1;
							}
							else if (x == 1)
							{
								i3 := i3 - 3;
								end := true;
							}
					
							i3 := i3 + 1;
						}
				
						if (i3 > |sc| -1 )
						{
							i3 := |sc| -1;
						}
						if (i2 + 2 < i3)
						{
							Br := StringToExpression(sc[i2+2..i3]);
						}
						else
						{
							// ERROR
							Br := StringToExpressionERROR();
						}
						
						// Move the index Forward
						i2:= i3;
					}
					else if ( sc[i2] == 'V' && sc[i2+1] == 'A')
					{
						var name := "";
						var k:= i2 + 3;
						var end:= false;
						while (!end) && k < (|sc|-1)
							invariant k>i2
						{
							if ( sc[k] == 'V' && sc[k+1] == 'E')
							{
								end := true;
							}
							else
							{
								name := name + [sc[k]];
							}
							k := k + 1;
						}
						Br := StringToExpressionVA(name);
						assert k+2>i2;
						i2 := k + 2;
					}
					else if ( sc[i2] == 'V' && sc[i2+1] == 'N')
					{
						var name := "";
						var k:= i2 + 3;
						var end:= false;
						while (!end) && k < (|sc|-1)
							invariant k>i2
						{
							if ( sc[k] == 'V' && sc[k+1] == 'E')
							{
								end := true;
							}
							else
							{
								name := name + [sc[k]];
							}
							k := k + 1;
						}
						Br := StringToExpressionVN(name);
						assert k+2>i2;
						i2 := k + 2;
					}
					
					/* FOR "BE" ONLY
					else if ( sc[i2] == 'V' && sc[i2+1] == 'T')
					{
						var name := "";
						var k:= i2 + 3;
						var end:= false;
						while (!end) && k < (|sc|-1)
							invariant k>i2
						{
							if ( sc[k] == 'V' && sc[k+1] == 'E')
							{
								end := true;
							}
							else
							{
								name := name + [sc[k]];
							}
							k := k + 1;
						}
					
						if (name == "TRUE" || name == "true")
						{
							Br := StringToExpressionVT(name,true);
						}
						else
						{
							Br := StringToExpressionVT(name,false);
						}
					
						assert k+2>i2;
						i2 := k + 2;
					}
					*/
					
					i2 := i2 + 1;
				}
				
				//Move the Index Forward
				i := i2;		
			}
			
			i := i+1;
		}
		
		// Building the Expression
		if (0 < opIndex < |sc|)
		{
			if ( sc[opIndex] == '+')
			{
				B0 := AddToExpr(Bl,Br,Bl.2+['+']+Br.2);
			}
			else if (sc[opIndex] == '-')
			{
				B0 := SubToExpr(Bl,Br,Bl.2+['-']+Br.2);
			}
			else if (sc[opIndex] == '*')
			{
				B0 := MulToExpr(Bl,Br,Bl.2+['*']+Br.2);
			}
			else if (sc[opIndex] == '/')
			{
				B0 := DevToExpr(Bl,Br,Bl.2+['/']+Br.2);
			}
			else 
			{
				//ERROR
				B0 := StringToExpressionERROR();
			}
		}
		else 
		{
			//ERROR
			B0 := StringToExpressionERROR();
		}
	}
}

method StringToBooleanExpression(sc: string) returns (B0: BooleanExpression)
{
	if (|sc| < 3)
	{
		//ERROR
		B0:=StringToBooleanExpressionERROR();
	}

	else
	{
	
		// FIND OPERATOR INDEX
		var i:= 0;
		var x := 0;
		var opIndex := -1;
		
		while  i < (|sc|-1)
		{
			if (sc[i] == 'E' && sc[i+1] == 'X')
			{
				x := x + 1;
			}
			else if (sc[i] == 'E' && sc[i+1] == 'E')
			{
				x := x - 1;
			}
			if (( sc[i] == '>' || sc[i] == '<' || sc[i] == '=' || sc[i] == '&' || sc[i] == '|' ) && opIndex < 0 && x == 1)
			{
				opIndex := i;
			}
			i := i +1;
		}
		
		// PARSE THE EXPRESSION
		i := 0;
		x := 0;
		var Bl:Expression;
		var Br:Expression;
		var Blb:BooleanExpression;
		var Brb:BooleanExpression;
		
		while  i < (|sc|-1)
		{
			// If left side is an Expression
			if (sc[i] == 'E' && sc[i+1] == 'X')
			{
				x := x + 1;
				if (x>1)
				{
					var i2 := i + 2;
					var end := false;
			
					while (!end) && (i2 < |sc| - 1)
						invariant  i2 + 1 > i
					{
						if ( sc[i2] == 'E' && sc[i2+1] == 'X')
						{
							x := x + 1;
							i2 := i2 + 1;							
						}
						else if ( sc[i2] == 'E' && sc[i2+1] == 'E')
						{
							x := x - 1; 
							i2 := i2 + 1;
						}
						else if (x == 1)
						{
							i2 := i2 - 3;
							end := true;
						}
				
						i2 := i2 + 1;
					}
					
					if (i2 > |sc| -1 )
					{
						i2 := |sc| -1;
					}
					if (i + 2 < i2)
					{
						Bl := StringToExpression(sc[i+2..i2]);
					}
					else
					{
						// ERROR
						Bl := StringToExpressionERROR();
					}
					
					//Now handle the right side
					while ( i2 < (|sc|-1))
						decreases |sc|-i2+4
					{
						if ( sc[i2] == 'E' && sc[i2+1] == 'X')
						{
							x := x + 1;
							var i3 := i2 + 2;
							var end := false;
					
							while (!end) && (i3 < |sc| - 1)
								invariant  i3 + 1 > i2  
							{
								if ( sc[i3] == 'E' && sc[i3+1] == 'X')
								{
									x := x + 1;
									i3 := i3 + 1;							
								}
								else if ( sc[i3] == 'E' && sc[i3+1] == 'E')
								{
									x := x - 1; 
									i3 := i3 + 1;
								}
								else if (x == 1)
								{
									i3 := i3 - 3;
									end := true;
								}
						
								i3 := i3 + 1;
							}
					
							if (i3 > |sc| -1 )
							{
								i3 := |sc| -1;
							}
							if (i2 + 2 < i3)
							{
								Br := StringToExpression(sc[i2+2..i3]);
							}
							else
							{
								// ERROR
								Br := StringToExpressionERROR();
							}
							
							// Move the index Forward
							i2:= i3;
						}
						else if ( sc[i2] == 'V' && sc[i2+1] == 'A')
						{
							var name := "";
							var k:= i2 + 3;
							var end:= false;
							while (!end) && k < (|sc|-1)
								invariant k>i2
							{
								if ( sc[k] == 'V' && sc[k+1] == 'E')
								{
									end := true;
								}
								else
								{
									name := name + [sc[k]];
								}
								k := k + 1;
							}
							Br := StringToExpressionVA(name);
							assert k+2>i2;
							i2 := k + 2;
						}
						else if ( sc[i2] == 'V' && sc[i2+1] == 'N')
						{
							var name := "";
							var k:= i2 + 3;
							var end:= false;
							while (!end) && k < (|sc|-1)
								invariant k>i2
							{
								if ( sc[k] == 'V' && sc[k+1] == 'E')
								{
									end := true;
								}
								else
								{
									name := name + [sc[k]];
								}
								k := k + 1;
							}
							Br := StringToExpressionVN(name);
							assert k+2>i2;
							i2 := k + 2;
						}
						// FOR "BE" ONLY
						else if ( sc[i2] == 'V' && sc[i2+1] == 'T')
						{
							var name := "";
							var k:= i2 + 3;
							var end:= false;
							while (!end) && k < (|sc|-1)
								invariant k>i2
							{
								if ( sc[k] == 'V' && sc[k+1] == 'E')
								{
									end := true;
								}
								else
								{
									name := name + [sc[k]];
								}
								k := k + 1;
							}
						
							if (name == "TRUE" || name == "true")
							{
								Brb := StringToExpressionVT(name,true);
							}
							else
							{
								Brb := StringToExpressionVT(name,false);
							}
						
							assert k+2>i2;
							i2 := k + 2;
						}	
						
						i2 := i2 + 1;
					}
										
					// Move the index Forward
					i:= i2;				
				}
			}
			
			// If left side is variable
			else if ( sc[i] == 'V' && sc[i+1] == 'A')
			{
				var name := "";
				var j:= i + 3;
				var end:= false;
				
				while (!end) && j < (|sc|-1)
				{
					if ( sc[j] == 'V' && sc[j+1] == 'E')
					{
						end := true;
					}
					else
					{
						name := name + [sc[j]];
					}
					j := j + 1;
				}
				Bl:= StringToExpressionVA(name);
				var i2 := j + 2;
				
				// Now parse the right side
				while ( i2 < (|sc|-1))
					decreases |sc|-i2+4
				{
					if ( sc[i2] == 'E' && sc[i2+1] == 'X')
					{
						x := x + 1;
						var i3 := i2 + 2;
						var end := false;
				
						while (!end) && (i3 < |sc| - 1)
							invariant  i3 + 1 > i2  
						{
							if ( sc[i3] == 'E' && sc[i3+1] == 'X')
							{
								x := x + 1;
								i3 := i3 + 1;							
							}
							else if ( sc[i3] == 'E' && sc[i3+1] == 'E')
							{
								x := x - 1; 
								i3 := i3 + 1;
							}
							else if (x == 1)
							{
								i3 := i3 - 3;
								end := true;
							}
					
							i3 := i3 + 1;
						}
				
						if (i3 > |sc| -1 )
						{
							i3 := |sc| -1;
						}
						if (i2 + 2 < i3)
						{
							Br := StringToExpression(sc[i2+2..i3]);
						}
						else
						{
							// ERROR
							Br := StringToExpressionERROR();
						}
						
						// Move the index Forward
						i2:= i3;
					}
					else if ( sc[i2] == 'V' && sc[i2+1] == 'A')
					{
						var name := "";
						var k:= i2 + 3;
						var end:= false;
						while (!end) && k < (|sc|-1)
							invariant k>i2
						{
							if ( sc[k] == 'V' && sc[k+1] == 'E')
							{
								end := true;
							}
							else
							{
								name := name + [sc[k]];
							}
							k := k + 1;
						}
						Br := StringToExpressionVA(name);
						assert k+2>i2;
						i2 := k + 2;
					}
					else if ( sc[i2] == 'V' && sc[i2+1] == 'N')
					{
						var name := "";
						var k:= i2 + 3;
						var end:= false;
						while (!end) && k < (|sc|-1)
							invariant k>i2
						{
							if ( sc[k] == 'V' && sc[k+1] == 'E')
							{
								end := true;
							}
							else
							{
								name := name + [sc[k]];
							}
							k := k + 1;
						}
						Br := StringToExpressionVN(name);
						assert k+2>i2;
						i2 := k + 2;
					}
					
					// FOR "BE" ONLY
					else if ( sc[i2] == 'V' && sc[i2+1] == 'T')
					{
						var name := "";
						var k:= i2 + 3;
						var end:= false;
						while (!end) && k < (|sc|-1)
							invariant k>i2
						{
							if ( sc[k] == 'V' && sc[k+1] == 'E')
							{
								end := true;
							}
							else
							{
								name := name + [sc[k]];
							}
							k := k + 1;
						}
					
						if (name == "TRUE" || name == "true")
						{
							Brb := StringToExpressionVT(name,true);
						}
						else
						{
							Brb := StringToExpressionVT(name,false);
						}
					
						assert k+2>i2;
						i2 := k + 2;
					}
					
					
					i2 := i2 + 1;
				}
				
				//Move the Index Forward
				i := i2;		
			}
			
			// If left side is number
			else if (sc[i] == 'V' && sc[i+1] == 'N')
			{
				var name := "";
				var i2:= i + 3;
				var end:= false;
				while (!end) && i2 < (|sc|-1)
					invariant i2>i
				{
					if ( sc[i2] == 'V' && sc[i2+1] == 'E')
					{
						end := true;
					}
					else
					{
						name := name + [sc[i2]];
					}
					i2 := i2 + 1;
				}
				Bl := StringToExpressionVN(name);
				assert i2+2>i;
				i := i2 + 2;
				i2 := i;
				
				// Now parse the right side
				while ( i2 < (|sc|-1))
					decreases |sc|-i2+4
				{
					if ( sc[i2] == 'E' && sc[i2+1] == 'X')
					{
						x := x + 1;
						var i3 := i2 + 2;
						var end := false;
				
						while (!end) && (i3 < |sc| - 1)
							invariant  i3 + 1 > i2  
						{
							if ( sc[i3] == 'E' && sc[i3+1] == 'X')
							{
								x := x + 1;
								i3 := i3 + 1;							
							}
							else if ( sc[i3] == 'E' && sc[i3+1] == 'E')
							{
								x := x - 1; 
								i3 := i3 + 1;
							}
							else if (x == 1)
							{
								i3 := i3 - 3;
								end := true;
							}
					
							i3 := i3 + 1;
						}
				
						if (i3 > |sc| -1 )
						{
							i3 := |sc| -1;
						}
						if (i2 + 2 < i3)
						{
							Br := StringToExpression(sc[i2+2..i3]);
						}
						else
						{
							// ERROR
							Br := StringToExpressionERROR();
						}
						
						// Move the index Forward
						i2:= i3;
					}
					else if ( sc[i2] == 'V' && sc[i2+1] == 'A')
					{
						var name := "";
						var k:= i2 + 3;
						var end:= false;
						while (!end) && k < (|sc|-1)
							invariant k>i2
						{
							if ( sc[k] == 'V' && sc[k+1] == 'E')
							{
								end := true;
							}
							else
							{
								name := name + [sc[k]];
							}
							k := k + 1;
						}
						Br := StringToExpressionVA(name);
						assert k+2>i2;
						i2 := k + 2;
					}
					else if ( sc[i2] == 'V' && sc[i2+1] == 'N')
					{
						var name := "";
						var k:= i2 + 3;
						var end:= false;
						while (!end) && k < (|sc|-1)
							invariant k>i2
						{
							if ( sc[k] == 'V' && sc[k+1] == 'E')
							{
								end := true;
							}
							else
							{
								name := name + [sc[k]];
							}
							k := k + 1;
						}
						Br := StringToExpressionVN(name);
						assert k+2>i2;
						i2 := k + 2;
					}
					
					// FOR "BE" ONLY
					else if ( sc[i2] == 'V' && sc[i2+1] == 'T')
					{
						var name := "";
						var k:= i2 + 3;
						var end:= false;
						while (!end) && k < (|sc|-1)
							invariant k>i2
						{
							if ( sc[k] == 'V' && sc[k+1] == 'E')
							{
								end := true;
							}
							else
							{
								name := name + [sc[k]];
							}
							k := k + 1;
						}
					
						if (name == "TRUE" || name == "true")
						{
							Brb := StringToExpressionVT(name,true);
						}
						else
						{
							Brb := StringToExpressionVT(name,false);
						}
					
						assert k+2>i2;
						i2 := k + 2;
					}
					
					
					i2 := i2 + 1;
				}
				
				//Move the Index Forward
				i := i2;		
			}
			
			i := i+1;
		}
		
		// Building the Expression
		if (0 < opIndex < |sc| - 1)
		{
			if ( sc[opIndex] == '>')
			{
				if(sc[opIndex + 1] == '=')
				{
					B0 := GreaterThanOrEqualToBoolExpr(Bl,Br,Bl.2+">="+Br.2);
				}
				else
				{
					B0 := GreaterThanToBoolExpr(Bl,Br,Bl.2+">"+Br.2);
				}
			}
			else if ( sc[opIndex] == '<')
			{
				if(sc[opIndex + 1] == '=')
				{
					B0 := LesserThanOrEqualToBoolExpr(Bl,Br,Bl.2+"<="+Br.2);
				}
				else
				{
					B0 := LesserThanToBoolExpr(Bl,Br,Bl.2+"<"+Br.2);
				}
			}
			else if ( sc[opIndex] == '=')
			{
				if(sc[opIndex + 1] == '=')
				{
					// It can also be Brb / Blb TODO
					B0 := EqualToBoolExpr(Bl,Br,Bl.2+"=="+Br.2);
				}
				else if (sc[opIndex + 1] == '>')
				{
					B0 := EqualToBoolExpr(Bl,Br,Bl.2+"=="+Br.2);
				}
				else
				{
					//ERROR
					B0 := StringToBooleanExpressionERROR();
				}
			}
			else if ( sc[opIndex] == '&')
			{
				if(sc[opIndex + 1] == '&')
				{
					B0 := ANDToBoolExpr(Blb,Brb,Blb.2+"=="+Brb.2);
				}
				else
				{
					//ERROR
					B0 := StringToBooleanExpressionERROR();
				}
			}
			else if ( sc[opIndex] == '|')
			{
				if(sc[opIndex + 1] == '|')
				{
					B0 := ORToBoolExpr(Blb,Brb,Blb.2+"=="+Brb.2);
				}
				else
				{
					//ERROR
					B0 := StringToBooleanExpressionERROR();
				}
			}
			else 
			{
				//ERROR
				B0 := StringToBooleanExpressionERROR();
			}
		}
		else 
		{
			//ERROR
			B0 := StringToBooleanExpressionERROR();
		}
	}
}

method StringToBooleanExpressionERROR() returns (B0: BooleanExpression)
{
	var Vars := {};
	var func :=  (state reads *  => false);
	B0 := (func,Vars,"false");
}

method StringToExpressionERROR() returns (B0: Expression)
{
	var Vars := {};
	var func :=  (state reads *  => Int(0));
	B0 := (func,Vars,"0");
}

method StringToExpressionVT(sc: string,val: bool) returns (B0: BooleanExpression)
{
	var Vars := {};
	var func :=  (state reads *  => val);
	
	B0 := (func,Vars,sc);
}

method StringToExpressionVA(sc: string) returns (B0: Expression)
{
	var Vars := {sc};
	var func :=  (state reads * requires sc in state => state[sc]);
	B0 := (func,Vars,sc);
}

method StringToExpressionVN(sc: string) returns (B0: Expression)
{
	var j := 0;
	var number;
	while  j < (|sc|)
	{	
		if (sc[j] == '0' )
		{
			number := number*10 + 0;
		}
		if (sc[j] == '1' )
		{
			number := number*10 + 1;
		}
		if (sc[j] == '2' )
		{
			number := number*10 + 2;
		}
		if (sc[j] == '3' )
		{
			number := number*10 + 3;
		}
		if (sc[j] == '4' )
		{
			number := number*10 + 4;
		}
		if (sc[j] == '5' )
		{
			number := number*10 + 5;
		}
		if (sc[j] == '6' )
		{
			number := number*10 + 6;
		}
		if (sc[j] == '7' )
		{
			number := number*10 + 7;
		}
		if (sc[j] == '8' )
		{
			number := number*10 + 8;
		}
		if (sc[j] == '9' )
		{
			number := number*10 + 9;
		}
		j := j + 1;
	}
	var Vars := {};
	var func :=  (state reads *  => Int(number));
	
	B0 := (func,Vars,sc);
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

method ORToBoolExpr(ELeft: BooleanExpression,ERight: BooleanExpression,Text: string) returns (b: BooleanExpression)
{
	 var func := (state reads * requires ELeft.0.requires(state) && ERight.0.requires(state) => (ELeft.0(state) || ERight.0(state)));
	 var vars := ELeft.1 + ERight.1;
	b := (func,vars ,Text);
}

method ANDToBoolExpr(ELeft: BooleanExpression,ERight: BooleanExpression,Text: string) returns (b: BooleanExpression)
{
	 var func := (state reads * requires ELeft.0.requires(state) && ERight.0.requires(state) => (ELeft.0(state) && ERight.0(state)));
	 var vars := ELeft.1 + ERight.1;
	b := (func,vars ,Text);
}