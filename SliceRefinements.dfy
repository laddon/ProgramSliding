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

}

// pretty printing...
function method ToString(S: Statement) : string
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


function method PredicateFromString(str: string): Predicate
{
	((state: map<Variable, Value>) => true,{})
}

predicate method ValidAssignment(str: string)
{
	true // check ":=" with same-length lists to its left and right, the former of distinct variable names and the right of expressions
}


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

//============================================================
//					*** Definitions ***
//============================================================

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

//============================================================
//					*** Predicate Operators ***
//============================================================
function PointwisePredicate(s: State, v: Variable) : Predicate
{
	(((s1: State) reads*  => v in s1 && v in s && s[v] == s1[v] ,{v}))
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
ensures EquivalentPredicates(P,(((s1: State) reads * requires P.0.requires(s1) => exists p: State :: P.0.requires(p) && P.0(p) && forall v: Variable :: v in V ==> v in s1 && v in p && p[v] == s1[v]), P.1))

lemma Equation_5_2(S: Statement, Sco: Statement, V: set<Variable>)
requires Valid(S)
requires Valid(Sco)
ensures (forall s: State, v: Variable :: v in V && v in s ==> (wp(S,PointwisePredicate(s,v)).0(s) ==> wp(Sco,PointwisePredicate(s,v)).0(s)))

//============================================================
//					*** RE1-RE5 ***
//============================================================
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

lemma RE2( S: Statement,P: Predicate)
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

lemma RE3( S: Statement,P: Predicate)
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
			== {} 
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
 


//============================================================
//					*** THEOREMS ***
//============================================================

lemma AbsorptionOfTermination3_14(P: Predicate,S: Statement)
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

lemma Theorem_4_1(S: Statement, T: Statement) 
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

// TODO: complete 1 err
lemma {:verify false} Lemma_4_2(S: Statement, T: Statement)
requires Valid(S)
requires Valid(T)
ensures  (forall P: Predicate, s: State :: wp(S,P).0(s) == wp(T,P).0(s)) <==> (forall P: Predicate, s:State :: (wp(S,P).0(s) ==> wp(T,P).0(s)) && (EquivalentPredicates(wp(S,ConstantPredicate(true)),wp(T,ConstantPredicate(true)))))
{
	calc 
	{
		(forall P: Predicate, s: State :: wp(S,P).0(s) == wp(T,P).0(s));
		== {Lemma_4_2_Left(S,T);Lemma_4_2_Right(S,T);}
		((forall P: Predicate, s:State :: (wp(S,P).0(s) ==> wp(T,P).0(s)) && (EquivalentPredicates(wp(S,ConstantPredicate(true)),wp(T,ConstantPredicate(true))))));
	}
}

lemma Lemma_4_2_Left(S: Statement, T: Statement)
requires Valid(S)
requires Valid(T)
ensures  (forall P: Predicate, s: State :: wp(S,P).0(s) == wp(T,P).0(s)) ==> (forall P: Predicate, s:State :: (wp(S,P).0(s) ==> wp(T,P).0(s)) && (EquivalentPredicates(wp(S,ConstantPredicate(true)),wp(T,ConstantPredicate(true)))))
{
	calc 
	{
		(forall P: Predicate, s: State :: wp(S,P).0(s) == wp(T,P).0(s));
		==> {}
		((forall P: Predicate, s:State :: (wp(S,P).0(s) ==> wp(T,P).0(s)) && (EquivalentPredicates(wp(S,ConstantPredicate(true)),wp(T,ConstantPredicate(true))))));
	}
}

lemma {:verify false} Lemma_4_2_Right(S: Statement, T: Statement)
requires Valid(S)
requires Valid(T)
ensures  (forall P: Predicate, s: State :: wp(S,P).0(s) == wp(T,P).0(s)) <== (forall P: Predicate, s:State :: (wp(S,P).0(s) ==> wp(T,P).0(s)) && (EquivalentPredicates(wp(S,ConstantPredicate(true)),wp(T,ConstantPredicate(true)))))
{
	forall s: State, P : Predicate
	{
		calc {
		wp(S,P).0(s);
		== {}
		// definition of wlp

		}
	}
}

lemma {:verify true} Lemma_4_2inV(S: Statement, T: Statement, V: set<Variable>)
requires Valid(S)
requires Valid(T)
ensures (forall P: Predicate, s:State :: vars(P) <= V ==> ((wp(S,P).0(s) ==> wp(T,P).0(s)) && (EquivalentPredicates(wp(S,ConstantPredicate(true)),wp(T,ConstantPredicate(true)))))) <==> (forall P: Predicate, s: State :: wp(S,P).0(s) == wp(T,P).0(s))

lemma {:verify true} Lemma_4_2StrangerV(S: Statement, T: Statement, V: set<Variable>)
requires Valid(S)
requires Valid(T)
ensures (forall P: Predicate, s:State :: vars(P) !! V ==> ((wp(S,P).0(s) ==> wp(T,P).0(s)) && (EquivalentPredicates(wp(S,ConstantPredicate(true)),wp(T,ConstantPredicate(true)))))) <==> (forall P: Predicate, s: State :: wp(S,P).0(s) == wp(T,P).0(s))


predicate dummy7(S: Statement, SV: Statement, V: set<Variable>)
reads *
requires Valid(S)
requires Valid(SV)
{
	(forall s: State :: ((wp(S,ConstantPredicate(true)).0(s) ==> wp(SV,ConstantPredicate(true)).0(s)))) && (forall s: State, v: Variable :: v in V && v in s ==> (wp(S,PointwisePredicate(s,v)).0(s) ==> wp(SV,PointwisePredicate(s,v)).0(s)))
}

lemma dummy7Lemma(S: Statement, SV: Statement, V: set<Variable>)
requires Valid(S)
requires Valid(SV)
ensures dummy7(S,SV,V) <==> (forall s: State :: ((wp(S,ConstantPredicate(true)).0(s) ==> wp(SV,ConstantPredicate(true)).0(s)))) && (forall s: State, v: Variable :: v in V && v in s ==> (wp(S,PointwisePredicate(s,v)).0(s) ==> wp(SV,PointwisePredicate(s,v)).0(s)))


lemma Theorem_5_1 (S: Statement, SV: Statement, V: set<Variable>)
requires Valid(S)
requires Valid(SV)
ensures SliceRefinement(S,SV,V) <==> dummy7(S,SV,V)
{
	calc
	{
	SliceRefinement(S,SV,V);
	== {Theorem_5_1Left(S,SV,V); Theorem_5_1Right(S,SV,V);}
	dummy7(S,SV,V);
	}
}

/*TODO: Complete*/
lemma {:verify false} Theorem_5_1Left (S: Statement, SV: Statement, V: set<Variable>)
requires Valid(S)
requires Valid(SV)
ensures SliceRefinement(S,SV,V) ==> dummy7(S,SV,V)
{
	calc {
	
	//== {}

	}
}

/*TODO : Complete 2 err*/
/*break into V is empty and V isnot empty */
/*add EMPTY type to V in order to use match+case */
lemma {:verify false} Theorem_5_1Right (S: Statement, SV: Statement, V: set<Variable>)
requires Valid(S)
requires Valid(SV)
ensures SliceRefinement(S,SV,V) <== dummy7(S,SV,V)
{
	/*match V {
		case EMPTY => true
		case set<Variable> => { 
		*/
	forall s: State,P: Predicate | vars(P) <= V 
	{
		var P1 := (((s1: State) reads * requires P.0.requires(s1) => exists p: State :: P.0.requires(p) && P.0(p) && forall v: Variable :: v in V ==> v in s1 && v in p && p[v] == s1[v]), P.1);
		var P2 := (p: State) => (((s0:State)=>(forall v: Variable :: v in V ==> v in s0 && v in p && s0[v] == p[v])),P.1);
		var P3 := (((s1: State) reads * requires P.0.requires(s1)=> exists p: State :: P.0.requires(p) && P.0(p) && wp.requires(S,P2(p)) && (wp(S,P2(p)).0(s1))),P.1);
		var P4 := (((s2: State) reads * requires P.0.requires(s2)=> exists p1: State :: P.0.requires(p1) && P.0(p1) && wp.requires(SV,P2(p1)) && (wp(SV,P2(p1)).0(s2))),P.1);
		calc{
		wp(S,P).0(s);
		==> {Equation_5_1(P,V);assert EquivalentPredicates(P,P1);Leibniz2(wp,P,P1,S);}
		wp(S,P1).0(s);
		==> {}
		wp(S,(((s1: State) reads * requires P.0.requires(s1) => exists p: State :: P.0.requires(p) && P.0(p) && forall v: Variable :: v in V ==> v in s1 && v in p && p[v] == s1[v]), P.1)).0(s);
		==> {assert forall s1: State, p: State :: (forall v: Variable :: v in V ==> v in s1 && v in p && p[v] == s1[v]) == (P2(p).0(s1));
			var P4 := (((s1: State) reads * requires P.0.requires(s1) => exists p: State :: P.0.requires(p) && P.0(p) && forall v: Variable :: v in V ==> v in s1 && v in p && p[v] == s1[v]), P.1); 
			var P5 := (((s1: State) reads * requires P.0.requires(s1) => exists p: State :: P.0.requires(p) && P.0(p) && P2(p).0(s1)), P.1);
			assert EquivalentPredicates(P4,P5);
			Leibniz2(wp, P4,P5, S);}
		wp(S,(((s1: State) reads * requires P.0.requires(s1) => exists p: State :: P.0.requires(p) && P.0(p) && P2(p).0(s1)), P.1)).0(s);
		==> { assume EquivalentPredicates(wp(S,(((s1: State) reads * requires P.0.requires(s1) => exists p: State :: P.0.requires(p) && P.0(p) && P2(p).0(s1)), P.1)),P3) /*by { RE1(S,{P/*2(p)*/});}*/;} 
		//(((s1: State) reads * requires P.0.requires(s1) => exists p: State :: P.0.requires(p) && P.0(p) && wp.requires(S,P2(p)) && (wp(S,P2(p)).0(s1))), P.1).0(s);
		//=={}                                                                                              
		P3.0(s);
		/*==> {/*assume EquivalentPredicates(wp(S,(((s1: State) reads * requires P.0.requires(s1) => exists p: State :: P.0.requires(p) && P.0(p) && P2(p).0(s1)), P.1)),P3);*/}
		((s1: State) reads * requires P.0.requires(s1)=>exists p: State :: P.0.requires(p) && P.0(p) && wp.requires(S,P2(p)) && wp(S,((s0:State)=>(forall v: Variable :: v in V ==> v in s0 && v in p && s0[v] == p[v]),P.1)).0(s1),P.1).0(s);
		*/==> {Equation_5_2(S,SV,V);/*leibniz3 - forall ==>*/}
		P4.0(s);
		==> {assume EquivalentPredicates(wp(SV,(((s1: State) reads * requires P.0.requires(s1) => exists p: State :: P.0.requires(p) && P.0(p) && P2(p).0(s1)), P.1)),P4) /*by { RE1(S,{P/*2(p)*/});}*/;} 
		wp(SV,(((s1: State) reads * requires P.0.requires(s1) => exists p: State :: P.0.requires(p) && P.0(p) && P2(p).0(s1)), P.1)).0(s);
		==> {assert forall s1: State, p: State :: (forall v: Variable :: v in V ==> v in s1 && v in p && p[v] == s1[v]) == (P2(p).0(s1));
			var P6 := (((s1: State) reads * requires P.0.requires(s1) => exists p: State :: P.0.requires(p) && P.0(p) && forall v: Variable :: v in V ==> v in s1 && v in p && p[v] == s1[v]), P.1); 
			var P7 := (((s1: State) reads * requires P.0.requires(s1) => exists p: State :: P.0.requires(p) && P.0(p) && P2(p).0(s1)), P.1);
			assert EquivalentPredicates(P6,P7);
			Leibniz2(wp, P6,P7, SV);}
		wp(SV,(((s1: State) reads * requires P.0.requires(s1) => exists p: State :: P.0.requires(p) && P.0(p) && forall v: Variable :: v in V ==> v in s1 && v in p && p[v] == s1[v]), P.1)).0(s);
		==> {}
		wp(SV,P1).0(s);
		==> {Equation_5_1(P,V);assert EquivalentPredicates(P,P1);Leibniz2(wp,P,P1,SV);}
		wp(SV,P).0(s);
		}
	}
	/*}
	}*/
}

predicate dummy3(S: Statement, SV: Statement, V: set<Variable>)
reads *
requires Valid(S)
requires Valid(SV)
{
	(((forall s: State :: ((wp(S,ConstantPredicate(true)).0(s) ==> wp(SV,ConstantPredicate(true)).0(s)))) && (forall s: State, v: Variable :: v in (def(S)+def(SV)-V) && v in s ==> (wp(S,PointwisePredicate(s,v)).0(s) ==> wp(SV,PointwisePredicate(s,v)).0(s)))))
}

lemma dummy3Lemma(S: Statement, SV: Statement, V: set<Variable>)
requires Valid(S)
requires Valid(SV)
ensures dummy3(S,SV,V) <==> (((forall s: State :: ((wp(S,ConstantPredicate(true)).0(s) ==> wp(SV,ConstantPredicate(true)).0(s)))) && (forall s: State, v: Variable :: v in (def(S)+def(SV)-V) && v in s ==> (wp(S,PointwisePredicate(s,v)).0(s) ==> wp(SV,PointwisePredicate(s,v)).0(s)))))

lemma Corollary_5_2 (S: Statement, SV: Statement, V: set<Variable>)
requires Valid(S)
requires Valid(SV)
ensures (CoSliceRefinement(S,SV,V)) <==> dummy3(S,SV,V)
{
	calc {
	CoSliceRefinement(S,SV,V);
	== {Corollary_5_3(S,SV,V,(def(S) + def(SV)) - V);}
	SliceRefinement(S,SV,(def(S) + def(SV)) - V);
	== {Theorem_5_1(S,SV,(def(S) + def(SV)) - V);dummy7Lemma(S,SV,(def(S) + def(SV)) - V);}
	((forall s:State :: ((wp(S,ConstantPredicate(true)).0(s) ==> wp(SV,ConstantPredicate(true)).0(s)))) && (forall s: State, v: Variable :: v in (def(S)+def(SV)-V) && v in s ==> (wp(S,PointwisePredicate(s,v)).0(s) ==> wp(SV,PointwisePredicate(s,v)).0(s))));
	== {dummy3Lemma(S,SV,V);}
	dummy3(S,SV,V);
	}
}

lemma Corollary_5_3 (S: Statement, SV: Statement, V: set<Variable>, CoV: set<Variable>)
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


lemma Corollary_5_3Left (S: Statement, SV: Statement, V: set<Variable>, CoV: set<Variable>)
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
		var P1 := ((s0:State) reads * =>(exists p: State ::  P.0.requires(p) && P.0(p) && (forall v: Variable :: v in CoV1 ==> v in s0 && v in p && s0[v] == p[v]) && (forall v: Variable :: v in ND ==> v in s0 && v in p && s0[v] == p[v])),P.1);
		calc {
			wp(S,P).0(s);
			== {assume EquivalentPredicates(P,P1);Leibniz2(wp,P,P1,S);}
			wp(S,P1).0(s);
			==>{}
			wp(SV,P).0(s);
		}
	}
}

predicate dummy4(S: Statement, SV: Statement, V: set<Variable>)
reads *
requires Valid(S)
requires Valid(SV)
{
	(forall s: State :: ((wp(S,ConstantPredicate(true)).0(s) ==> wp(SV,ConstantPredicate(true)).0(s)))) && (forall s: State ,v: Variable :: v in (V+def(S)+def(SV)) && v in s  ==> (wp(S,PointwisePredicate(s,v)).0(s) ==> wp(SV,PointwisePredicate(s,v)).0(s)))
}

lemma dummy4Lemma(S: Statement, SV: Statement, V: set<Variable>)
requires Valid(S)
requires Valid(SV)
ensures dummy4(S,SV,V) <==> (forall s: State :: ((wp(S,ConstantPredicate(true)).0(s) ==> wp(SV,ConstantPredicate(true)).0(s)))) && (forall s: State ,v: Variable :: v in (V+def(S)+def(SV)) && v in s  ==> (wp(S,PointwisePredicate(s,v)).0(s) ==> wp(SV,PointwisePredicate(s,v)).0(s)))

// TODO: complete 1 error : 2 assemption to use 5.5 -> why is it valid to all ranges?
lemma {:verify false} dummy4AllRange(S: Statement, SV: Statement, V: set<Variable>)
requires Valid(S)
requires Valid(SV)
ensures dummy3(S,SV,{}) <==>  dummy4(S,SV,V)
{
	forall s: State, v: Variable  {
	calc {
	dummy3(S,SV,{});
	== {dummy3Lemma(S,SV,{});}
	(((forall s: State :: ((wp(S,ConstantPredicate(true)).0(s) ==> wp(SV,ConstantPredicate(true)).0(s)))) && (forall s: State, v: Variable :: v in (def(S)+def(SV)-{}) && v in s ==> (wp(S,PointwisePredicate(s,v)).0(s) ==> wp(SV,PointwisePredicate(s,v)).0(s)))));
	== {}
	((forall s: State :: ((wp(S,ConstantPredicate(true)).0(s) ==> wp(SV,ConstantPredicate(true)).0(s)))) && (forall s: State ,v: Variable :: v in (def(S)+def(SV)) && v in s ==> (wp(S,PointwisePredicate(s,v)).0(s) ==> wp(SV,PointwisePredicate(s,v)).0(s))));
	== {var P:=  (((s1: State) reads *  =>  v in (def(S)+def(SV)-{}) && v in s && v in s1 && s[v] == s1[v]),{v}); assume vars(P) !! (def(S) + def(SV)); assume (forall s: State :: ((wp(S,ConstantPredicate(true)).0(s) ==> wp(SV,ConstantPredicate(true)).0(s)))); Corollary_5_5(S, SV,P);}
	((forall s: State :: ((wp(S,ConstantPredicate(true)).0(s) ==> wp(SV,ConstantPredicate(true)).0(s)))) && (forall s: State ,v: Variable :: (v in (def(S)+def(SV)) || v in (V - (def(S)+def(SV)))) && v in s ==> (wp(S,PointwisePredicate(s,v)).0(s) ==> wp(SV,PointwisePredicate(s,v)).0(s))));
	== {}
	((forall s: State :: ((wp(S,ConstantPredicate(true)).0(s) ==> wp(SV,ConstantPredicate(true)).0(s)))) && (forall s: State ,v: Variable :: v in (V + def(S)+def(SV)) && v in s ==> (wp(S,PointwisePredicate(s,v)).0(s) ==> wp(SV,PointwisePredicate(s,v)).0(s))));
	== {dummy4Lemma(S,SV,V);}
	dummy4(S,SV,V);
	}
	}
}


lemma dummy4dummy5Lemma(S: Statement, SV: Statement, V: set<Variable>)
requires Valid(S)
requires Valid(SV)
ensures dummy4(S,SV,V) <==> dummy5(S,SV,V)
{
	calc {
		dummy4(S,SV,V);
		== {dummy4Lemma(S,SV,V);}
		(forall s: State :: ((wp(S,ConstantPredicate(true)).0(s) ==> wp(SV,ConstantPredicate(true)).0(s)))) && (forall s: State ,v: Variable :: v in (V+def(S)+def(SV)) && v in s  ==> (wp(S,PointwisePredicate(s,v)).0(s) ==> wp(SV,PointwisePredicate(s,v)).0(s)));
		== {}
		(forall s: State :: ((wp(S,ConstantPredicate(true)).0(s) ==> wp(SV,ConstantPredicate(true)).0(s)))) && (forall s: State ,v: Variable :: (v in (V) || v in (def(S)+def(SV)-V)) && v in s  ==> (wp(S,PointwisePredicate(s,v)).0(s) ==> wp(SV,PointwisePredicate(s,v)).0(s)));
		== {dummy4AllLemma(S,SV,V);}
		dummy4All(S,SV,V);
		== {dummy4Alldummy5Lemma(S,SV,V);}
		dummy5(S,SV,V);
	}

}

predicate dummy4All(S: Statement, SV: Statement, V: set<Variable>)
reads *
requires Valid(S)
requires Valid(SV)
{
	(forall s: State :: ((wp(S,ConstantPredicate(true)).0(s) ==> wp(SV,ConstantPredicate(true)).0(s)))) && (forall s: State ,v: Variable :: (v in (V) || v in (def(S)+def(SV)-V)) && v in s  ==> (wp(S,PointwisePredicate(s,v)).0(s) ==> wp(SV,PointwisePredicate(s,v)).0(s)))
}

predicate dummy4A(S: Statement, SV: Statement, V: set<Variable>)
reads *
requires Valid(S)
requires Valid(SV)
{
	(forall s: State :: ((wp(S,ConstantPredicate(true)).0(s) ==> wp(SV,ConstantPredicate(true)).0(s))))
}

predicate dummy4B(S: Statement, SV: Statement, V: set<Variable>)
reads *
requires Valid(S)
requires Valid(SV)
{
	(forall s: State ,v: Variable :: (v in (V) || v in (def(S)+def(SV)-V)) && v in s  ==> (wp(S,PointwisePredicate(s,v)).0(s) ==> wp(SV,PointwisePredicate(s,v)).0(s)))
}

predicate dummy4C(S: Statement, SV: Statement, V: set<Variable>)
reads *
requires Valid(S)
requires Valid(SV)
{
	(forall s: State ,v: Variable :: v in (V) && v in s ==> (wp(S,PointwisePredicate(s,v)).0(s) ==> wp(SV,PointwisePredicate(s,v)).0(s))) && (forall s: State ,v: Variable :: v in ((def(S)+def(SV))-V) && v in s  ==> (wp(S,PointwisePredicate(s,v)).0(s) ==> wp(SV,PointwisePredicate(s,v)).0(s)))
}


lemma dummy4AllLemma(S: Statement, SV: Statement, V: set<Variable>)
requires Valid(S)
requires Valid(SV)
ensures dummy4All(S,SV,V) <==> (forall s: State :: ((wp(S,ConstantPredicate(true)).0(s) ==> wp(SV,ConstantPredicate(true)).0(s)))) && (forall s: State ,v: Variable :: (v in (V) || v in (def(S)+def(SV)-V)) && v in s  ==> (wp(S,PointwisePredicate(s,v)).0(s) ==> wp(SV,PointwisePredicate(s,v)).0(s)))

lemma dummy4ALemma(S: Statement, SV: Statement, V: set<Variable>)
requires Valid(S)
requires Valid(SV)
ensures dummy4A(S,SV,V) <==> (forall s: State :: ((wp(S,ConstantPredicate(true)).0(s) ==> wp(SV,ConstantPredicate(true)).0(s))))

lemma dummy4BLemma(S: Statement, SV: Statement, V: set<Variable>)
requires Valid(S)
requires Valid(SV)
ensures dummy4B(S,SV,V) <==> (forall s: State ,v: Variable :: (v in (V) || v in (def(S)+def(SV)-V)) && v in s  ==> (wp(S,PointwisePredicate(s,v)).0(s) ==> wp(SV,PointwisePredicate(s,v)).0(s)))

lemma dummy4CLemma(S: Statement, SV: Statement, V: set<Variable>)
requires Valid(S)
requires Valid(SV)
ensures dummy4C(S,SV,V) <==> (forall s: State ,v: Variable :: v in (V) && v in s ==> (wp(S,PointwisePredicate(s,v)).0(s) ==> wp(SV,PointwisePredicate(s,v)).0(s))) && (forall s: State ,v: Variable :: v in ((def(S)+def(SV))-V) && v in s  ==> (wp(S,PointwisePredicate(s,v)).0(s) ==> wp(SV,PointwisePredicate(s,v)).0(s)))

lemma dummy4Bdummy4CLemma(S: Statement, SV: Statement, V: set<Variable>)
requires Valid(S)
requires Valid(SV)
ensures dummy4B(S,SV,V) <==> dummy4C(S,SV,V)
{
	calc {
		dummy4B(S,SV,V);
		=={}
		(forall s: State ,v: Variable :: (v in V || v in ((def(S)+def(SV))-V)) && v in s  ==> (wp(S,PointwisePredicate(s,v)).0(s) ==> wp(SV,PointwisePredicate(s,v)).0(s)));
		=={dummy4CLemma(S,SV,V);}
		/*(forall s: State ,v: Variable :: v in V && v in s ==> (wp(S,PointwisePredicate(s,v)).0(s) ==> wp(SV,PointwisePredicate(s,v)).0(s))) && (forall s: State ,v: Variable :: v in ((def(S)+def(SV))-V)  ==> (wp(S,PointwisePredicate(s,v)).0(s) ==> wp(SV,PointwisePredicate(s,v)).0(s)));
		=={}*/
		dummy4C(S,SV,V);
	}
}


lemma dummy4Alldummy5Lemma(S: Statement, SV: Statement, V: set<Variable>)
requires Valid(S)
requires Valid(SV)
ensures dummy4All(S,SV,V) <==> dummy5(S,SV,V)
{
	calc {
		dummy4All(S,SV,V);
		== {} 
		dummy4A(S,SV,V) && dummy4B(S,SV,V);
		== {dummy4Bdummy4CLemma(S,SV,V);}
		dummy4A(S,SV,V) && dummy4C(S,SV,V);
		== {}
		dummy5(S,SV,V);
	}
}


predicate dummy5(S: Statement, SV: Statement, V: set<Variable>)
reads *
requires Valid(S)
requires Valid(SV)
{
	(forall s: State :: ((wp(S,ConstantPredicate(true)).0(s) ==> wp(SV,ConstantPredicate(true)).0(s)))) && (forall s: State ,v: Variable :: v in (V) && v in s ==> (wp(S,PointwisePredicate(s,v)).0(s) ==> wp(SV,PointwisePredicate(s,v)).0(s))) && (forall s: State ,v: Variable :: v in ((def(S)+def(SV))-V) && v in s ==> (wp(S,PointwisePredicate(s,v)).0(s) ==> wp(SV,PointwisePredicate(s,v)).0(s)))
}

lemma dummy5Lemma(S: Statement, SV: Statement, V: set<Variable>)
requires Valid(S)
requires Valid(SV)
ensures dummy5(S,SV,V) <==> (forall s: State :: ((wp(S,ConstantPredicate(true)).0(s) ==> wp(SV,ConstantPredicate(true)).0(s)))) && (forall s: State ,v: Variable :: v in (V) && v in s ==> (wp(S,PointwisePredicate(s,v)).0(s) ==> wp(SV,PointwisePredicate(s,v)).0(s))) && (forall s: State ,v: Variable :: v in ((def(S)+def(SV))-V) && v in s ==> (wp(S,PointwisePredicate(s,v)).0(s) ==> wp(SV,PointwisePredicate(s,v)).0(s)))

lemma dummy5dummy6Lemma(S: Statement, SV: Statement, V: set<Variable>,CoV: set<Variable>)
requires Valid(S)
requires Valid(SV)
requires CoV == (def(S) + def(SV)) - V
ensures dummy5(S,SV,V) <==> dummy6(S,SV,V,CoV) && CoDummy6(S,SV,V,CoV)
{
	calc {
		dummy5(S,SV,V);
		=={dummy5Lemma(S,SV,V);}
		(forall s: State :: ((wp(S,ConstantPredicate(true)).0(s) ==> wp(SV,ConstantPredicate(true)).0(s)))) && (forall s: State ,v: Variable :: v in (V) && v in s ==> (wp(S,PointwisePredicate(s,v)).0(s) ==> wp(SV,PointwisePredicate(s,v)).0(s))) && (forall s: State ,v: Variable :: v in ((def(S)+def(SV))-V) && v in s  ==> (wp(S,PointwisePredicate(s,v)).0(s) ==> wp(SV,PointwisePredicate(s,v)).0(s)));
		== {}
		(forall s: State :: ((wp(S,ConstantPredicate(true)).0(s) ==> wp(SV,ConstantPredicate(true)).0(s)))) && (forall s: State :: ((wp(S,ConstantPredicate(true)).0(s) ==> wp(SV,ConstantPredicate(true)).0(s)))) && (forall s: State ,v: Variable :: v in (V) && v in s ==> (wp(S,PointwisePredicate(s,v)).0(s) ==> wp(SV,PointwisePredicate(s,v)).0(s))) && (forall s: State ,v: Variable :: v in ((def(S)+def(SV))-V) && v in s  ==> (wp(S,PointwisePredicate(s,v)).0(s) ==> wp(SV,PointwisePredicate(s,v)).0(s)));
		== {dummy6Lemma(S,SV,V,CoV);}
		dummy6(S,SV,V,CoV) && (forall s: State :: ((wp(S,ConstantPredicate(true)).0(s) ==> wp(SV,ConstantPredicate(true)).0(s)))) && (forall s: State ,v: Variable :: v in ((def(S)+def(SV))-V) && v in s  ==> (wp(S,PointwisePredicate(s,v)).0(s) ==> wp(SV,PointwisePredicate(s,v)).0(s)));
		== {assert CoV == (def(S) + def(SV)) - V;}
		dummy6(S,SV,V,CoV) && (forall s: State :: ((wp(S,ConstantPredicate(true)).0(s) ==> wp(SV,ConstantPredicate(true)).0(s)))) && (forall s: State ,v: Variable :: v in (CoV) && v in s ==> (wp(S,PointwisePredicate(s,v)).0(s) ==> wp(SV,PointwisePredicate(s,v)).0(s)));
		//					  (forall s: State :: ((wp(S,ConstantPredicate(true)).0(s) ==> wp(SV,ConstantPredicate(true)).0(s)))) && (forall s: State ,v: Variable :: v in (CoV) && v in s ==> (wp(S,PointwisePredicate(s,v)).0(s) ==> wp(SV,PointwisePredicate(s,v)).0(s)))
		== {CoDummy6Lemma(S,SV,V,CoV);}
		dummy6(S,SV,V,CoV) && CoDummy6(S,SV,V,CoV);
	}
}

predicate dummy6(S: Statement, SV: Statement, V: set<Variable>,CoV: set<Variable>)
reads *
requires Valid(S)
requires Valid(SV)
requires CoV == (def(S) + def(SV)) - V
{
	(forall s: State :: ((wp(S,ConstantPredicate(true)).0(s) ==> wp(SV,ConstantPredicate(true)).0(s)))) && (forall s: State ,v: Variable :: v in (V) && v in s ==> (wp(S,PointwisePredicate(s,v)).0(s) ==> wp(SV,PointwisePredicate(s,v)).0(s)))
}

predicate CoDummy6(S: Statement, SV: Statement, V: set<Variable>,CoV: set<Variable>)
reads *
requires Valid(S)
requires Valid(SV)
requires CoV == (def(S) + def(SV)) - V
{
	(forall s: State :: ((wp(S,ConstantPredicate(true)).0(s) ==> wp(SV,ConstantPredicate(true)).0(s)))) && (forall s: State ,v: Variable :: v in (CoV) && v in s ==> (wp(S,PointwisePredicate(s,v)).0(s) ==> wp(SV,PointwisePredicate(s,v)).0(s)))
}


lemma dummy6Lemma(S: Statement, SV: Statement, V: set<Variable>,CoV: set<Variable>)
requires Valid(S)
requires Valid(SV)
requires CoV == (def(S) + def(SV)) - V
ensures dummy6(S,SV,V,CoV) <==> (forall s: State :: ((wp(S,ConstantPredicate(true)).0(s) ==> wp(SV,ConstantPredicate(true)).0(s)))) && (forall s: State ,v: Variable :: v in (V) && v in s ==> (wp(S,PointwisePredicate(s,v)).0(s) ==> wp(SV,PointwisePredicate(s,v)).0(s)))

lemma CoDummy6Lemma(S: Statement, SV: Statement, V: set<Variable>,CoV: set<Variable>)
requires Valid(S)
requires Valid(SV)
requires CoV == (def(S) + def(SV)) - V
ensures CoDummy6(S,SV,V,CoV) <==> (forall s: State :: ((wp(S,ConstantPredicate(true)).0(s) ==> wp(SV,ConstantPredicate(true)).0(s)))) && (forall s: State ,v: Variable :: v in (CoV) && v in s ==> (wp(S,PointwisePredicate(s,v)).0(s) ==> wp(SV,PointwisePredicate(s,v)).0(s)))

lemma CoDummy6CoSliceRefinementLemma(S: Statement, SV: Statement, V: set<Variable>,CoV: set<Variable>)
requires Valid(S)
requires Valid(SV)
requires CoV == (def(S)+def(SV))-V
ensures CoSliceRefinement(S,SV,V) <==> CoDummy6(S,SV,V,CoV)
{
	calc {
		CoDummy6(S,SV,V,CoV);
		== {CoDummy6Lemma(S,SV,V,CoV);}
		(forall s: State :: ((wp(S,ConstantPredicate(true)).0(s) ==> wp(SV,ConstantPredicate(true)).0(s)))) && (forall s: State ,v: Variable :: v in (CoV) && v in s ==> (wp(S,PointwisePredicate(s,v)).0(s) ==> wp(SV,PointwisePredicate(s,v)).0(s)));
		== {assert CoV == (def(S)+def(SV)-V);}
		(forall s: State :: ((wp(S,ConstantPredicate(true)).0(s) ==> wp(SV,ConstantPredicate(true)).0(s)))) && (forall s: State ,v: Variable :: v in (def(S)+def(SV)-V) && v in s ==> (wp(S,PointwisePredicate(s,v)).0(s) ==> wp(SV,PointwisePredicate(s,v)).0(s)));
		== {dummy3Lemma(S,SV,V);}
		dummy3(S,SV,V);
		== {Corollary_5_2(S,SV,V);}
		CoSliceRefinement(S,SV,V);
	}
}


lemma dummy6SliceRefinementLemma(S: Statement, SV: Statement, V: set<Variable>,CoV: set<Variable>)
requires Valid(S)
requires Valid(SV)
requires CoV == (def(S)+def(SV))-V
ensures SliceRefinement(S,SV,V) <==> dummy6(S,SV,V,CoV)
{
	calc {
		dummy6(S,SV,V,CoV);
		=={dummy6Lemma(S,SV,V,CoV);}
		(forall s: State :: ((wp(S,ConstantPredicate(true)).0(s) ==> wp(SV,ConstantPredicate(true)).0(s)))) && (forall s: State ,v: Variable :: v in (V) && v in s ==> (wp(S,PointwisePredicate(s,v)).0(s) ==> wp(SV,PointwisePredicate(s,v)).0(s)));
		== {}
		(forall s: State :: ((wp(S,ConstantPredicate(true)).0(s) ==> wp(SV,ConstantPredicate(true)).0(s)))) && (forall s: State ,v: Variable :: v in (V) && v in s ==> (wp(S,PointwisePredicate(s,v)).0(s) ==> wp(SV,PointwisePredicate(s,v)).0(s)));
	//	(forall s: State :: ((wp(S,ConstantPredicate(true)).0(s) ==> wp(SV,ConstantPredicate(true)).0(s)))) && (forall s: State, v: Variable :: v in V && v in s ==> (wp(S,PointwisePredicate(s,v)).0(s) ==> wp(SV,PointwisePredicate(s,v)).0(s)))	
		== {dummy7Lemma(S,SV,V);}
		dummy7(S,SV,V);
		=={Theorem_5_1(S,SV,V);}
		SliceRefinement(S,SV,V);
	}
}

lemma Corollary_5_4 (S: Statement, T: Statement, V: set<Variable>)
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
		dummy3(S,T,{});
		== {dummy4AllRange(S,T,V);}
		dummy4(S,T,V);
		== {dummy4dummy5Lemma(S,T,V);}
		dummy5(S,T,V);
		== {dummy5dummy6Lemma(S,T,V,(def(S)+def(T))-V);}
		dummy6(S,T,V,(def(S)+def(T))-V) && CoDummy6(S,T,V,(def(S)+def(T))-V);
		== {dummy6SliceRefinementLemma(S,T,V,(def(S)+def(T))-V);CoDummy6CoSliceRefinementLemma(S,T,V,(def(S)+def(T))-V);}
		SliceRefinement(S,T,V) && CoSliceRefinement(S,T,V);
		/*((forall s: State :: ((wp(S,ConstantPredicate(true)).0(s) ==> wp(T,ConstantPredicate(true)).0(s)))) 
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
		SliceRefinement(S,T,V) && CoSliceRefinement(S,T,V);*/
		}
}



lemma Corollary_5_5 (S: Statement, T: Statement, P:Predicate)
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
// All the following lemma's and predicates till Corollary_5_6 are used in that order so i can prove it to dafny that Corollary_5_6 is correct 
predicate dummy1 (S: Statement, T: Statement, V: set<Variable>)
reads * 
requires Valid(S)
requires Valid(T)
{
	SliceRefinement(S,T,V)	&& EquivalentPredicates(wp(S,ConstantPredicate(true)),wp(T,ConstantPredicate(true)))
}

predicate dummy1forall (S: Statement, T: Statement, V: set<Variable>)
reads * 
requires Valid(S)
requires Valid(T)
{
	(forall P: Predicate, s: State :: vars(P) <= V ==> wp(S, P).0(s) == wp(T, P).0(s))
}

lemma Dummy1ForallLemma(S: Statement, T: Statement, V: set<Variable>)
requires Valid(S)
requires Valid(T)
ensures dummy1forall(S,T,V) == (forall P: Predicate, s: State :: vars(P) <= V ==> wp(S, P).0(s) == wp(T, P).0(s))  


lemma EquivalentDummy1Lemma(S: Statement, T: Statement, V: set<Variable>)
requires Valid(S)
requires Valid(T)
ensures dummy1(S,T,V) <==> dummy1forall(S,T,V) 
{
	calc {
	dummy1(S,T,V);
	=={}
	SliceRefinement(S,T,V)	&& EquivalentPredicates(wp(S,ConstantPredicate(true)),wp(T,ConstantPredicate(true)));
	=={SliceRefinementLemma(S,T,V);}
	((forall P: Predicate, s: State :: vars(P) <= V ==> wp(S, P).0(s) ==> wp(T, P).0(s)) && EquivalentPredicates(wp(S,ConstantPredicate(true)),wp(T,ConstantPredicate(true))));
	=={}
	forall P: Predicate, s: State :: vars(P) <= V ==> ((wp(S, P).0(s) ==> wp(T, P).0(s)) && (EquivalentPredicates(wp(S,ConstantPredicate(true)),wp(T,ConstantPredicate(true)))));
	=={Lemma_4_2inV(S, T,V);}
	(forall P: Predicate, s: State :: vars(P) <= V ==> wp(S, P).0(s) == wp(T, P).0(s));
	== {Dummy1ForallLemma(S,T,V);}
	dummy1forall(S,T,V);
	}
}

predicate dummy2 (S: Statement, T: Statement, V: set<Variable>)
reads * 
requires Valid(S)
requires Valid(T)
{
	CoSliceRefinement(S,T,V) && EquivalentPredicates(wp(S,ConstantPredicate(true)),wp(T,ConstantPredicate(true)))
}

predicate dummy2forall (S: Statement, T: Statement, V: set<Variable>)
reads * 
requires Valid(S)
requires Valid(T)
{
	(forall P: Predicate, s: State :: vars(P) !! V ==> wp(S, P).0(s) == wp(T, P).0(s)) 
}

lemma Dummy2ForallLemma(S: Statement, T: Statement, V: set<Variable>)
requires Valid(S)
requires Valid(T)
ensures dummy2forall(S,T,V) == (forall P: Predicate, s: State :: vars(P) !! V ==> wp(S, P).0(s) == wp(T, P).0(s))

lemma EquivalentDummy2Lemma(S: Statement, T: Statement, V: set<Variable>)
requires Valid(S)
requires Valid(T)
ensures dummy2(S,T,V) == dummy2forall(S,T,V)
{
	calc {
	dummy2(S,T,V);
	=={}
	CoSliceRefinement(S,T,V)	&& EquivalentPredicates(wp(S,ConstantPredicate(true)),wp(T,ConstantPredicate(true)));
	=={CoSliceRefinementLemma(S,T,V);}
	((forall P: Predicate, s: State :: vars(P) !! V ==> wp(S, P).0(s) ==> wp(T, P).0(s)) && EquivalentPredicates(wp(S,ConstantPredicate(true)),wp(T,ConstantPredicate(true))));
	=={}
	forall P: Predicate, s: State :: vars(P) !! V ==> ((wp(S, P).0(s) ==> wp(T, P).0(s)) && (EquivalentPredicates(wp(S,ConstantPredicate(true)),wp(T,ConstantPredicate(true)))));
	=={Lemma_4_2StrangerV(S, T, V);}
	(forall P: Predicate, s: State :: vars(P) !! V ==> wp(S, P).0(s) == wp(T, P).0(s));
	== {Dummy2ForallLemma(S,T,V);}
	dummy2forall(S,T,V);
	}
}

lemma Corollary_5_6 (S: Statement, T: Statement, V: set<Variable>)
requires Valid(S)
requires Valid(T)
ensures EquivalentStatments(S,T) <==> dummy1forall(S,T,V) && dummy2forall(S,T,V)
{
		calc{
		EquivalentStatments(S,T);
		== {Theorem_4_1(S,T);}
		Refinement(S,T) && EquivalentPredicates(wp(S,ConstantPredicate(true)),wp(T,ConstantPredicate(true)));
		== {Corollary_5_4(S,T,V);}
		SliceRefinement(S,T,V) && CoSliceRefinement(S,T,V) && EquivalentPredicates(wp(S,ConstantPredicate(true)),wp(T,ConstantPredicate(true)));
		== {}
		SliceRefinement(S,T,V) && CoSliceRefinement(S,T,V) && EquivalentPredicates(wp(S,ConstantPredicate(true)),wp(T,ConstantPredicate(true))) 
		&& EquivalentPredicates(wp(S,ConstantPredicate(true)),wp(T,ConstantPredicate(true)));
		== {} 
		SliceRefinement(S,T,V) && EquivalentPredicates(wp(S,ConstantPredicate(true)),wp(T,ConstantPredicate(true))) 
		&& CoSliceRefinement(S,T,V) && EquivalentPredicates(wp(S,ConstantPredicate(true)),wp(T,ConstantPredicate(true)));
		== {}
		dummy1(S,T,V) && dummy2(S,T,V);
		== {EquivalentDummy1Lemma(S,T,V);EquivalentDummy2Lemma(S,T,V);}
		dummy1forall(S,T,V) && dummy2forall(S,T,V);
		}
}

lemma ProgramEquivalence5_7 ( S1: Statement, S2: Statement)
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
