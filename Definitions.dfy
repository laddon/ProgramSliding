//============================================================
//					*** DATATYPES ***
//============================================================

datatype Statement = Assignment(LHS: seq<Variable>, RHS: seq<Expression>) | Skip | SeqComp(S1: Statement, S2: Statement) | 
		IF(B0: BooleanExpression, Sthen: Statement, Selse: Statement) | DO(B: BooleanExpression, Sloop: Statement) |
		LocalDeclaration(L: seq<Variable>, S0: Statement) | Live(L: seq<Variable>, S0: Statement) | Assert(B: BooleanExpression)
type Variable = string
datatype Value = Int(i: int) | Bool(b: bool)
type Expression = (State -> Value, set<Variable>)
type BooleanExpression = (State -> bool, set<Variable>) 
type State = map<Variable, Value>
type Predicate = (State -> bool, set<Variable>)


//============================================================
//					*** Validation ***
//============================================================

predicate Valid(stmt: Statement) reads *
{
	match stmt {
		case Skip => true
		case Assignment(LHS,RHS) => ValidAssignment(LHS,RHS) 
		case SeqComp(S1,S2) => Valid(S1) && Valid(S2)
		case IF(B0,Sthen,Selse) => 
			(forall state: State :: B0.0.requires(state) /*&& B.0(state).Bool?*/) && 
			Valid(Sthen) && Valid(Selse)
		case DO(B,Sloop) =>
			(forall state: State :: B.0.requires(state) /*&& B.0(state).Bool?*/) && Valid(Sloop)
		case LocalDeclaration(L,S0) => Valid(S0)
		case Live(L, S0) => Valid(S0)
		case Assert(B) => true
	} &&
	// TODO: FixMe
	//(forall state1: State, P: Predicate  :: (forall v :: v in state1 ==> v in P.1) ==> P.0.requires(state1))
	forall state1: State, P: Predicate  ::  P.0.requires(state1)
}

predicate Core(stmt: Statement)
{
	match stmt {
		case Skip => true
		case Assignment(LHS, RHS) => true
		case SeqComp(S1, S2) => Core(S1) && Core(S2)
		case IF(B0,Sthen,Selse) => Core(Sthen) && Core(Selse)
		case DO(B,Sloop) => Core(Sloop)
		case LocalDeclaration(L,S0) => false
		case Live(L,S0) => false
		case Assert(B) => false
	}
}

function ValidAssignment(LHS:  seq<Variable>, RHS: seq<Expression>): bool 
{
	if (|LHS| != |RHS|) then false else true 
}

/*
predicate method ValidAssignment(str: string)
{
	true // check ":=" with same-length lists to its left and right, the former of distinct variable names and the right of expressions
}
*/

//============================================================
//					*** PRINTING ***
//============================================================

function method ToString(S: Statement) : string
{
	match S {
		case Assignment(LHS,RHS) => AssignmentToString(LHS,RHS)
		case Skip => ";"
		case SeqComp(S1,S2) => ToString(S1) + ToString(S2)
		case IF(B0,Sthen,Selse) => "if " + BooleanExpressionToString(B0) + " {" + ToString(Sthen) + " else " + ToString(Selse) + " } "
		case DO(B,Sloop) => "while (" + BooleanExpressionToString(B) + ") { " + ToString(Sloop) + " } "
		case LocalDeclaration(L,S0) => "{ var " + VariableListToString(L) + "; " + ToString(S0) + " } "
		case Live(L,S0) => "{ var " + VariableListToString(L) + "; " + ToString(S0) + " } "
		case Assert(B) => "assert " + BooleanExpressionToString(B) + ";"
	}
}

function method BooleanExpressionToString(B: BooleanExpression) : string 
{ "boolean expression... " } // TODO: implement

function method PredicateToString(P: Predicate) : string 
{ "predicate " } // TODO: implement

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

//============================================================
//					*** Constructors ***
//============================================================

function EqualityAssertion(X: seq<Variable>, E: seq<Expression>): (assertion: Statement)
	requires ValidAssignment(X,E)
{
	var B := ((state: State) reads * 
		requires (forall i :: 0 <= i < |X| ==> X[i] in state && E[i].0.requires(state)) => 
		forall i :: 0 <= i < |X| ==> state[X[i]] == E[i].0(state), 
		setOf(X)+varsInExps(E));
	Assert(B)
}

function method PredicateFromString(str: string): Predicate
{
	((state: map<Variable, Value>) => true,{})
}

function ConstantPredicate(b: bool): Predicate
{
	if b then ((_ => true),{})
	else ((_ => false),{})
}

//============================================================
//					*** Definitions ***
//============================================================

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

function existsK(i: nat, k: Predicate -> Predicate, state: State): bool
	reads *
	requires forall i: nat :: power.requires(k, i)
	requires forall i: nat, P: Predicate :: power(k, i).requires(P)
	requires forall state1: State, P: Predicate  :: P.0.requires(state1)
{
	var P := ((_ => false),(set v | v in state));
	exists i: nat :: power(k, i)(P).0(state)
}

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
		case IF(B0,Sthen,Selse) => var f:= (state: State)
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
		case Live(L,S0) => wp(S0,P)
		case Assert(B) => var f:= (state: State)
			reads *
			requires B.0.requires(state)
			requires P.0.requires(state)
			=> /*B.0(state).Bool? && */
			(B.0(state) && P.0(state));
			(f,vars(P)+B.1)
	}
}

function wlp(stmt: Statement, P: Predicate): Predicate
	reads Valid.reads(stmt)
	requires Valid(stmt)
	//requires stmt.LocalDeclaration? ==> vars(P) !! setOf(L)
{
	NOT(wp(stmt,NOT(P)))
}

lemma WP_Definition(S : Statement, P : Predicate)
requires Valid(S)
ensures EquivalentPredicates(wp(S,P),AND(wlp(S,P),wp(S,ConstantPredicate(true))))

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

function method def(S: Statement) : set<Variable>
{
	match S {
		case Assignment(LHS,RHS) => setOf(LHS)
		case Skip => {}
		case SeqComp(S1,S2) => def(S1) + def(S2)
		case IF(B0,Sthen,Selse) => def(Sthen) + def(Selse)
		case DO(B,Sloop) => def(Sloop)
		case LocalDeclaration(L,S0) => def(S0) - setOf(L)
		case Live(L,S0) => def(S0) - setOf(L)
		case Assert(B) => {}
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
		case Live(L,S0) => ddef(S0) - setOf(L)
		case Assert(B) => {}
	}
}

function method input(S: Statement) : set<Variable>
{
	match S {
		case Assignment(LHS,RHS) => varsInExps(RHS) 
		case Skip => {}
		case SeqComp(S1,S2) => input(S1) + (input(S2) - ddef(S1)) 
		case IF(B0,Sthen,Selse) => B0.1 + input(Sthen) + input(Selse)
		case DO(B,S) => B.1 + input(S) 
		case LocalDeclaration(L,S0) => input(S0) - setOf(L)
		case Live(L,S0) => input(S0) - setOf(L)
		case Assert(B) => B.1
	}
}

function method trigger<T>(x: T): bool
{
	true
}

function method glob(S: Statement) : set<Variable>
{
	set x | trigger(x) && x in def(S) + input(S)
}

function allVars(S: Statement): set<Variable>
{
	match S {
		case Skip => {}
		case Assignment(LHS, RHS) => setOf(LHS)+varsInExps(RHS)
		case SeqComp(S1, S2) => allVars(S1)+allVars(S2)
		case IF(B0,Sthen,Selse) => B0.1+allVars(Sthen)+allVars(Selse)
		case DO(B,S) => B.1 + allVars(S)
		case LocalDeclaration(L,S0) => setOf(L)+allVars(S0)
		case Live(L,S0) => setOf(L)+allVars(S0)
		case Assert(B) => B.1
	}
}

function method setOf<T>(s: seq<T>) : (res: set<T>)
ensures forall v :: v in res <==> v in s
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

function method {:verify true}seqVarToSeqExpr(seqvars: seq<Variable>): (res:seq<Expression>)
	ensures ValidAssignment(seqvars, res)
	ensures varsInExps(res) == setOf(seqvars)
{
	if seqvars == [] then []
	else 
		([((s:State)requires(seqvars[0] in s)=>s[seqvars[0]], {seqvars[0]})] + seqVarToSeqExpr(seqvars[1..]))
	
}

function method {:verify false} fSetToSeq(s : set<Variable>) : (res: seq<Variable>)
ensures |res| == |s|
{
if s == {} then []
else
	var v : Variable :| v in s;
	[v] + fSetToSeq(s - {v})
	
} 

predicate EquivalentPredicates(P1: Predicate, P2: Predicate) reads *
{
	forall s: State :: P1.0.requires(s) && P2.0.requires(s) ==> P1.0(s) == P2.0(s)  
}

lemma EquivalentPredicatesLemma(P1: Predicate, P2: Predicate)
ensures EquivalentPredicates(P1,P2) <==> (forall s: State :: P1.0.requires(s) && P2.0.requires(s) ==> P1.0(s) == P2.0(s))

predicate EquivalentBooleanExpressions(B1: BooleanExpression, B2: BooleanExpression) reads *
{
	B1.1 == B2.1 &&
	(forall s :: B1.0.requires(s) <==> B2.0.requires(s)) &&
	(forall s :: B1.0.requires(s) ==> B1.0(s) == B2.0(s))
}

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

predicate TerminationRefinement(S1: Statement, S2: Statement)
reads *
requires Valid(S1)
requires Valid(S2)
{
	forall s: State :: ((wp(S1,ConstantPredicate(true)).0(s) ==> wp(S2,ConstantPredicate(true)).0(s)))
}

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

function VarsOfPredicateSet(W: set<Predicate>): set<Variable>
{
	if W == {} then {} else var w :| w in W; w.1 + VarsOfPredicateSet(W-{w})
}

function PointwisePredicate(s: State, v: Variable) : Predicate
{
	(((s1: State) reads*  => v in s1 && v in s && s[v] == s1[v] ,{v}))
}

predicate PointwiseRefinement(S: Statement, T: Statement, s1: State, v: Variable)
	reads *
{
	Valid(S) && Valid(T) && v in s1 ==>
		(forall s2 :: (forall x :: x in input(S) || x in input(T) ==> x in s1) && 
		wp(S,PointwisePredicate(s1,v)).0(s2) ==> wp(T,PointwisePredicate(s1,v)).0(s2))
}

predicate SetPointwiseRefinement(S: Statement, T: Statement, V: set<Variable>)
	reads *
{
	Valid(S) && Valid(T) && (forall s: State ,v: Variable :: v in V && v in s ==> PointwiseRefinement(S,T,s,v))
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

//============================================================
//					*** Global Theorem ***
//============================================================

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

lemma Leibniz3<T>(f: (Statement,Predicate)->T, S: Statement,SV: Statement ,p: Predicate)
requires f.requires(S,p) && f.requires(SV,p)
ensures f(S,p) == f(SV,p)

lemma ConjWp(S: Statement, P1: Predicate, P2: Predicate)
requires Valid(S)
ensures  EquivalentPredicates(wp(S,AND(P1,P2)),AND(wp(S,P1),wp(S,P2)))

lemma LocalDecStrangers(S: Statement,P: Predicate)
requires S.LocalDeclaration? 
ensures S.LocalDeclaration? ==> vars(P) !! setOf(S.L)

lemma LocalDecStrangers2(S: Statement,P: Predicate)
requires S.LocalDeclaration? 
ensures S.LocalDeclaration? ==> vars(P) - ddef(S.S0) + input(S.S0) == vars(P) - ddef(S) + input(S)

lemma SubDefinitionLemma(P: Predicate,LHS: seq<Variable>, RHS: seq<Expression>,s: State)
requires setOf(LHS) !! vars(P)
requires P.0.requires(s)
requires |LHS| == |RHS|
requires sub(P, LHS, RHS).0.requires(s)
ensures P.0(s) == sub(P, LHS, RHS).0(s)
 
lemma Leibniz4(S1: Statement, S2: Statement, S2': Statement)
requires Valid(S1) && Valid(S2) && Valid(S2')
requires EquivalentStatments(S2,S2')
ensures EquivalentStatments(SeqComp(S1,S2),SeqComp(S1,S2'))
