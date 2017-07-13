//============================================================
//					*** DATATYPES ***
//============================================================

datatype Statement = Assignment(LHS: seq<Variable>, RHS: seq<Expression>) | Skip | SeqComp(S1: Statement, S2: Statement) | 
		IF(B0: BooleanExpression, Sthen: Statement, Selse: Statement) | DO(B: BooleanExpression, Sloop: Statement) |
		LocalDeclaration(L: seq<Variable>, S0: Statement)
type Variable = string
datatype Value = Int(i: int) | Bool(b: bool)
type Expression = (State -> Value, set<Variable>)
type BooleanExpression = (State -> bool, set<Variable>) // State->Value,set<Variable>
type State = map<Variable, Value>
type Predicate = (State -> bool, set<Variable>)//string


//============================================================
//					*** Validation ***
//============================================================

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

predicate method ValidAssignment(str: string)
{
	true // check ":=" with same-length lists to its left and right, the former of distinct variable names and the right of expressions
}

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
//					*** Constractors ***
//============================================================

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

function VarsOfPredicateSet(W: set<Predicate>): set<Variable>
{
	if W == {} then {} else var w :| w in W; w.1 + VarsOfPredicateSet(W-{w})
}

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
 
