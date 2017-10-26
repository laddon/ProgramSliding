include "Definitions.dfy"


/*
 * Functions for performing substitutions of variables by variables on statements
 * and of variables by variables or variables by expressions on
 * sequences of variables, expressions, sequences of expressions, 
 * and boolean expressions.
 *
 */
 
/*
 * Substitutions by variables:
 * Each of the following functions substitutes all occurrences of v from X with 
 * the corresponding v' from X'
 * 
 */
function method substitute(S: Statement, X: seq<Variable>, X': seq<Variable>) : (S': Statement)
requires Valid(S)
requires |X| == |X'|
requires setOf(X) !! setOf(X')
requires setOf(X') !! allVars(S)
requires Core(S)
ensures setOf(X) !! allVars(S')
ensures Valid(S')
{
	match S {
		case Skip => Skip
		case Assignment(LHS, RHS) => 
			var LHS' := VSubstitute(LHS, X, X');
			var RHS' := ESeqSubstitute(RHS, X, X');
			assert |LHS'| == |RHS'|;
			Assignment(LHS', RHS')
		case SeqComp(S1, S2) => 
			var S1' := substitute(S1, X, X');
			var S2' := substitute(S2, X, X');
			SeqComp(S1', S2')
		case IF(B0, Sthen, Selse) => 
			var B' := BSubstitute(B0, X, X');
			var Sthen' := substitute(Sthen, X, X');
			var Selse' := substitute(Selse, X, X');
			IF(B', Sthen', Selse')
		case DO(B, S) => 
			var B' := BSubstitute(B, X, X');
			var S'' := substitute(S, X, X');
			DO(B', S'')

		case LocalDeclaration(L, S0) => Skip // S is Core Statement
		case Live(L, S0) => Skip // S is Core Statement
	}
}

function method {:verify true} VSubstitute(
	LHS: seq<Variable>,
	X: seq<Variable>,
	X': seq<Variable>): (res: seq<Variable>)
	requires |X| == |X'|
	requires setOf(X) !! setOf(X')
	ensures |res| == |LHS|
	ensures setOf(X) !! setOf(res)
{
	if LHS == [] then []
	else
		[if LHS[0] in X
			then GetCorrespondingV(LHS[0], X, X')
			else LHS[0]] 
		 + VSubstitute(LHS[1..], X, X')
}

function method {:verify true} GetCorrespondingV(v: Variable, X: seq<Variable>, X': seq<Variable>)
: (res: Variable)
	requires v in X
	requires |X| == |X'|
	requires setOf(X) !! setOf(X')
	ensures res in X'
{
	if v == X[0] then X'[0]
	else
		assert setOf(X[1..]) !! setOf(X'[1..]) by {
			assert setOf(X[1..]) <= setOf(X);
		}
		GetCorrespondingV(v, X[1..], X'[1..])
}

function method {:verify true} BSubstitute(
	B0: BooleanExpression,
	X: seq<Variable>,
	X': seq<Variable>) : (res: BooleanExpression)
requires |X| == |X'|
requires setOf(X) !! setOf(X')
ensures |B0.1-setOf(X)+setOf(X')|==|res.1|
ensures setOf(X) !! res.1
{
	((state
		=> (forall v :: v in B0.1-setOf(X)+setOf(X') ==> v in state) && //(forall m :: (forall v :: v in B0.1 ==> v in m) ==> B0.0.requires(m)) &&
			var m := map v | v in B0.1 :: 
			(if v !in X 	
				then state[v] 
				else state[FindParallelV(v, X, X')]);

		B0.0(m)),
	 B0.1-setOf(X)+setOf(X'))
}

function method {:verify true} ESubstitute(
	E: Expression,
	X: seq<Variable>,
	X': seq<Variable>) : (res:Expression)
requires |X| == |X'|
requires setOf(X) !! setOf(X')
ensures |E.1-setOf(X)+setOf(X')|==|res.1|
ensures setOf(X) !! res.1
{
	var f := (state => 
			var m := map v | v in E.1 :: 
			(if v !in X 	
				then (if v in state then state[v] else Int(0))//Error
				else var v' := FindParallelV(v, X, X'); if v' in state then state[v'] else Int(0));// Error
		E.0(m));
	(f,E.1-setOf(X)+setOf(X'))
}

function method {:verify true} FindParallelV(v: Variable,
	X: seq<Variable>,
	X': seq<Variable>) : (res: Variable)
requires |X| == |X'|
requires v in X
ensures res in X'
{
	if v == X[0] then X'[0] else
	FindParallelV(v, X[1..], X'[1..])
}

function method {:verify true} ESeqSubstitute(
	Es : seq<Expression>,
	X: seq<Variable>,
	X': seq<Variable>) : (res : seq<Expression>)
requires |X| == |X'|
requires setOf(X) !! setOf(X')
ensures |res| == |Es|
ensures setOf(X) !! varsInExps(res)
{
	if Es == [] then []
	else
		[ESubstitute(Es[0], X, X')]+ESeqSubstitute(Es[1..], X, X')
}

/*
 * Substitutions by expressions:
 * Each of the following functions substitutes all occurrences of v from X with 
 * the corresponding v' from X'
 */
function method {:verify true} BSubstituteVbyE(
	B0: BooleanExpression,
	X: seq<Variable>,
	E: seq<Expression>) : (res: BooleanExpression)
requires |X| == |E|
{
	((state => 
			var m := map v | v in B0.1 :: 
			(if v !in X 	
				then if v in state then state[v] else Int(0)//Error
				else E[FindV(v, X)].0(state));

		B0.0(m)),
	 B0.1-setOf(X)+varsInExps(E))
}

function method {:verify true} FindV(v: Variable, X: seq<Variable>) : (res: nat)
requires v in X
ensures 0 <= res < |X| && X[res] == v
{
	if v == X[0] then 0 else 1+FindV(v,X[1..])
}

function method {:verify true} ESubstituteVbyE(
	E0: Expression,
	X: seq<Variable>,
	E: seq<Expression>) : (res:Expression)
requires |X| == |E|
{
	var f := (state => 
			var m := map v | v in E0.1 :: 
			(if v !in X 	
				then if v in state then state[v] else Int(0) //Error
				else E[FindV(v, X)].0(state));

		E0.0(m));
	(f,E0.1-setOf(X)+varsInExps(E))
}

function method {:verify true} ESeqSubstituteVbyE(
	Es: seq<Expression>,
	X: seq<Variable>,
	E: seq<Expression>) : (res : seq<Expression>)
requires |X| == |E|
{
	if Es == [] then []
	else
		[ESubstituteVbyE(Es[0], X, E)]+ESeqSubstituteVbyE(Es[1..], X, E)
}

lemma ReversedDoubleSubstitutions(B: BooleanExpression, V1: seq<Variable>, V2: seq<Variable>)
	requires |V1| == |V2|
	requires setOf(V1) !! setOf(V2) // TODO: should be removed after its removal from BSubstitute; and then could use BSubstitute instead of BSubstituteVbyE below
	requires setOf(V2) !! B.1
	ensures EquivalentBooleanExpressions(B,BSubstituteVbyE(BSubstitute(B,V1,V2),V2,seqVarToSeqExpr(V1)))