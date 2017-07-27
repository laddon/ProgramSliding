include "Definitions.dfy"
/*
 * Substitutes all occurances of v in X in S with v' in X'
 * 
 */
function method substitute(S: Statement, X: seq<Variable>, X': seq<Variable>) : (S': Statement)
reads *
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
reads *
requires |X| == |X'|
requires setOf(X) !! setOf(X')
ensures |B0.1-setOf(X)+setOf(X')|==|res.1|
ensures setOf(X) !! res.1
{
	((state reads * requires(forall v :: v in B0.1-setOf(X)+setOf(X') ==> v in state)
		requires forall m :: (forall v :: v in B0.1 ==> v in m) ==> B0.0.requires(m) 
		=> 
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
reads *
requires |X| == |X'|
requires setOf(X) !! setOf(X')
ensures |E.1-setOf(X)+setOf(X')|==|res.1|
ensures setOf(X) !! res.1
{
	((state reads * requires(forall v :: v in E.1-setOf(X)+setOf(X') ==> v in state)
		requires forall m :: (forall v :: v in E.1 ==> v in m) ==> E.0.requires(m) 
		=> 
			var m := map v | v in E.1 :: 
			(if v !in X 	
				then state[v] 
				else state[FindParallelV(v, X, X')]);

		E.0(m)),
	 E.1-setOf(X)+setOf(X'))
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
reads *
requires |X| == |X'|
requires setOf(X) !! setOf(X')
ensures |res| == |Es|
ensures setOf(X) !! varsInExps(res)
{
	if Es == [] then []
	else
		[ESubstitute(Es[0], X, X')]+ESeqSubstitute(Es[1..], X, X')
}
