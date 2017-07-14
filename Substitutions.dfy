/*
 * Substitutes all occurances of v in X in S with v' in X'
 * 
 */
function method substitute(S: Statement, X: seq<Variable>, X': seq<Variable>) : (S': Statement)
requires Valid(S)
requires |X| == |X'|
requires setOf(X) !! setOf(X')
requires setOf(X) <= glob(S)
requires setOf(X') !! glob(S) // consider replacing with allVars(S) (including locals)
requires S.Skip? || S.Assignment? || S.SeqComp? || S.IF? || S.DO? // replace with Core(S)
ensures setOf(X') <= glob(S')
ensures setOf(X) !! glob(S)
ensures Valid(S')
{
	match S {
		case Skip => Skip
		case Assignment(LHS, RHS) => 
			var LHS' := VSubstitute(LHS, X, X');
			var RHS' := ESeqSubstitute(RHS, X, X');
			Assignment(LHS', RHS');
		case SeqComp(S1, S2) => 
			var S1' := substitute(S1, X, X');
			var S2' := substitute(S2, X, X');
			SeqComp(S1', S2')
		case IF(B0, Sthen, Selse) => 
			var B' := BSubstitue(B0, X, X');
			var Sthen' := substitute(Sthen, X, X');
			var Selse' := substitute(Selse, X, X');
			IF(B', Sthen', Selse')
		case DO(B, S) => 
			var B' := BSubstitue(B, X, X');
			var S'' := substitute(S, X, X');
			DO(B', S'')

		case LocalDeclaration(L, S0) => Skip // S is Core Statement
		case Live(L, S0) => Skip // S is Core Statement
	}
}

function method {:verify true} VSubstitute(
	LHS: seq<Variable>,
	X: seq<Variable>,
	X': seq<Variable>): seq<Variable>
	requires |X| == |X'|
{
	if LHS == [] then []
	else
		[if LHS[0] in X
			then GetCorrespondingV(LHS[0], X, X');
			else LHS[0]] 
		 + VSubstitute(LHS[1..], X, X')
}

function method {:verify true} GetCorrespondingV(v: Variable, X: seq<Variable, X': seq<Variable): Variable
	requires v in X
	requires |X| == |X'|
{
	if v == X[0] then X'[0]
	else
		GetCorrespondingV(v, X[1..], X'[1..])
}

function method {:verify true} BSubstitue(
	B0: BooleanExpression,
	X: seq<Variable>,
	X': seq<Variable>) : BooleanExpression
{
	(state=>
		B0.0(map v | v in (B0.1-setOf(X)+setOf(X')) :: 
				(if v !in X' 
				then state[v] 
				else state[FindParallelV(v, X, X')])
			),
		B0.1-setOf(X)+setOf(X'))
}

function method {:verify true} ESubstitue(
	E: Expression,
	X: seq<Variable>,
	X': seq<Variable>) : (res:Expression)
requires |X| <= |X'|
ensures |E.1|==|res.1|
{
	(state=>
		E.0(map v | v in (E.1-setOf(X)+setOf(X')) :: 
				(if v !in X' 	
				then state[v] 
				else state[FindParallelV(v, X, X')])
			),
		E.1-setOf(X)+setOf(X'))
}

function method {:verify true} FindParallelV(v: Variable,
	X: seq<Variable>,
	X': seq<Variable>) : Variable
requires |X| > 0
requires |X'| > 0
requires |X| <= |X'|
requires v in X
{
	if v == X[0] then X'[0] else
	FindParallelV(v, X[1..], X'[1..])
}

function method {:verify true} ESeqSubstitute(
	Es : seq<Expression>,
	X: seq<Variable>,
	X': seq<Variable>) : (res : seq<Expression>)
requires |X| <= |X'|
{
	if Es == [] then []
	else
		[ESubstitue(Es[0], X, X')]+ESeqSubstitute(Es[1..], X, X')
}
