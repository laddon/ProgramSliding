include "Util.dfy"
include "Definitions.dfy"
include "Substitutions.dfy"

/*
 * LHS: left-hand side of assignment statement
 * RHS: right-hand side of assignment statement
 * V: a set of variables that we want to search in LHS and construct
 *		the corresponding RHS
 * S': the returned assignment statement
 * Example: LHS:=[a,b,c], RHS:=[a+1, a+2, c+1], V:=[a,c]
 *		S' := Assignment([a,c], [a+1, c+1])
 * Note: order of elements of V is not important (can be a set)
 */
function method {:verify true} GetAssignmentsOfV(
	LHS: seq<Variable>, 
	RHS: seq<Expression>, 
	V: seq<Variable>) : (S': Statement)
requires |LHS| == |RHS|
ensures Valid(S')
ensures def(S')<=setOf(LHS)
{
	if LHS == [] || RHS == [] then 
		assert def(Skip) == {};
		Skip
	else if LHS[0] in V then 
		var tempRes := GetAssignmentsOfV(LHS[1..], RHS[1..], V);
		assert Valid(tempRes);
		assert def(tempRes) <= setOf(LHS);
		match tempRes {
			case Assignment(LHS1,RHS1) => 
				assert Valid(Assignment([LHS[0]]+LHS1, [RHS[0]]+RHS1));
				Assignment([LHS[0]]+LHS1, [RHS[0]]+RHS1)
			case Skip => 
				assert Valid(Assignment([LHS[0]], [RHS[0]]));
				Assignment([LHS[0]], [RHS[0]])
			case SeqComp(S1,S2) =>Skip
			case IF(B0, Sthen, Selse) => Skip
			case DO(B, S) => Skip
			case LocalDeclaration(L, S0) => Skip
			case Live(L, S0) => Skip
			case Assert(B) => Skip
		}
	else GetAssignmentsOfV(LHS[1..], RHS[1..], V)
}

/*
 * v: a variable for which we want its fresh one
 * SV: set of all variables for which we have fresh ones
 * fV: set of all fresh variable corresponding to those in SV
 * returns variable from fV corresponding to v
 */
function method GetFreshOfVariable(v: Variable, SV: seq<Variable>, fV: seq<Variable>)
: (res: Variable)
reads *
requires v in SV
requires v !in fV
requires |SV| == |fV|
ensures res in fV
{
	if (v == SV[0]) then fV[0]
	else
		GetFreshOfVariable(v, SV[1..], fV[1..])
}

/*
 * V: set of variables for which we want the fresh ones
 * SV: set of all variables for which we have fresh ones
 * fV: set of all fresh variable corresponding to those in SV
 * returns subset of fV corresponding to V
 */
function method GetFreshOfVars(V: seq<Variable>, SV: seq<Variable>, fV: seq<Variable>)
: (res: seq<Variable>)
reads *
requires forall v :: v in V ==> v in SV
requires forall v :: v in V ==> v !in fV
requires |SV| == |fV|
ensures |res| == |V|
ensures forall v :: v in res ==> v in fV
{
	if V == [] then []
	else
		var fv : Variable := GetFreshOfVariable(V[0], SV, fV);
		[fv] + GetFreshOfVars(V[1..], SV, fV)
}


// Ch. 10 Fig 10.1
/*
 * S: Core Statment
 * X: set of original variables in S to be substituted
 * X': fresh names for X
 */
function method {:verify true} FinalUseSubstitution(
	S: Statement, 
	X: seq<Variable>, 
	X': seq<Variable>) : (S' : Statement)
reads *
requires Valid(S)
requires |X| == |X'|
requires mutuallyDisjoint([X,X'])
requires mutuallyDisjoint([X', fSetToSeq(glob(S))])
ensures mutuallyDisjoint([X, fSetToSeq(glob(S'))])
ensures Valid(S')
{
	match S {
		case Skip => Skip
		case Assignment(LHS, RHS) => 
			var X1 := seqConjunction(X, LHS); // X*LHS
			var X2 := seqSubtraction(X, X1);  // X \ X1
			assert forall v :: v in X1 ==> v !in X';
			var X1' := GetFreshOfVars(X1, X, X'); 
			var X2' := GetFreshOfVars(X2, X, X');
			var Y := seqSubtraction(LHS,X1); // LHS \ X1
			assert |LHS|==|X1|+|Y| by {
				assert forall v :: v in X1 ==> v in LHS;
				assert forall v :: v in Y ==> v in LHS;
				assert forall v :: v in Y ==> v !in X1;
				assert forall v :: v in X1 ==> v !in Y;
				assert forall v :: v in LHS ==> (v in Y ) || (v in X1);
			}
			var A1 := GetAssignmentsOfV(LHS, RHS, X1);
			var A2 := GetAssignmentsOfV(LHS, RHS, Y);
			if (A1.Assignment? && A2.Assignment?) then
				var E1 := A1.RHS; 
				var E2 := A2.RHS;
				assert forall v :: v in X2 ==> v !in X';
				var E1' := ESeqSubstitute(E1, X2, X2');
				var E2' := ESeqSubstitute(E2, X2, X2');
				assert forall v :: v in X ==> v !in (X1'+Y);
//				assert forall v :: v in X ==> v !in varsInExps(E1');
//				assert forall v :: v in X ==> v !in varsInExps(E2');
				Assignment(X1'+Y, E1'+E2')// build sequence in right order
			else
				Skip
		case SeqComp(S1, S2) => 
			var X1 := seqConjunction(X, fSetToSeq(def(S2)));
			var X2 := seqSubtraction(X,X1);
			var X2' := GetFreshOfVars(X2, X, X');
			
			assert glob(S1)+glob(S2) <= glob(S) by {
				globOf2PartialSPartialToGlobSLemma(S, S1, S2);
			}
			
			var S1' := FinalUseSubstitution(S1, X2, X2');
			var S2' := FinalUseSubstitution(S2, X, X');
			SeqComp(S1', S2')
		case IF(B0, Sthen, Selse) => 
			var X1 := seqConjunction(X, fSetToSeq(def(Sthen)+def(Selse)));
			var X2 := seqSubtraction(X,X1);
			var X2' := GetFreshOfVars(X2, X, X');
			var B' := BSubstitute(B0, X2, X2');
			var Sthen' := FinalUseSubstitution(Sthen, X, X');
			var Selse' := FinalUseSubstitution(Selse, X, X');
			IF(B', Sthen', Selse')
		case DO(B, S) => 
			var X1 := seqConjunction(X, fSetToSeq(def(S)));
			var X2 := seqSubtraction(X,X1);
			var X2' := GetFreshOfVars(X2, X, X');
			var B' := BSubstitute(B, X2, X2');
			var S'' := FinalUseSubstitution(S, X2, X2');
			DO(B', S'')

		case LocalDeclaration(L, S0) => Skip // S is Core Statement
		case Live(L, S0) => Skip // S is Core Statement
		case Assert(B) => Skip
	}
}

/*
 * S' <= S ==> glob(S') <= glob(S)
 */
lemma globOfPartialSPartialToGlobSLemma(S: Statement, S': Statement)
requires Valid(S) && Valid(S')
ensures glob(S') <= glob(S)

/*
 * S1 <= S && S2 <= S && S1+S2==S ==> glob(S1) <= glob(S) && glob(S2) <= glob(S) && glob(S1)+glob(S2) <= glob(S)
 */
lemma globOf2PartialSPartialToGlobSLemma(S: Statement, S1: Statement, S2: Statement)
requires Valid(S) && Valid(S1) && Valid(S2)
requires S.SeqComp? == true
ensures glob(S1) <= glob(S) && glob(S2) <= glob(S)
ensures glob(S1)+glob(S2) <= glob(S)

/*
 * S' <= S ==> def(S') <= def(S)
 */
lemma defOfPratialSPartialToDefSLemma(S: Statement, S': Statement)
requires Valid(S) && Valid(S')
ensures def(S') <= def(S)

