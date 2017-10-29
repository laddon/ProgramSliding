include "FinalUseSubstitution.dfy"
include "SliceRefinements.dfy"
include "Fresh.dfy"

//include "SSA.dfy"
/* TODO:
 * Prove SliceRefinement
 * Prove CoSliceRefinement
 * Prove Refinement by above + Corollary5_4_Lemma
 */
// Ch. 8 Fig 8.1
function method {:verify true} ComputeSlides(S: Statement, V: seq<Variable>) : (S': Statement)
reads *
requires Valid(S)
ensures Valid(S')
{
	if setOf(V)*def(S) == {} then Skip
	else
	match S {
		case Skip => Skip
		case Assignment(LHS, RHS) => GetAssignmentsOfV(LHS, RHS, V)
		case SeqComp(S1, S2) => SeqComp(ComputeSlides(S1,V), ComputeSlides(S2,V))
		case IF(B0, Sthen, Selse) => IF(B0, ComputeSlides(Sthen, V), ComputeSlides(Selse, V))
		case DO(B, S) => DO(B, ComputeSlides(S, V))
		case LocalDeclaration(L, S0) => ComputeSlides(S0, V)
		case Live(L, S0) => ComputeSlides(S0, V)
	}
}

// Ch. 9 Fig 9.1
function method {:verify true} ComputeSlidesDepRtc(S: Statement, V: set<Variable>) 
	: (V': set<Variable>)
reads *
requires Valid(S)
ensures V <= V'
decreases glob(S)-V
{
	var slidesSv := ComputeSlides(S, fSetToSeq(V));
	var U := glob(slidesSv)*def(S);

	if U <= V then V else ComputeSlidesDepRtc(S, V+U)
}

// Ch. 9 Fig 9.1
method {:verify true} ComputeSlice(S: Statement, V: set<Variable>) 
returns (Sv: Statement)
requires Valid(S) 
//ensures Refinement(Live(fSetToSeq(V), S), Live(fSetToSeq(V), Sv))
ensures def(Sv)<=def(S)
ensures glob(Sv)<=glob(S)
ensures Valid(Sv)
{
	var Vstar := ComputeSlidesDepRtc(S, V);
	Sv := ComputeSlides(S, fSetToSeq(Vstar));
	assert Valid(Sv);
	assert def(Sv)<=def(S) by {defOfPratialSPartialToDefSLemma(S, Sv);}
	assert glob(Sv)<=glob(S) by {globOfPartialSPartialToGlobSLemma(S, Sv);}
}

// Ch. 10 Fig 10.2
method {:verify true} ComputeCoSlice(
	S: Statement, 
	V: seq<Variable>, 
	Vr: seq<Variable>, 
	fVr: seq<Variable>) 
returns (Scov: Statement)
requires Valid(S)
requires Vr <= V
requires |Vr| == |fVr|
requires forall v :: v in V ==> v !in fVr
requires forall v :: v in glob(S) ==> v !in fVr
requires forall v :: v in fVr ==> v !in V
requires forall v :: v in fVr ==> v !in glob(S)
ensures Valid(Scov)
ensures forall v :: v in Vr ==> v !in glob(Scov)
ensures forall v :: v in glob(Scov) ==> v !in Vr
{
	var coV := def(S) - setOf(V);
	var S' := FinalUseSubstitution(S, Vr, fVr);
	Scov := ComputeSlice(S', coV);
	assert forall v :: v in Vr ==> v !in glob(Scov) by {
		assert Vr <= V;
		assert forall v :: v in coV ==> v !in Vr;
		assert forall v :: v in Vr ==> v !in coV;
		assert forall v :: v in Vr ==> v !in glob(S');
		assert forall v :: v in glob(S') ==> v !in Vr;
		assert glob(Scov) <= glob(S');
	}
}

