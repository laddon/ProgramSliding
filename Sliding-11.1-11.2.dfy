include "Sliding-8-9-10.dfy"

// Ch 11.2
method {:verify true} ComputePenlessCoSlice(
	S: Statement, 
	V: seq<Variable>, 
	Vr: seq<Variable>) 
returns (Scov: Statement) 
requires Vr != []
requires Vr <= V
requires Valid(S)
ensures Valid(Scov)
{
	//var fVr := Fresh(Vr, V+glob(S));
	var freshV := new Fresh();
	assert forall v :: v in Vr ==> v !in freshV.range by {
		assert freshV.range == {};
	}
	var fVr := freshV.CreateFresh(Vr, V+fSetToSeq(glob(S)));
	assert forall v :: v in glob(S) ==> v !in fVr by {
		assert forall v :: v in glob(S) ==> v in fSetToSeq(glob(S));
	}
	var S' := ComputeCoSlice(S, V, Vr, fVr/*, freshV*/);
	assert forall v :: v in glob(S') ==> v !in Vr;

	Scov := FinalUseSubstitution(S', fVr, Vr);
}

// Ch. 11.1 Refinement 11.1
lemma {:verify true} Refinement11_1(
	S: Statement, 
	Sv: Statement,
	Scov: Statement,
	Vr : seq<Variable>, 
	Vnr: seq<Variable>, 
	coV: seq<Variable>,
	iVr: seq<Variable>,
	iVnr: seq<Variable>,
	icoV: seq<Variable>,
	fVr: seq<Variable>,
	fVnr: seq<Variable>)
requires Valid(S)
requires Valid(Sv)
requires Valid(Scov)
requires 
	var S' := Live(Vr+Vnr, S);
	var Sv' := Live(Vr+Vnr, Sv);
	Refinment(S', Sv');
requires mutuallyDisjoint([Vr,Vnr,coV])
requires mutuallyDisjoint([iVr,iVnr,icoV,fVr,fVnr])
requires def(Sv) <= def(S);
requires def(Scov) <= def(S);
requires uniqueness(Vr);
requires uniqueness(Vnr);
requires uniqueness(iVr);
requires uniqueness(iVnr);
requires uniqueness(fVr);
requires uniqueness(fVnr);
requires uniqueness(coV);
requires uniqueness(icoV);
requires |Vr| == |fVr|
requires |Vnr| == |fVnr|
requires |iVr| == |Vr|
requires |iVnr| == |Vnr|
requires |icoV| == |coV|
requires forall v :: v in Vr ==> v !in fVr
requires forall v :: v in fVr ==> v !in glob(S)
ensures 
	var Vr1 := setOf(Vr)*input(Scov);
	var Vr2 := setOf(Vr)*(def(Scov)-input(Scov));
	var Vr3 := seqSubtraction(Vr, fSetToSeq(glob(Scov)));
	var iVr1 := setOf(iVr)*input(Scov);
	var iVr2 := setOf(iVr)*(def(Scov)-input(Scov));
	var iVr3 := setOf(iVr)-glob(Scov);
	var fVr1 := setOf(fVr)*input(Scov);
	var fVr2 := setOf(fVr)*(def(Scov)-input(Scov));
	var fVr3 := seqSubtraction(fVr,fSetToSeq(glob(Scov)));

	var Vnr1 := setOf(Vnr)*input(Scov);
	var Vnr2 := setOf(Vnr)*(def(Scov)-input(Scov));
	var Vnr3 := setOf(Vnr)-glob(Scov);
	var iVnr1 := setOf(iVnr)*input(Scov);
	var iVnr2 := setOf(iVnr)*(def(Scov)-input(Scov));
	var iVnr3 := setOf(iVnr)-glob(Scov);
	var fVnr1 := setOf(fVnr)*input(Scov);
	var fVnr2 := setOf(fVnr)*(def(Scov)-input(Scov));
	var fVnr3 := setOf(fVnr)-glob(Scov);
	
	var coV11 := setOf(coV)*def(Sv)*input(Scov);
	var coV12 := setOf(coV)*(input(Scov)-def(Sv));
	var coV2 := setOf(coV) - input(Scov);
	var icoV11 := setOf(icoV)*def(Sv)*input(Scov);
	var icoV12 := setOf(icoV)*(input(Scov)-def(Sv));
	var icoV2 := setOf(icoV) - input(Scov);

	
	assume |Vr3| == |fVr3|;
	var Scovsub := FinalUseSubstitution(Scov, Vr3, fVr3);
	assert def(Sv) <= def(S);
	assert def(Scov) <= def(S);

	var vars : seq<Variable> := fSetToSeq(Vr1+Vnr1+coV11);
	var ivars : seq<Variable> := fSetToSeq(iVr1+iVnr1+icoV11);
	var varsb : seq<Variable> := fSetToSeq(Vr1+Vr2+Vnr1+Vnr2);
	var fvars : seq<Variable> := fSetToSeq(fVr1+fVr2+fVnr1+fVnr2);
	var varse := seqVarToSeqExpr(vars);
	var ivarse := seqVarToSeqExpr(ivars);
	var varsbe := seqVarToSeqExpr(varsb);
	var fvarse := seqVarToSeqExpr(fvars);
	

	var	result := Live(Vr+Vnr+coV,
				SeqComp(Assignment(ivars, varse),
					SeqComp(Sv, 
						SeqComp(Assignment(fvars, varsbe),
							SeqComp(Assignment(vars, ivarse),
								SeqComp(Scov, Assignment(varsb, fvarse)))))));

/*	assume Valid(result);
	calc {
		|ivars|;
		== 
		|varse|;
		== 
		|vars|;
	}
	calc {
		|varsbe|; 
		== 
		|varsb|;
		== 
		|Vr1|+|Vr2|+|Vnr1|+|Vnr2|;
		==
		|fvars|;
	}*/
	Refinement(S, result)

