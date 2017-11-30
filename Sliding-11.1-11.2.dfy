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
	var freshV := new Fresh();
	assert forall v :: v in Vr ==> v !in freshV.range by {
		assert freshV.range == {};
	}
	var fVr := freshV.CreateFresh(Vr, V+fSetToSeq(glob(S)));
	assert forall v :: v in glob(S) ==> v !in fVr by {
		assert forall v :: v in glob(S) ==> v in fSetToSeq(glob(S));
	}
	var S' := ComputeCoSlice(S, V, Vr, fVr);
	assert mutuallyDisjoint([Vr, fSetToSeq(glob(S'))]);

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
requires |Vr|==|fVr|
requires |Vnr|==|fVnr|
requires |iVr|==|Vr|
requires |iVnr|==|Vnr|
requires |icoV|==|coV|
requires mutuallyDisjoint([fVr, fSetToSeq(glob(S))]);
requires mutuallyDisjoint([Vr,fVr])
requires mutuallyDisjoint([Vnr,fVnr])
requires Valid(S)
requires Valid(Sv)
requires Valid(Scov)
requires Core(Scov)
requires mutuallyDisjoint([Vr,Vnr,coV])
requires def(S) == setOf(Vr+Vnr+coV)
requires 
	var S' := Live(Vr+Vnr, S);
	var Sv' := Live(Vr+Vnr, Sv);
	Refinement(S', Sv');
requires 
	var Scov' := Live(coV, Scov);
	var S' := FinalUseSubstitution(S, Vr, fVr);
	Refinement(Live(coV, S'), Scov');
requires def(Sv) <= def(S);
requires def(Scov) <= def(S);
requires mutuallyDisjoint([iVr,iVnr,icoV,fVr,fVnr])
requires mutuallyDisjoint([iVr+iVnr+icoV+fVr+fVnr, fSetToSeq(glob(S))])
ensures 
	var Vr1 := seqConjunction(Vr, fSetToSeq(input(Scov)));
	var Vr2 := seqConjunction(Vr, fSetToSeq(def(Scov)-input(Scov)));
	var Vr3 := seqSubtraction(Vr, fSetToSeq(glob(Scov)));
	var iVr1 := corresponding(Vr, iVr, setOf(Vr1));//setOf(iVr)*input(Scov);
	var iVr2 := corresponding(Vr, iVr, setOf(Vr2));//setOf(iVr)*(def(Scov)-input(Scov));
	var iVr3 := corresponding(Vr, iVr, setOf(Vr3));//setOf(iVr)-glob(Scov);
	var fVr1 := corresponding(Vr, fVr, setOf(Vr1));//setOf(fVr)*input(Scov);
	var fVr2 := corresponding(Vr, fVr, setOf(Vr2));//setOf(fVr)*(def(Scov)-input(Scov));
	var fVr3 := corresponding(Vr, fVr, setOf(Vr3));//seqSubtraction(fVr,fSetToSeq(glob(Scov)));

	var Vnr1 := seqConjunction(Vnr, fSetToSeq(input(Scov)));
	var Vnr2 := seqConjunction(Vnr, fSetToSeq(def(Scov)-input(Scov)));
	var Vnr3 := seqSubtraction(Vnr, fSetToSeq(glob(Scov)));
	var iVnr1 := corresponding(Vnr, iVnr, setOf(Vnr1));//setOf(iVnr)*input(Scov);
	var iVnr2 := corresponding(Vnr, iVnr, setOf(Vnr2));//setOf(iVnr)*(def(Scov)-input(Scov));
	var iVnr3 := corresponding(Vnr, iVnr, setOf(Vnr3));//setOf(iVnr)-glob(Scov);
	var fVnr1 := corresponding(Vnr, fVnr, setOf(Vnr1));//setOf(fVnr)*input(Scov);
	var fVnr2 := corresponding(Vnr, fVnr, setOf(Vnr2));//setOf(fVnr)*(def(Scov)-input(Scov));
	var fVnr3 := corresponding(Vnr, fVnr, setOf(Vnr3));//setOf(fVnr)-glob(Scov);
	
	var coV11 := seqConjunction(coV, fSetToSeq(def(Sv)*input(Scov)));
	var coV12 := seqConjunction(coV, fSetToSeq(input(Scov)-def(Sv)));
	var coV2 := seqSubtraction(coV, fSetToSeq(input(Scov)));
	var icoV11 := corresponding(coV, icoV, setOf(coV11));//setOf(icoV)*def(Sv)*input(Scov);
	var icoV12 := corresponding(coV, icoV, setOf(coV12));//setOf(icoV)*(input(Scov)-def(Sv));
	var icoV2 := corresponding(coV, icoV, setOf(coV2));//setOf(icoV) - input(Scov);

	var sVr := setOf(Vr);
	var sfVr := setOf(fVr);
	var sVr3 := setOf(Vr3);
	var sfVr3 := setOf(fVr3);


	assert |fVr3| == |Vr3| by {
		assume |sVr3| == |Vr3|;
	}
	assert mutuallyDisjoint([Vr3, fVr3]) by {
		assert mutuallyDisjoint([Vr, fVr]);
		assert sfVr3 <= sfVr;
		assert sVr3 <= sVr;
		assume sVr3 !! sfVr3;//<<<
	}
	assume mutuallyDisjoint([Vr3, fSetToSeq(allVars(Scov))]);//<<<
	var Scovsub := substitute(Scov, fVr3, Vr3);

	var vars : seq<Variable> := Vr1+Vnr1+coV11;
	var ivars : seq<Variable> := iVr1+iVnr1+icoV11;
	var varsb : seq<Variable> := Vr1+Vr2+Vnr1+Vnr2;
	var fvars : seq<Variable> := fVr1+fVr2+fVnr1+fVnr2;
	var varse := seqVarToSeqExpr(vars);
	var ivarse := seqVarToSeqExpr(ivars);
	var varsbe := seqVarToSeqExpr(varsb);
	var fvarse := seqVarToSeqExpr(fvars);
	

	var	result := Live(Vr+Vnr+coV,
				SeqComp(Assignment(ivars, varse),
					SeqComp(Sv, 
						SeqComp(Assignment(fvars, varsbe),
							SeqComp(Assignment(vars, ivarse),
								SeqComp(Scovsub, Assignment(varsb, fvarse)))))));

	assert Valid(result);
	Refinement(S, result)

