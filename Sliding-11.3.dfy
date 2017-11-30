include "Sliding-11.1-11.2.dfy"

// Ch 11.3, Transformation 11.2
method {:verify true} Sliding_PenlessCoSlice(
	S: Statement, 
	Vr: seq<Variable>, 
	Vnr: seq<Variable>) 
returns (result: Statement, Sv: Statement, Scov: Statement)
requires Valid(S)
requires setOf(Vr) !! setOf(Vnr) 
/*requires 
	var Vr' := seqConjunction(Vr, fSetToSeq(def(S)));
	var Vnr' := seqConjunction(Vnr, fSetToSeq(def(S)));
	var freshV := new Fresh();
	var fVr := freshV.CreateFresh(Vr', Vr+Vnr+fSetToSeq(glob(S)));	
	setOf(Vr') !! glob(ComputeCoSlice(S, Vr'+Vnr', Vr', fVr))*/
ensures Valid(result)
ensures Refinement(S, result)
{
	var freshV := new Fresh();

	var Vr' := seqConjunction(Vr, fSetToSeq(def(S)));//Vr*def(S); 
	var Vnr' := seqConjunction(Vnr, fSetToSeq(def(S)));//Vnr*def(S);
	var coV := seqSubtraction(fSetToSeq(def(S)),(Vr'+Vnr'));//def(S)-(Vr'+Vnr')

	Sv := ComputeSlice(S, setOf(Vr'+Vnr'));
	Scov := ComputePenlessCoSlice(S, Vr'+Vnr', Vr');

	var Vnr1 := seqConjunction(Vnr',fSetToSeq(input(Scov)));//Vnr'*input(Scov)
	var Vnr2 := seqConjunction(Vnr',fSetToSeq(def(Scov)-input(Scov)));//Vnr'*(def(Scov)-input(Scov))
	var coV11 := seqConjunction(coV,fSetToSeq(def(Sv)*input(Scov)));//coV*def(Sv)*input(Scov)

	var iVr := freshV.CreateFresh(Vr', Vr+Vnr+fSetToSeq(glob(S)));
	var iVnr := freshV.CreateFresh(Vnr', Vr+Vnr+fSetToSeq(glob(S)));
	var icoV := freshV.CreateFresh(coV, Vr+Vnr+fSetToSeq(glob(S)));
	var fVnr := freshV.CreateFresh(Vnr', Vr+Vnr+fSetToSeq(glob(S)));

	
	var iVnr1 := freshV.CreateFresh(Vnr1, Vr+Vnr+fSetToSeq(glob(S)));
	var icoV11 := freshV.CreateFresh(coV11, Vr+Vnr+fSetToSeq(glob(S)));
	var fVnr1 := freshV.CreateFresh(Vnr1, Vr+Vnr+fSetToSeq(glob(S)));
	var fVnr2 := freshV.CreateFresh(Vnr2, Vr+Vnr+fSetToSeq(glob(S)));

	var decl : seq<Variable> := iVnr1+icoV11+fVnr1+fVnr2;
	var ivars : seq<Variable> := iVnr1+icoV11;
	var vars : seq<Variable> := Vnr1+coV11;
	var vnrs : seq<Variable> := Vnr1+Vnr2;
	var fvars : seq<Variable> := fVnr1+fVnr2;

	var varse := seqVarToSeqExpr(vars);
	var vnrse := seqVarToSeqExpr(vnrs);
	var ivarse := seqVarToSeqExpr(ivars);
	var fvarse := seqVarToSeqExpr(fvars);
	var S' := SeqComp(Assignment(ivars, varse),
				 SeqComp(Sv, 
				  SeqComp(Assignment(fvars, vnrse),
				   SeqComp(Assignment(vars, ivarse),
				    SeqComp(Scov, Assignment(vnrs, fvarse))))));
	result := LocalDeclaration(decl,S');
	assert Valid(result); 
	
	var S'' := Live(Vr'+Vnr'+coV,S');
//	assert Refinement(S, S'');
//   forall P: Predicate,s: State :: (wp(S1,P).0.requires(s) && wp(S2,P).0.requires(s) && wp(S1,P).0(s) ==> wp(S2,P).0(s))

	forall P: Predicate,s: State {
		calc {
			wp(S,P).0(s);
			==> {Refinement11_1(S, Sv, Scov,
								Vr', 
								Vnr', 
								coV,
								iVr,
								iVnr,
								icoV,
								fVr,
								fVnr);
			}
			wp(S'',P).0(s);
			== {}
			wp(result,P).0(s);
		}
	}
}
