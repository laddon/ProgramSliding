include "Definitions.dfy"
include "Substitutions.dfy"
include "Util.dfy"
include "CorrectnessSSA.dfy"
include "SlideDG.dfy"
include "VarSlideDG.dfy"
include "SSA.dfy"
include "Slicing.dfy"

function {:verify true}SliceOf(S: Statement, V: set<Variable>): (set<Slide>, Statement)
	reads *
	requires Valid(S) && Core(S)
	ensures forall Sm :: Sm in SliceOf(S,V).0 <==> (Sm in slidesOf(S,def(S)) && exists Sn :: Sn in finalDefSlides(S, SlideDGOf(S, CFGOf(S)), CFGOf(S), V) && SlideDGReachable(SlideDGOf(S, CFGOf(S)), Sm, Sn, SlideDGOf(S, CFGOf(S)).1))
	ensures Valid(SliceOf(S,V).1) && Core(SliceOf(S,V).1)
{
	var cfg := ComputeCFG(S);
	assert cfg == CFGOf(S);
	var slideDG := SlideDGOf(S, cfg);
	var slidesSV := set Sm | (Sm in slidesOf(S,def(S)) && exists Sn :: Sn in finalDefSlides(S, slideDG, cfg, V) && SlideDGReachable(slideDG, Sm, Sn, slideDG.1));

	(slidesSV, statementOf(slidesSV, S))
}

method {:verify true}SSASlice(S: Statement, V: set<Variable>) returns (res: Statement)
	requires Valid(S)
	requires Core(S)
	decreases *
	ensures SliceOf(S,V).1 == res 
{
	var varSlideDG := ComputeVarSlideDG(S); // not needed

	res := ComputeSSASlice(S, V, varSlideDG);
}

method {:verify true}ComputeSSASlice(S: Statement, V: set<Variable>, ghost varSlideDG: VarSlideDG) returns (res: Statement)
	//requires NoSelfAssignments(S) // requires there are no self assignments TODO
	requires Valid(S) && Core(S)
	requires VarSlideDGOf(varSlideDG, S)
	decreases *
	ensures Valid(res) && Core(res)
	ensures var varSlidesRes: set<VarSlide> := varSlidesOf(res, V); forall Sm :: Sm in varSlidesRes <==> (Sm.0 in V || (exists Sn: VarSlide :: Sn.0 in V && VarSlideDGReachable(varSlideDG, Sm, Sn, varSlideDG.1)))	 // Implement VarSlideDGReachable
	//ensures var SV := SliceOf(S,V); MergeVars(SV) == res 
	ensures SliceOf(S,V).1 == res
{
	// To SSA
	var vsSSA := new VariablesSSA(); 
	var Xset := def(S);
	var X := setToSeq(Xset);
	var Y := {};
	var liveOnEntryXSeq := freshInit(X, {}, vsSSA);
	var liveOnEntryX := setOf(liveOnEntryXSeq);
	var liveOnExitXSeq := freshInit(X, glob(S) + liveOnEntryX, vsSSA);
	var liveOnExitX := setOf(liveOnExitXSeq);
	var XLs := liveOnEntryX + liveOnExitX;
	assume forall i :: i in liveOnEntryX ==> vsSSA.existsVariable2(i);
	assume forall i :: i in liveOnExitX ==> vsSSA.existsVariable2(i);
	assume forall v :: v in X ==> vsSSA.existsInstance(v);
	var S' := ToSSA(S, X, liveOnEntryX, liveOnExitX, Y, XLs, vsSSA);
	assert Valid(S) && Core(S);

	// Create varSlideDGS' for S'
	ghost var varSlideDGS' := ComputeVarSlideDG(S');
	assert VarSlideDGOf(varSlideDGS', S');

	// V' := foreach v in V find liveOnExit v
	var VSeq := setToSeq(V);
	assume forall v :: v in VSeq ==> vsSSA.existsInstance(v);
	var instancesOfVSeq := vsSSA.getInstancesOfVaribleSeq(VSeq);
	var V' := setOf(instancesOfVSeq) * liveOnExitX;
	assert Valid(S) && Core(S);

	// Flow-Insensitive Slice
	var SV' := ComputeFISlice(S', V', varSlideDGS');
	ghost var varSlidesSV: set<VarSlide> := varSlidesOf(SV', V');
	//assert forall Sm :: Sm in varSlidesSV <==> (exists Sn: VarSlide :: Sn.0 in V' && VarSlideDGReachable(varSlideDGS', Sm, Sn, varSlideDGS'.1));	 // Implement VarSlideDGReachable
	assert forall vSlide :: vSlide in varSlidesSV ==> (vSlide in varSlidesOf(S,def(S)) && exists Sn: VarSlide :: Sn.0 in V' && VarSlideDGReachable(varSlideDGS', vSlide, Sn, varSlideDGS'.1));
	
	assert Valid(S) && Core(S);
	ghost var allSlides := slidesOf(S,def(S));
	//ghost var SV := SliceOf(S,V);
	ghost var SliceOfSV := SliceOf(S,V);
	ghost var SV := SliceOfSV.1;
	assert Valid(SV) && Core(SV); 
	//ghost var slidesSV := slidesOf(SV,V);
	ghost var slidesSV := SliceOfSV.0;
	assert forall Sm :: Sm in slidesSV <==> (Sm in slidesOf(S,def(S)) && exists Sn :: Sn in finalDefSlides(S, SlideDGOf(S, CFGOf(S)), CFGOf(S), V) && SlideDGReachable(SlideDGOf(S, CFGOf(S)), Sm, Sn, SlideDGOf(S, CFGOf(S)).1));
	assume slidesSV <= allSlides;
	
	LemmaSlidesSVToVarSlidesSV(S, SV, SV', slidesSV, varSlidesSV, X, V, V', varSlideDGS', vsSSA);
	assert forall slide :: slide in SlideDGOf(S, CFGOf(S)).1 ==> (slide in slidesSV <==> VarSlideOf(SV, SV', slide) in varSlidesSV);
	
	// From SSA
	var XL1i := liveOnEntryXSeq;
	var XL2f := liveOnExitXSeq;
	res := FromSSA(SV', X, XL1i, XL2f, Y, XLs, vsSSA, V, S', V', varSlideDGS');
	assert Substatement(res,S);
	
	//assert forall U: set<Variable> :: slidesOf(res, U) <= slidesOf(S, U) <= slidesOf(S, def(S));


	assert Substatement(res, S);
	assert Substatement(SliceOfSV.1, S);
	
	assume def(res) <= def(S);// by { assert Core(S) && Substatement(res,S); }
	assert allSlidesOf(res) == slidesOf(res, def(S));
	assume def(SliceOfSV.1) <= def(S);// by { assert Core(S) && Substatement(SliceOfSV,S); }
	assert allSlidesOf(SliceOfSV.1) == slidesOf(SliceOfSV.1, def(S));

	assert slidesOf(res, def(S)) <= slidesOf(S, def(S));
	assert slidesSV == slidesOf(SliceOfSV.1, def(S)) == SliceOfSV.0 <= slidesOf(S, def(S));

	assert slidesOf(res, def(S)) == slidesOf(SliceOfSV.1, def(S)) by {
		forall slide | slide in slidesOf(S, def(S)) ensures slide in slidesOf(res, def(S)) <==> slide in slidesOf(SliceOfSV.1, def(S)) {
			assert VarSlideOf(SV, SV', slide) in varSlidesSV <==> slide in slidesOf(res, def(S)) by {
				assert forall slide :: slide in SlideDGOf(S, CFGOf(S)).1 ==> (slide in slidesSV <==> VarSlideOf(SV, SV', slide) in varSlidesSV);
				assert VarSlideOf(SV, SV', slide) in varSlidesSV ==> slide in slidesOf(res, def(S)) by {
					assert slide in slidesOf(S, def(S));
					assert slide in slidesSV by { assert slide in slidesSV <==> VarSlideOf(SV, SV', slide) in varSlidesSV; }
					assert forall vSlide :: vSlide in varSlidesSV ==> (vSlide in varSlidesOf(S,def(S)) && exists Sn: VarSlide :: Sn.0 in V' && VarSlideDGReachable(varSlideDGS', vSlide, Sn, varSlideDGS'.1));
					var vSlide := VarSlideOf(SV, SV', slide);
					assert vSlide in varSlidesOf(S,def(S)) && exists Sn: VarSlide :: Sn.0 in V' && VarSlideDGReachable(varSlideDGS', vSlide, Sn, varSlideDGS'.1);
					
					var v := slide.1;
					match slide.0 {
					case Node(l) => 
						var vLabel := VarLabelOf(SV, SV', l);
						assert ValidLabel(l, res) && IsAssignment(slipOf(res, l)) && v in def(slipOf(res, l)) by {
							assert ValidLabel(l, res) by {
								assert Substatement(res, S);
								assert ValidLabel(l, S) by { assert slide in slidesOf(S, def(S)); }

							}
							assert IsAssignment(slipOf(res, l)) by {
								assert IsAssignment(slipOf(SV', vLabel));
								assert MatchingSlipsFromSSA(SV', vLabel, res, l);
							}
							assert v in def(slipOf(res, l)) by {
								assert Substatement(res, S);
								// vLabel of Regular Assignment (vSlide), v' in LHS of vSlide <==> Rename(v') in def(slipOf(res, l))
								// vSlide.1 == Regular && v' in def(slipOf(SV', vLabel) <==> Rename(v') in def(slipOf(res, l))
								// call lemma for:
								// forall l,l',v,v' :: ValidLabel(l, S) && IsAssignment(slipOf(S, l)) && l' corresponding to l (function) && 
								//		ValidLabel(l', SV') && IsAssignment(slipOf(SV', l')) && v == Rename(v') ==>
								//		ValidLabel(l, res) && IsAssignment(slipOf(res, l)) &&
								//		(v in def(slipOf(res, l)) <==> v' in def(slipOf(SV', l')))
								//
							}
						}
					}
				}

				assert VarSlideOf(SV, SV', slide) !in varSlidesSV ==> slide !in slidesOf(res, def(S)) by {
					assert slide in slidesOf(S, def(S));
					assert slide !in slidesSV by { assert slide in slidesSV <==> VarSlideOf(SV, SV', slide) in varSlidesSV; }
					var vSlide := VarSlideOf(SV, SV', slide);
					assert !(vSlide in varSlidesOf(S,def(S)) && exists Sn: VarSlide :: Sn.0 in V' && VarSlideDGReachable(varSlideDGS', vSlide, Sn, varSlideDGS'.1)) by {
						assert forall vSlide :: vSlide in varSlidesSV ==> (vSlide in varSlidesOf(S,def(S)) && exists Sn: VarSlide :: Sn.0 in V' && VarSlideDGReachable(varSlideDGS', vSlide, Sn, varSlideDGS'.1));
						assert vSlide !in varSlidesSV;
					}
					
					assert slide !in slidesOf(res, def(S)) by {
						calc {
							slide in slidesOf(res, def(S));
						==> { assert slidesOf(res, def(S)) <= slidesOf(S, def(S)); }
							slide in slidesOf(S, def(S));
						==>
							
						==>
							slide in slidesOf(S,def(S)) && exists Sn :: Sn in finalDefSlides(S, slideDG, cfg, V) && SlideDGReachable(slideDG, slide, Sn, slideDG.1);
						==> { assert slide in slidesSV <==> VarSlideOf(SV, SV', slide) in varSlidesSV; }
							vSlide in varSlidesOf(S,def(S)) && exists Sn: VarSlide :: Sn.0 in V' && VarSlideDGReachable(varSlideDGS', vSlide, Sn, varSlideDGS'.1);
						==> { assert vSlide !in varSlidesSV; }
							false;
						}
					}
				} 
			}
		}
	}

	
	
	// Done. Now the proof:
	// ensures SliceOfSV == res :
	assume forall Sm :: Sm in slidesSV <==> (Sm in slidesOf(S,def(S)) && exists Sn :: Sn in finalDefSlides(S, SlideDGOf(S, CFGOf(S)), CFGOf(S), V) && SlideDGReachable(SlideDGOf(S, CFGOf(S)), Sm, Sn, SlideDGOf(S, CFGOf(S)).1));
	assume forall vSlide :: vSlide in varSlidesSV ==> (vSlide in varSlidesOf(S,def(S)) && exists Sn: VarSlide :: Sn.0 in V' && VarSlideDGReachable(varSlideDGS', vSlide, Sn, varSlideDGS'.1));
	LemmaSlidesSVToVarSlidesSV(S, SV, SV', slidesSV, varSlidesSV, X, V, V', varSlideDGS', vsSSA);
	assert forall slide :: slide in SlideDGOf(S, CFGOf(S)).1 ==> (VarSlideOf(SV, SV', slide) in varSlidesSV <==> slide in slidesOf(res, def(S)));
	L9(S, V, res, SV, SV', slidesSV, varSlidesSV, varSlideDGS', V'); // ensures allSlidesOf(SliceOfSV) == allSlidesOf(res)
	
	assert allSlidesOf(res) == allSlidesOf(SliceOfSV.1);
	LemmaIdenticalSlices(S, SliceOfSV.1, res);
}

lemma LemmaIdenticalSlices(S: Statement, S1: Statement, S2: Statement)
	requires Valid(S) && Valid(S1) && Valid(S2)
	requires Core(S) && Core(S1) && Core(S2)
	//requires Substatement(S1, S)
	//requires Substatement(S2, S)
	requires allSlidesOf(S1) == allSlidesOf(S2) // check multiple assignments
	ensures S1 == S2


/*lemma {:verify false}L10(SliceOfSV: Statement, res: Statement, l: Label/*, SV: Statement, SV': Statement, slidesSV: set<Slide>, varSlidesSV: set<VarSlide>*/)
	requires allLabelsOf(SliceOfSV) == allLabelsOf(res)
	requires l in allLabelsOf(SliceOfSV)
	ensures slipOf(SliceOfSV, l) == slipOf(res, l)
{
	var A := slipOf(SliceOfSV, l);
	assert A == Substatement(slipOf(S,l));
	var B := slipOf(res, l);
	assert B == Substatement(slipOf(S,l));
	L11(A, B);
}*/

/*	requires Substatement(S1, S) 
	requires Substatement(S2, S)
	ensures S1 == S2 <==> slidesOf(S1) == slidesOf(S2)*/

lemma {:verify false}L10(S: Statement, SliceOfSV: Statement, res: Statement, l: Label, v: Variable/*, SV: Statement, SV': Statement, slidesSV: set<Slide>, varSlidesSV: set<VarSlide>*/)
	requires exists exp :: slipOf(SliceOfSV, l) == Assignment([v], [exp])
	requires exists exp :: slipOf(res, l) == Assignment([v], [exp])
	requires allLabelsOf(SliceOfSV) == allLabelsOf(res)
	requires Substatement(res, S) 
	requires Substatement(SliceOfSV, S) 
	requires l in allLabelsOf(SliceOfSV)
	ensures slipOf(SliceOfSV, l) == slipOf(res, l)
{
	var A := slipOf(SliceOfSV, l);
	assert Substatement(A,S);
	var B := slipOf(res, l);
	assert Substatement(B,S);
	L11(A, B, S, l, SliceOfSV, res);
}
/*
S:
x,y := 1,2;

slides:
x,  := 1, ;
 ,y :=  ,2;

substatements:
x := 1;

y := 2;

x,y := 1,2;

[]

*/
lemma {:verify false}L11(A: Statement, B: Statement, S: Statement, l: Label, SliceOfSV: Statement, res: Statement)
	requires allLabelsOf(SliceOfSV) == allLabelsOf(res)
	requires Substatement(res, S) 
	requires Substatement(SliceOfSV, S) 
	requires ValidLabel(l, S)
	requires l in allLabelsOf(SliceOfSV)
	requires A == slipOf(SliceOfSV, l)
	requires B == slipOf(res, l)
	requires Valid(A) && Core(A)
	requires Valid(B) && Core(B)
	decreases A
	decreases B
	ensures A == B
{
	match A {
		case Assignment(LHS,RHS) =>	match B {
										case Assignment(LHS',RHS') =>	assert EqualAssignments(LHS, RHS, LHS', RHS');
																		assert Assignment(LHS,RHS) == Assignment(LHS',RHS');
										case SeqComp(S1',S2') =>		assert false;
										case IF(B0',Sthen',Selse') =>	assert false;
										case DO(B',S1') =>				assert false;
										case Skip =>					assert false;
									}	
		case SeqComp(S1,S2) =>		match B {
										case Assignment(LHS',RHS') =>	assert false;
										case SeqComp(S1',S2') =>		assert S1 < A; assert S2 < A; assert S1' < B; assert S2' < B; // for termination
																		//L11(S1, S1'); L11(S2, S2');
										case IF(B0',Sthen',Selse') =>	assert false;
										case DO(B',S1') =>				assert false;
										case Skip =>					assert false;	
									}	
		case IF(B0,Sthen,Selse) =>	match B {
										case Assignment(LHS',RHS') =>	assert false;
										case SeqComp(S1',S2') =>		assert false;
										case IF(B0',Sthen',Selse') =>	assert Sthen < A; assert Selse < A; assert Sthen' < B; assert Selse' < B; // for termination
																		assert EqualBooleanExpressions(B0, B0'); //L11(Sthen, Sthen'); L11(Selse, Selse');
										case DO(B',S1') =>				assert false;
										case Skip =>					assert false;
									}	
		case DO(B0,S1) =>			match B {
										case Assignment(LHS',RHS') =>	assert false;
										case SeqComp(S1',S2') =>		assert false;
										case IF(B0',Sthen',Selse') =>	assert false;	
										case DO(B0',S1') =>				assert S1 < A; assert S1' < B; // for termination
																		assert EqualBooleanExpressions(B0, B0'); //L11(S1, S1');
										case Skip =>					assert false;
									}	
		case Skip =>				assert B == Skip;	
	}	
}


predicate {:verify true}EqualAssignments(LHS: seq<Variable>, RHS: seq<Expression>, LHS': seq<Variable>, RHS': seq<Expression>)
	requires |LHS| == |RHS|
	requires |LHS'| == |RHS'|
{
	LHS == LHS' && RHS == RHS'

	/*if |LHS| == |LHS'| == 0 then true
	else if |LHS| != |LHS'| then false
	else if LHS[0] != LHS'[0] ||  RHS[0] != RHS'[0] then false
	else EqualAssignments(LHS[1..], RHS[1..], LHS'[1..], RHS'[1..])*/
}

predicate {:verify true}EqualBooleanExpressions(B: BooleanExpression, B': BooleanExpression)
	reads *
{
	EquivalentBooleanExpressions(B, B')
}

function {:verify false}allLabelsOf(S: Statement): set<Label>
{
	allLabelsOfStatement(S, [])
}

function {:verify false}allLabelsOfStatement(S: Statement, l: Label): set<Label>
{
	match S {
		case Assignment(LHS,RHS) => {l}
		case SeqComp(S1,S2) =>		{l} + allLabelsOfStatement(S1, l+[1]) + allLabelsOfStatement(S2, l+[2])
		case IF(B0,Sthen,Selse) =>	{l} + allLabelsOfStatement(Sthen, l+[1]) + allLabelsOfStatement(Selse, l+[2])
		case DO(B,S1) =>			{l} + allLabelsOfStatement(S1, l+[1])
		case Skip =>				{l}
	}	
}

lemma {:verify false}L9(S: Statement, V: set<Variable>, res: Statement, SV: Statement, SV': Statement, slidesSV: set<Slide>, varSlidesSV: set<VarSlide>, varSlideDG: VarSlideDG, V': set<Variable>)
	//requires NoSelfAssignments(S)
	requires Valid(S) && Core(S)
	requires Valid(SV) && Core(SV)
	requires Valid(SV') && Core(SV')
	requires forall Sm :: Sm in slidesSV <==> (Sm in slidesOf(S,def(S)) && exists Sn :: Sn in finalDefSlides(S, SlideDGOf(S, CFGOf(S)), CFGOf(S), V) && SlideDGReachable(SlideDGOf(S, CFGOf(S)), Sm, Sn, SlideDGOf(S, CFGOf(S)).1))
	requires forall vSlide :: vSlide in varSlidesSV ==> (vSlide in varSlidesOf(S,def(S)) && exists Sn: VarSlide :: Sn.0 in V' && VarSlideDGReachable(varSlideDG, vSlide, Sn, varSlideDG.1))
	requires forall slide :: slide in SlideDGOf(S, CFGOf(S)).1 ==> (slide in slidesSV <==> VarSlideOf(SV, SV', slide) in varSlidesSV)
	requires forall slide :: slide in SlideDGOf(S, CFGOf(S)).1 ==> (VarSlideOf(SV, SV', slide) in varSlidesSV <==> slide in slidesOf(res, def(S)))
	ensures allSlidesOf(SliceOf(S,V).1) == allSlidesOf(res)


function {:verify true}slipOf(S: Statement, l: Label): Statement
	reads *
	requires Valid(S) && Core(S)
	requires ValidLabel(l, S)
	ensures Valid(slipOf(S, l)) && Core(slipOf(S, l))
	ensures l == [] ==> slipOf(S, l) == S
	ensures l != [] ==> slipOf(S, l) < S
	decreases l
{
	if l == [] then  S
	else
		match S {
			case Assignment(LHS,RHS) => Skip//assert false - Doesn't work!!!
			case SeqComp(S1,S2) =>		if l[0] == 1 then slipOf(S1, l[1..]) else slipOf(S2, l[1..])
			case IF(B0,Sthen,Selse) =>	if l[0] == 1 then slipOf(Sthen, l[1..]) else slipOf(Selse, l[1..])
			case DO(B,S1) =>			slipOf(S1, l[1..])
			case Skip =>				Skip//assert false - Doesn't work!!!
		}
}


/*lemma {:verify false}L8(slidesSV: set<Slide>, SV: Statement, SV': Statement)
	ensures forall slide :: slide in slidesSV ==> var varSlide := VarSlideOf(SV, SV', slide); var s' := varStatementOf({varSlide}, SV'); slideOf(FromSSA(s')) == slide
*/

lemma LemmaSlidesSVToVarSlidesSV(S: Statement, SV: Statement, SV': Statement, slidesSV: set<Slide>, varSlidesSV: set<VarSlide>, X: seq<Variable>, V: set<Variable>, V': set<Variable>, varSlideDGS': VarSlideDG, vsSSA: VariablesSSA)
	requires Valid(S) && Core(S)
	requires Valid(SV) && Core(SV)
	requires Valid(SV') && Core(SV')
	requires ValidVsSSA(vsSSA)
	requires forall Sm :: Sm in slidesSV <==> (Sm in slidesOf(S,def(S)) && exists Sn :: Sn in finalDefSlides(S, SlideDGOf(S, CFGOf(S)), CFGOf(S), V) && SlideDGReachable(SlideDGOf(S, CFGOf(S)), Sm, Sn, SlideDGOf(S, CFGOf(S)).1));
	requires forall vSlide :: vSlide in varSlidesSV ==> (vSlide in varSlidesOf(S,def(S)) && exists Sn: VarSlide :: Sn.0 in V' && VarSlideDGReachable(varSlideDGS', vSlide, Sn, varSlideDGS'.1))
	ensures forall slide :: slide in SlideDGOf(S, CFGOf(S)).1 ==> (slide in slidesSV <==> VarSlideOf(SV, SV', slide) in varSlidesSV)
{
	assert forall slide :: slide in SlideDGOf(S, CFGOf(S)).1 ==> (slide in slidesSV <==> VarSlideOf(SV, SV', slide) in varSlidesSV) by {
		// p ==> q:	
		L1(setOf(X), S, SV, SV', slidesSV, varSlidesSV, vsSSA, V, V', varSlideDGS');
		assert forall slide :: slide in slidesSV ==> VarSlideOf(SV, SV', slide) in varSlidesSV;
		
		assert forall vSlide :: vSlide in varSlidesSV ==> (vSlide in varSlidesOf(S,def(S)) && exists Sn: VarSlide :: Sn.0 in V' && VarSlideDGReachable(varSlideDGS', vSlide, Sn, varSlideDGS'.1));
		
		// ^p ==> ^q:
		L2(S, SV, SV', slidesSV, varSlidesSV, V, V', varSlideDGS', vsSSA);
		assert forall slide :: slide in SlideDGOf(S, CFGOf(S)).1 - slidesSV ==> VarSlideOf(SV, SV', slide) !in varSlidesSV;
	}
}

lemma {:verify false}L1(X: set<Variable>, S: Statement, SV: Statement, SV': Statement, slidesSV: set<Slide>, varSlidesSV: set<VarSlide>, vsSSA: VariablesSSA, V: set<Variable>, V': set<Variable>, varSlideDG: VarSlideDG)
	requires Valid(S) && Core(S)
	requires Valid(SV) && Core(SV)
	requires Valid(SV') && Core(SV')
	requires ValidVsSSA(vsSSA)
	ensures forall slide :: slide in slidesSV ==> VarSlideOf(SV, SV', slide) in varSlidesSV
	//ensures varSlidesSV == old(varSlidesSV)
{
	forall slide | slide in slidesSV ensures VarSlideOf(SV, SV', slide) in varSlidesSV {
		assert slide in slidesSV;
		
		var varSlide := VarSlideOf(SV, SV', slide);
		var cfg := ComputeCFG(S);
		var slideDG := SlideDGOf(S, cfg);

		assert varSlide in varSlidesSV by {
			assert exists Sn: VarSlide :: Sn.0 in V' && VarSlideDGReachable(varSlideDG, varSlide/*i1*/, Sn/*sum4*/, varSlideDG.1) by {
				var finalDefSlide;
				if slide in finalDefSlides(S, slideDG, cfg, V)
				{
					finalDefSlide := slide;
				}
				else
				{ // i1 --> sum5 --> sum4 , sum5 is pre of sum4 via phi only
					finalDefSlide :| finalDefSlide in finalDefSlides(S, slideDG, cfg, V) && SlideDGReachable(slideDG, slide, finalDefSlide, slideDG.1);
				} 
					
				var finalDefVarSlide := VarSlideOf(SV, SV', finalDefSlide);

				assert varSlide == VarSlideOf(SV, SV', slide);
				assert VarSlideDGReachable(varSlideDG, varSlide, finalDefVarSlide, varSlideDG.1) by {
					PathCorrespondence(slideDG, varSlideDG, slide, finalDefSlide, SV, SV');
				}

				assert VarSlideDGReachable(varSlideDG, varSlide, finalDefVarSlide, varSlideDG.1);

				assert vsSSA.existsInstance(finalDefSlide.1);
				var instancesOfFinalDefSlideSeq := vsSSA.getInstancesOfVaribleFunc(finalDefSlide.1);
				var instancesOfFinalDefSlide := setOf(instancesOfFinalDefSlideSeq);
				assert |instancesOfFinalDefSlide * V'| == 1;
				var v' :| v' in instancesOfFinalDefSlide * V';
				var slideOfV': VarSlide :| slideOfV'.0 == v';// varSlideOf(v'); // TODO

				if slideOfV'.1 == Regular
				{
					assert slideOfV' == finalDefVarSlide;
					assert slideOfV'.0 in V' && VarSlideDGReachable(varSlideDG, varSlide/*i1*/, slideOfV'/*sum5*/, varSlideDG.1);
					// Done
				}
				else // Phi
				{
					assert slideOfV' != finalDefVarSlide; // צריך להוכיח מסלול ביניהם
					assert VarSlideDGReachable(varSlideDG, finalDefVarSlide/*sum5*/, slideOfV'/*sum4*/, varSlideDG.1);
					assert finalDefVarSlide in RegularPredecessorSlides(slideOfV', varSlideDG, varSlidesOf(SV', V')) by {
						//var finalDefVarSlides := set slide, varSlide | slide in finalDefSlides(S, slideDG, cfg, V) && varSlide == VarSlideOf(SV, SV', slide) :: varSlide;
						var finalDefVarSlides := set slide, varSlide | slide in finalDefSlides(S, slideDG, cfg, V) && varSlide in varSlidesOf(S,def(S)) && varSlide == VarSlideOf(SV, SV', slide) :: varSlide;
						//////////////L4(X, vsSSA, v', V', instancesOfFinalDefSlide, finalDefSlide, S, slideDG, cfg, V, slide, slidesSV, slideOfV', finalDefVarSlides, varSlideDG, SV');
					}
				}
			}
		}
	}	
}

// Working
lemma {:verify false}L2(S: Statement, SV: Statement, SV': Statement, slidesSV: set<Slide>, varSlidesSV: set<VarSlide>, V: set<Variable>, V': set<Variable>, varSlideDG: VarSlideDG, vsSSA: VariablesSSA)
	requires Valid(S) && Core(S)
	requires Valid(SV) && Core(SV)
	requires Valid(SV') && Core(SV')
	requires var slideDG := SlideDGOf(S, CFGOf(S)); forall Sm :: Sm in slidesSV <==> (Sm in slidesOf(S,def(S)) && exists Sn :: Sn in finalDefSlides(S, slideDG, CFGOf(S), V) && SlideDGReachable(slideDG, Sm, Sn, slideDG.1));
	requires forall vSlide :: vSlide in varSlidesSV ==> (vSlide in varSlidesOf(S,def(S)) && exists Sn: VarSlide :: Sn.0 in V' && VarSlideDGReachable(varSlideDG, vSlide, Sn, varSlideDG.1));
	ensures forall slide :: slide in SlideDGOf(S, CFGOf(S)).1 - slidesSV ==> VarSlideOf(SV, SV', slide) !in varSlidesSV;
{
	var cfg := ComputeCFG(S);
	var slideDG := SlideDGOf(S, cfg); 
	assume slideDG == SlideDGOf(S, cfg); 
	assume cfg == CFGOf(S);
	assert forall slide :: slide in slideDG.1 - slidesSV ==> VarSlideOf(SV, SV', slide) !in varSlidesSV by {

		forall slide | slide in slideDG.1 - slidesSV ensures VarSlideOf(SV, SV', slide) !in varSlidesSV {
			var varSlide := VarSlideOf(SV, SV', slide);
			assert varSlide == VarSlideOf(SV, SV', slide);
			
			assert !(slide in slidesOf(S,def(S)) && exists Sn :: Sn in finalDefSlides(S, slideDG, cfg, V) && SlideDGReachable(slideDG, slide, Sn, slideDG.1)) by {
				assert forall Sm :: Sm in slidesSV <==> (Sm in slidesOf(S,def(S)) && exists Sn :: Sn in finalDefSlides(S, slideDG, cfg, V) && SlideDGReachable(slideDG, Sm, Sn, slideDG.1));
				assert slide !in slidesSV;
			} 
		 
			assert varSlide !in varSlidesSV by {
				calc {
					varSlide in varSlidesSV;
				==> { assert forall vSlide :: vSlide in varSlidesSV ==> (vSlide in varSlidesOf(S,def(S)) && exists Sn: VarSlide :: Sn.0 in V' && VarSlideDGReachable(varSlideDG, vSlide, Sn, varSlideDG.1)); }
					varSlide in varSlidesOf(S,def(S)) && exists Sn: VarSlide :: Sn.0 in V' && VarSlideDGReachable(varSlideDG, varSlide/*i1*/, Sn/*sum4*/, varSlideDG.1);
				==> { assert varSlide == VarSlideOf(SV, SV', slide);
					  L5(slide, varSlide, S, SV, SV', V, V', slideDG, cfg, varSlideDG, vsSSA); }
					slide in slidesOf(S,def(S)) && exists Sn :: Sn in finalDefSlides(S, slideDG, cfg, V) && SlideDGReachable(slideDG, slide, Sn, slideDG.1);
				==> { assert !(slide in slidesOf(S,def(S)) && exists Sn :: Sn in finalDefSlides(S, slideDG, cfg, V) && SlideDGReachable(slideDG, slide, Sn, slideDG.1)); }	
					false;
				}
			}	
		}
	}
}

lemma {:verify false}L5(slide: Slide, varSlide: VarSlide, S: Statement, SV: Statement, SV': Statement, V: set<Variable>, V': set<Variable>, slideDG: SlideDG, cfg: CFG, varSlideDG: VarSlideDG, vsSSA: VariablesSSA)
	requires Valid(S) && Core(S)
	requires Valid(SV) && Core(SV)
	requires Valid(SV') && Core(SV')
	requires varSlide.1 == Regular
	requires varSlide == VarSlideOf(SV, SV', slide) 
	requires varSlide in varSlidesOf(S,def(S)) && exists varSn: VarSlide :: varSn.0 in V' && VarSlideDGReachable(varSlideDG, varSlide/*i1*/, varSn/*sum4*/, varSlideDG.1)
	ensures slide in slidesOf(S,def(S)) && exists Sn :: Sn in finalDefSlides(S, slideDG, cfg, V) && SlideDGReachable(slideDG, slide, Sn, slideDG.1)
/*{
	var varSn: VarSlide :| varSn.0 in V' && VarSlideDGReachable(varSlideDG, varSlide, varSn, varSlideDG.1);
	var Sn;

	if varSn.1 == Regular
	{
		Sn := SlideOf(SV, SV', varSn);
		PathBackCorrespondence(slideDG, varSlideDG, slide, Sn, SV, SV');
		assert SlideDGReachable(slideDG, slide, Sn, slideDG.1); // From PathBackCorrespondence
		assert Sn in finalDefSlides(S, slideDG, cfg, V) by {
			L6(varSn, V, V', S, SV, SV', slideDG, cfg);
		}
		assert Sn in finalDefSlides(S, slideDG, cfg, V) && SlideDGReachable(slideDG, slide, Sn, slideDG.1); // From the two above
	}
	else
	{
		var rpsVarSn := RegularPredecessorSlides(varSn, varSlideDG, varSlidesOf(SV', V'));
		var Sn' :| Sn' in rpsVarSn && VarSlideDGReachable(varSlideDG, varSlide, Sn', varSlideDG.1) && vsSSA.getVariableInRegularFormFunc(Sn'.0) in V;
		Sn := SlideOf(SV, SV', Sn');
		PathBackCorrespondence(slideDG, varSlideDG, slide, Sn, SV, SV');
		assert SlideDGReachable(slideDG, slide, Sn, slideDG.1); // From PathBackCorrespondence
		assert Sn in finalDefSlides(S, slideDG, cfg, V) by {
			L7(varSn, V, V', S, SV, SV', slideDG, cfg, varSlideDG, varSlide, Sn', rpsVarSn, vsSSA);
		}
		assert Sn in finalDefSlides(S, slideDG, cfg, V) && SlideDGReachable(slideDG, slide, Sn, slideDG.1); // From the two above
	}
}*/
/*
lemma L6(varSn: VarSlide, V: set<Variable>, V': set<Variable>, S: Statement, SV: Statement, SV': Statement, slideDG: SlideDG, cfg: CFG)
	requires Valid(S) && Core(S)
	requires Valid(SV) && Core(SV)
	requires Valid(SV') && Core(SV')
	requires varSn.1 == Regular
	requires varSn.0 in V'
	ensures SlideOf(SV, SV', varSn) in finalDefSlides(S, slideDG, cfg, V)

lemma L7(varSn: VarSlide, V: set<Variable>, V': set<Variable>, S: Statement, SV: Statement, SV': Statement, slideDG: SlideDG, cfg: CFG,
		 varSlideDG: VarSlideDG, varSlide: VarSlide, Sn': VarSlide, rpsVarSn: set<VarSlide>, vsSSA: VariablesSSA)
	requires varSn.1 == Phi
	requires varSn.0 in V'
	requires Sn' in rpsVarSn && VarSlideDGReachable(varSlideDG, varSlide, Sn', varSlideDG.1) && vsSSA.getVariableInRegularFormFunc(Sn'.0) in V
	ensures SlideOf(SV, SV', Sn') in finalDefSlides(S, slideDG, cfg, V)


lemma EdgeToVarPhiPath(slide1: Slide, slide2: Slide, slideDG: SlideDG, varSlideDG: VarSlideDG, SV: Statement, SV': Statement)
	requires Valid(SV) && Core(SV)
	requires Valid(SV') && Core(SV')
	requires slide2 in slideDG.2
	requires slide1 in slideDG.2[slide2]
	//requires connection between SV and SV'
	ensures VarSlideDGReachablePhi(varSlideDG, VarSlideOf(SV, SV', slide1), VarSlideOf(SV, SV', slide2), varSlideDG.1)
// לכתוב למה עבור קשת מסלייד1 לסלייד2, קיים מסלול מוארסלייד1 לוארסלייד2 שעובר דרך 0 או יותר קודקודי פי
// והפוך, ממסלול לקשת

lemma VarPhiPathToEdge(slide1: Slide, slide2: Slide, slideDG: SlideDG, varSlideDG: VarSlideDG, SV: Statement, SV': Statement)
	requires Valid(SV) && Core(SV)
	requires Valid(SV') && Core(SV')
	requires VarSlideDGReachablePhi(varSlideDG, VarSlideOf(SV, SV', slide1), VarSlideOf(SV, SV', slide2), varSlideDG.1)
	//requires connection between SV and SV'
	ensures slide2 in slideDG.2
	ensures slide1 in slideDG.2[slide2]

//  למה עבור מסלול מוארסלייד1 לוארסלייד2 שעובר דרך 0 או יותר קודקודי פי, קיימת קשת מסלייד1 לסלייד2

lemma PathBackCorrespondence(slideDG: SlideDG, varSlideDG: VarSlideDG, slide1: Slide, slide2: Slide, SV: Statement, SV': Statement)
	requires Valid(SV) && Core(SV)
	requires Valid(SV') && Core(SV')
	requires VarSlideOf(SV, SV', slide1).1 == Regular && VarSlideOf(SV, SV', slide2).1 == Regular
	requires VarSlideDGReachable(varSlideDG, VarSlideOf(SV, SV', slide1), VarSlideOf(SV, SV', slide2), varSlideDG.1)
	//requires connection between SV and SV'
	ensures SlideDGReachable(slideDG, slide1, slide2, slideDG.1)

*/
lemma {:verify false}PathCorrespondence(slideDG: SlideDG, varSlideDG: VarSlideDG, slide1: Slide, slide2: Slide, SV: Statement, SV': Statement)
	requires Valid(SV) && Core(SV)
	requires Valid(SV') && Core(SV')
	requires SlideDGReachable(slideDG, slide1, slide2, slideDG.1)
	//requires connection between SV and SV'
	ensures VarSlideDGReachable(varSlideDG, VarSlideOf(SV, SV', slide1), VarSlideOf(SV, SV', slide2), varSlideDG.1)
	
	

/*lemma L4(X: set<Variable>, vsSSA: VariablesSSA, v': Variable, V': set<Variable>, instancesOfFinalDefSlide: set<Variable>,
		 finalDefSlide: Slide, S: Statement, slideDG: SlideDG, cfg: CFG, V: set<Variable>, slide: Slide, slidesSV: set<Slide>,
		 slideOfV': VarSlide, finalDefVarSlides: set<VarSlide>, varSlideDG: VarSlideDG, SV': Statement)
	//requires forall Sm :: Sm in finalDefSlides(S, slideDG, cfg, V) || (exists Sn :: Sn in finalDefSlides(S, slideDG, cfg, V) && SlideDGReachable(slideDG, slide, Sn, slideDG.1))	
	requires slide in slidesSV
	requires slide !in finalDefSlides(S, slideDG, cfg, V)
	requires finalDefSlide in finalDefSlides(S, slideDG, cfg, V) && SlideDGReachable(slideDG, slide, finalDefSlide, slideDG.1)
	requires instancesOfFinalDefSlide == setOf(vsSSA.getInstancesOfVaribleFunc(finalDefSlide.1))
	requires {v'} == instancesOfFinalDefSlide * V'
	requires slideOfV' == varslideof(v') // TODO
	requires slideOfV'.1 == Phi
	ensures forall x,i :: x in X && i in vsSSA.getInstancesOfVaribleFunc(x) && varslideof(i)/*TODO*/ in finalDefVarSlides ==>
																varslideof(i) in RegularPredecessorSlides(slideOfV', varSlideDG, varSlidesOf(SV', V'))
*/
	
					/*if (i4 % 2 == 0)
						i9 := i4 + 1;
						i8 := i9;
					else
						i10 := 3;
						i8 := i10;

					V' = {i8}
					v' = i8
					finalDefVaSlides = {i9,i10}*/



function {:verify false}RegularPredecessorSlides(varSlide: VarSlide, varSlideDG: VarSlideDG, unvisitedVarSlides: set<VarSlide>): set<VarSlide>
	requires varSlide in varSlideDG.2
	requires unvisitedVarSlides <= varSlideDG.1
	requires forall p :: p in varSlideDG.2[varSlide] ==> p in varSlideDG.1
	requires forall p :: p in varSlideDG.2[varSlide] ==> p in unvisitedVarSlides
	requires forall vSlide :: vSlide in unvisitedVarSlides ==> vSlide in varSlideDG.2
	decreases unvisitedVarSlides
{
	var predecessors := varSlideDG.2[varSlide];
	assert forall p :: p in predecessors ==> p in varSlideDG.2;

	(set vSlide | vSlide in predecessors && vSlide.1 == Regular) + 
	(set vSlide1, vSlide2 | vSlide1 in predecessors && vSlide1.1 == Phi && vSlide1 in unvisitedVarSlides && vSlide2 in RegularPredecessorSlides(vSlide1, varSlideDG, unvisitedVarSlides - {vSlide1}) :: vSlide2)
}

function {:verify false}SlideOf(S: Statement, S': Statement, varSlide: VarSlide): Slide


function {:verify false}VarLabelOfSlide(S: Statement, S': Statement, slide: Slide): Label
	reads *
	requires Valid(S)
	requires Valid(S')
	requires Core(S)
	requires Core(S')
{
	match slide.0 { 
		case Node(l) => VarLabelOf(S, S', l)
		case Entry => [] // מיותר! הוספתי רק כדי שירוץ
		case Exit => [] // מיותר! הוספתי רק כדי שירוץ
	}
}

function {:verify false}VarSlideOf(S: Statement, S': Statement, slide: Slide): VarSlide
	reads *
	requires Valid(S)
	requires Valid(S')
	requires Core(S)
	requires Core(S')
{
	match slide.0 { 
		case Node(l) => var varLabel := VarLabelOf(S, S', l); var i := InstanceOf(S', varLabel); (i, Regular)
		case Entry => ("", Regular) // מיותר! הוספתי רק כדי שירוץ
		case Exit => ("", Regular) // מיותר! הוספתי רק כדי שירוץ
	}
}

function {:verify false}VarLabelOf(S: Statement, S': Statement, l: Label): Label
	//requires S' == ToSSA(S) //////
	reads *
	requires Valid(S)
	requires Valid(S')
	requires Core(S)
	requires Core(S')
	ensures |VarLabelOf(S, S', l)| >= 1 && |VarLabelOf(S, S', l)| <= maxLabelSize(S')
{
	match S {
	case Skip =>				[]		
	case Assignment(LHS,RHS) =>	match S' {
								case Assignment(LHS',RHS') => []
								}
	case SeqComp(S1,S2) =>		match S' {
								case SeqComp(S1',S2') => if l[0] == 1 then [1] + VarLabelOf(S1, S1', l[1..]) else [2] + VarLabelOf(S2, S2', l[1..])
								}	
	case IF(B0,Sthen,Selse) =>	match S' {							
								case IF(B0',Sthen',Selse') => if l[0] == 1 then [1] + VarLabelOf(Sthen, Sthen', l[1..]) else [2] + VarLabelOf(Selse, Selse', l[1..])
								}
	case DO(B,Sloop) =>			match S' {
								// S1' is the phi assignment and S2' is the DO
								// we should add another [2] in order to go to the loop
								case SeqComp(S1',S2') => match S2' {
														 case DO(B',Sloop') => [2] + [1] + VarLabelOf(Sloop, Sloop', l[1..])
														 }
								}
	}
}

function {:verify false}InstanceOf(S': Statement, varLabel: Label): Variable
	reads *
	requires Valid(S')
	requires Core(S')
	requires |varLabel| >= 1 && |varLabel| <= maxLabelSize(S')
{
	match S' {
	case Skip =>					""
	case Assignment(LHS',RHS') =>	assume |LHS'| >= 1; LHS'[0]
	case SeqComp(S1',S2') =>		if varLabel[0] == 1 then InstanceOf(S1', varLabel[1..]) else InstanceOf(S2', varLabel[1..])
	case IF(B0',Sthen',Selse') =>	""//if varLabel[0] == 1 then InstanceOf(Sthen', varLabel[1..]) else InstanceOf(Selse', varLabel[1..])
	case DO(B',Sloop') =>			""//InstanceOf(Sloop', varLabel[1..])
	}
}

function {:verify false}varStatementOf(varSlides: set<VarSlide>, S: Statement): Statement


function {:verify false}statementOf(slides: set<Slide>, S: Statement): Statement
	reads *
	requires Valid(S)
	requires Core(S)
	//requires forall slide :: slide in allSlidesOf(S) && exists l :: slide.0 == CFGNode.Node(l) ==> ValidLabel(l, S)
	requires forall slide :: exists l :: slide in allSlidesOf(S) && slide.0 == CFGNode.Node(l) ==> ValidLabel(l, S)
	requires slides <= allSlidesOf(S)
	ensures Core(statementOf(slides, S))
	ensures Valid(statementOf(slides, S))
	ensures Substatement(statementOf(slides, S), S)
{
//Slide = (CFGNode, Variable, set<CFGNode>)
//CFGNode = Node(l:Label) | Entry | Exit

	if slides == {} then Skip
	else
	var slide :| slide in slides;
	match slide.0 {
	case Node(l) => 	assert slide in allSlidesOf(S);
						assert ValidLabel(l, S);
						var S' := statementOfSlide(slide, l, S);
						assert Substatement(S', S);
						var rest := statementOf(slides - {slide}, S);
						assert Substatement(rest, S);
						mergeStatements(S', rest, S)
	case Entry =>		Skip // ?
	case Exit =>		Skip // ?
	}
}

function {:verify true}allSlidesOf(S: Statement) : set<Slide>
	reads *
	requires Valid(S)
	requires Core(S)
{
	slidesOf(S, def(S))
}

predicate {:verify true}ValidLabel(l: Label, S: Statement)
	reads *
	requires Valid(S)
	requires Core(S)
{
	if l == [] then true
	else
	match S {
	case Skip =>				false
	case Assignment(LHS,RHS) =>	false
	case SeqComp(S1,S2) =>		if l[0] == 1 then ValidLabel(l[1..], S1) else ValidLabel(l[1..], S2)
	case IF(B0,Sthen,Selse) =>	if l[0] == 1 then ValidLabel(l[1..], Sthen) else ValidLabel(l[1..], Selse)
	case DO(B,Sloop) =>			if l[0] == 1 then ValidLabel(l[1..], Sloop) else false
	}
}

function {:verify true}maxLabelSize(S: Statement): int
	reads *
	requires Valid(S)
	requires Core(S)
{
	match S {
	case Skip => 0
	case Assignment(LHS,RHS) =>	0
	case SeqComp(S1,S2) =>		1 + max(maxLabelSize(S1), maxLabelSize(S2))
	case IF(B0,Sthen,Selse) =>	1 + max(maxLabelSize(Sthen), maxLabelSize(Selse))
	case DO(B,Sloop) =>			1 + maxLabelSize(Sloop)
	}	
}

function max(x: int, y: int): int
{
	if x > y then x else y
}

function {:verify false}statementOfSlide(slide: Slide, l: Label, S: Statement): Statement
	reads *
	requires Valid(S)
	requires Core(S)
	requires ValidLabel(l, S)
	ensures Core(statementOfSlide(slide, l, S))
	ensures Valid(statementOfSlide(slide, l, S))
	ensures Substatement(statementOfSlide(slide, l, S), S)
{
	if l == [] then S
	else
	match S {
	case Skip => Skip
	case Assignment(LHS,RHS) => S
	case SeqComp(S1,S2) =>		if l[0] == 1 then SeqComp(statementOfSlide(slide, l[1..], S1), Skip)  else SeqComp(Skip, statementOfSlide(slide, l[1..], S2))
	case IF(B0,Sthen,Selse) =>	if l[0] == 1 then IF(B0, statementOfSlide(slide, l[1..], Sthen), Skip) else IF(B0, Skip, statementOfSlide(slide, l[1..], Selse))
	case DO(B,Sloop) =>			DO(B, statementOfSlide(slide, l[1..], Sloop))
	}
}

function {:verify false}mergeStatements(S1: Statement, S2: Statement, S: Statement) : Statement
	reads *
	requires Valid(S1)
	requires Valid(S2)
	requires Valid(S)
	requires Core(S)
	requires Core(S1)
	requires Core(S2)
	requires Substatement(S1, S) && Substatement(S2, S) 
	ensures Valid(mergeStatements(S1, S2, S))
	ensures Core(mergeStatements(S1, S2, S))
	ensures Substatement(mergeStatements(S1, S2, S), S)
{
	match S {
	case Skip =>					Skip
	case Assignment(LHS',RHS') =>	match S1 {
									case Skip =>					S2
									case Assignment(LHS1,RHS1) =>	match S2 {
																	case Skip => S1
																	case Assignment(LHS2,RHS2) => var LR := mergeAssignments(LHS1, LHS2, RHS1, RHS2, {}); Assignment(LR.0, LR.1)
																	}
									}
	case SeqComp(S1',S2') =>		match S1 {
									case Skip =>					S2
									case SeqComp(S11,S12) =>		match S2 {
																	case Skip => S1
																	case SeqComp(S21,S22) => SeqComp(mergeStatements(S11, S21, S1'), mergeStatements(S12, S22, S2'))
																	}
									}
	case IF(B',Sthen',Selse') =>	match S1 {
									case Skip =>					S2
									case IF(B1,Sthen1,Selse1) =>	match S2 {
																	case Skip => S1
																	case IF(B2,Sthen2,Selse2) => IF(B1, mergeStatements(Sthen1, Sthen2, Sthen'), mergeStatements(Selse1, Selse2, Selse'))
																	}
									}
	case DO(B',Sloop') =>			match S1 {
									case Skip =>					S2
									case DO(B1,Sloop1) =>			match S2 {
																	case Skip => S1
																	case DO(B2,Sloop2) => DO(B1, mergeStatements(Sloop1, Sloop2, Sloop'))
																	}
									}
	}

	/*match S1 {
	case Skip =>				  S2
								  
	case Assignment(LHS1,RHS1) => match S2 {
								  case Skip =>					S1
								  case Assignment(LHS2,RHS2) => match S {
																case Assignment(LHS',RHS') => var LR := mergeAssignments(LHS1, LHS2, RHS1, RHS2, {}); Assignment(LR.0, LR.1)
																}
								  }
	case SeqComp(S11,S12) =>	  match S2 {
								  case Skip =>					S1
								  case SeqComp(S21,S22) =>		match S {
																case SeqComp(S1',S2') => SeqComp(mergeStatements(S11, S21, S1'), mergeStatements(S12, S22, S2'))
																}
								  }
	case IF(B1,Sthen1,Selse1) =>  match S2 {
								  case Skip =>					S1
								  case IF(B2,Sthen2,Selse2) =>	match S {
																case IF(B',Sthen',Selse') => IF(B1, mergeStatements(Sthen1, Sthen2, Sthen'), mergeStatements(Selse1, Selse2, Selse'))
																}
								  }
	case DO(B1,Sloop1) =>		  match S2 {
								  case Skip =>					S1 
								  case DO(B2,Sloop2) =>			match S {
																case DO(B',Sloop') => DO(B1, mergeStatements(Sloop1, Sloop2, Sloop'))
																}
								  }
	}*/
}

function {:verify false}mergeAssignments(LHS1: seq<Variable>, LHS2: seq<Variable>, RHS1: seq<Expression>, RHS2: seq<Expression>, vars: set<Variable>) : (seq<Variable>, seq<Expression>)
	requires |LHS1| == |RHS1| && |LHS2| == |RHS2|
	ensures Valid(Assignment(mergeAssignments(LHS1, LHS2, RHS1, RHS2, vars).0, mergeAssignments(LHS1, LHS2, RHS1, RHS2, vars).1))
{
	// LHS1 = [x,y]
	// LHS2 = [y,z]
	// RHS1 = [1,2]
	// RHS2 = [2,3]

	// LHS1 = [x,y]
	// LHS2 = [x,z]
	// RHS1 = [1,2]
	// RHS2 = [1,3]

	// LHS1 = [x,y]
	// LHS2 = [z,x]
	// RHS1 = [1,2]
	// RHS2 = [3,1]

	// LHS1 = [x,y,z]
	// LHS2 = [u,v]
	// RHS1 = [1,2,3]
	// RHS2 = [4,5]


	if LHS1 == [] && LHS2 == [] then ([],[])
	else
		if LHS1 == [] && LHS2 != [] then 
			var res := mergeAssignments(LHS1, LHS2[1..], RHS1, RHS2[1..], vars + {LHS2[0]});
			var LHS := [LHS2[0]] + res.0;
			var RHS := [RHS2[0]] + res.1;
			(LHS, RHS)			
		else if LHS1 != [] && LHS2 == [] then
			var res := mergeAssignments(LHS1[1..], LHS2, RHS1[1..], RHS2, vars + {LHS1[0]});
			var LHS := [LHS1[0]] + res.0;
			var RHS := [RHS1[0]] + res.1;
			(LHS, RHS)			
		else 
			if LHS1[0] == LHS2[0] then
				var res := mergeAssignments(LHS1[1..], LHS2[1..], RHS1[1..], RHS2[1..], vars + {LHS1[0]});
				var LHS := [LHS1[0]] + res.0;
				var RHS := [RHS1[0]] + res.1;
				(LHS, RHS)
			else
				var res := mergeAssignments(LHS1[1..], LHS2[1..], RHS1[1..], RHS2[1..], vars + {LHS1[0], LHS2[0]});
				if LHS1[0] !in vars && LHS2[0] !in vars then
					var LHS := [LHS1[0]] + [LHS2[0]] + res.0;
					var RHS := [RHS1[0]] + [RHS2[0]] + res.1;
					(LHS, RHS)
				else if LHS1[0] !in vars then
					var LHS := [LHS1[0]] + res.0;
					var RHS := [RHS1[0]] + res.1;
					(LHS, RHS)
				else /* if LHS2[0] !in vars then */
					var LHS := [LHS2[0]] + res.0;
					var RHS := [RHS2[0]] + res.1;
					(LHS, RHS)
}

predicate {:verify true}Substatement(S': Statement, S: Statement)
	reads *
	requires Valid(S')
	requires Valid(S)
	requires Core(S')
	requires Core(S)
{
	match S {
	case Skip =>				S' == Skip		
	case Assignment(LHS,RHS) =>	match S' {
								case Skip => true
								case Assignment(LHS',RHS') => Subassignment(LHS', RHS', LHS, RHS)
								case SeqComp(S1',S2') => false
								case IF(B0',Sthen',Selse') => false
								case DO(B',Sloop') => false
								}
	case SeqComp(S1,S2) =>		match S' {
								case Skip => true
								case Assignment(LHS',RHS') => false
								case SeqComp(S1',S2') => Substatement(S1', S1) && Substatement(S2', S2)
								case IF(B0',Sthen',Selse') => false
								case DO(B',Sloop') => false
								}	
	case IF(B0,Sthen,Selse) =>	match S' {
								case Skip => true
								case Assignment(LHS',RHS') => false
								case SeqComp(S1',S2') => false								
								case IF(B0',Sthen',Selse') => SameBooleanExpressions(B0, B0') && Substatement(Sthen', Sthen) && Substatement(Selse', Selse)
								case DO(B',Sloop') => false
								}
	case DO(B,Sloop) =>			match S' {
								case Skip => true
								case Assignment(LHS',RHS') => false
								case SeqComp(S1',S2') => false								
								case IF(B0',Sthen',Selse') => false
								case DO(B',Sloop') => SameBooleanExpressions(B, B') && Substatement(Sloop', Sloop)
								}
	}
}

predicate {:verify true}Subassignment(LHS': seq<Variable>, RHS': seq<Expression>, LHS: seq<Variable>, RHS: seq<Expression>)
	requires ValidAssignment(LHS', RHS')
	requires ValidAssignment(LHS, RHS)
{
	// S':  x,z := 1,3;
	// S:   x,y,z := 1,2,3;

	if LHS' == [] then true
	else if LHS == [] then false
	else
		assert ValidAssignment(LHS[1..], RHS[1..]) by { LemmaSetOf1(LHS); }
		assert ValidAssignment(LHS'[1..], RHS'[1..]) by { LemmaSetOf1(LHS'); }
		if LHS'[0] == LHS[0] then
			if SameExpressions(RHS'[0], RHS[0]) then Subassignment(LHS'[1..], RHS'[1..], LHS[1..], RHS[1..])
			else false
		else
			Subassignment(LHS', RHS', LHS[1..], RHS[1..])
}

lemma LemmaSetOf1<T>(q: seq<T>)
	requires |q| != 0
	requires |setOf(q)| == |q|
	ensures |setOf(q[1..])| == |q[1..]|
/*
{
	calc {
		|q[1..]|;
	== { assert |[q[0]]| == 1; assert q == [q[0]] + q[1..]; }
		|LHS| - 1;
	== { assert |setOf(q)| == |q|; }
		|setOf(q)| - 1;
	== { assert q == [q[0]] + q[1..]; }
		|setOf([q[0]] + q[1..])| - 1;
	== { assert q[0] !in q[1..]; } // lemma
		|setOf([q[0]]) + setOf(q[1..])| - 1;
	== { assert setOf([q[0]]) * setOf(q[1..]) == {}; }
		|setOf([q[0]])| + |setOf(q[1..])| - 1;
	== { assert |setOf([q[0]])| == 1; }
		|setOf(q[1..])|;
	}
}
*/

///////////////////////////////////////////////////////////////////////////////////////////////////


function method {:verify false}GetAssignmentsOfV(LHS : seq<Variable>, RHS : seq<Expression>, V: set<Variable>) : Statement
{
	if LHS == [] then Skip
	else if LHS[0] in V then 
	var tempRes := GetAssignmentsOfV(LHS[1..], RHS[1..], V);
	match tempRes {
		case Assignment(LHS1,RHS1) => Assignment([LHS[0]]+LHS1, [RHS[0]]+RHS1)
	}
	else GetAssignmentsOfV(LHS[1..], RHS[1..], V)

	/*if LHS == [] then Skip
	else if LHS[0] in V then SeqComp(Assignment([LHS[0]],[RHS[0]]), GetAssignmentsOfV(LHS[1..], RHS[1..], V))
	else GetAssignmentsOfV(LHS[1..], RHS[1..], V)*/
}

function method {:verify false}ComputeSlides(S: Statement, V: set<Variable>) : Statement
{
	if V * def(S) == {} then Skip
	else
	match S {
		case Skip => Skip
		case Assignment(LHS,RHS) => GetAssignmentsOfV(LHS,RHS,V)
		case SeqComp(S1,S2) => SeqComp(ComputeSlides(S1,V), ComputeSlides(S2,V))
		case IF(B0,Sthen,Selse) => IF(B0, ComputeSlides(Sthen,V) , ComputeSlides(Selse,V))
		case DO(B,S) => DO(B, ComputeSlides(S,V))
	}
}

function method {:verify false}ComputeSlidesDepRtc(S: Statement, V: set<Variable>) : set<Variable>
{
	var slidesSV := ComputeSlides(S, V);
	var U := glob(slidesSV) * def(S);

	if U <= V then V else ComputeSlidesDepRtc(S, V + U)
}

method {:verify false} ComputeFISlice(S: Statement, V: set<Variable>, ghost varSlideDG: VarSlideDG) returns (SV: Statement)
	requires VarSlideDGOf(varSlideDG, S) // varSlideDG is of S
	ensures var varSlidesSV: set<VarSlide> := varSlidesOf(SV, V); forall Sm :: Sm in varSlidesSV <==> (Sm.0 in V || (exists Sn: VarSlide :: Sn.0 in V && VarSlideDGReachable(varSlideDG, Sm, Sn, varSlideDG.1)))	 // Implement VarSlideDGReachable
	ensures Substatement(SV, S)
{
	var Vstar := ComputeSlidesDepRtc(S, V);

	SV := ComputeSlides(S, Vstar);

	//SV := ComputeSlides(S, ComputeSlidesDepRtc(S, V));
}

/******************************************* Proof of Substatement(res, S) *******************************************/

lemma {:verify true}L20(S: Statement, S': Statement, SV': Statement, res: Statement, X: seq<Variable>, XLsToSSA: seq<set<Variable>>, l: Label, varLabel: Label) // called with l==varLabel==[]
	requires Valid(S) && Valid(S') && Valid(SV') && Valid(res)
	requires Core(S) && Core(S') && Core(SV') && Core(res)
	requires ValidLabel(l, S)
	requires ValidLabel(l, res)
	requires ValidLabel(varLabel, SV')
	requires ValidLabel(varLabel, S')
	requires MatchingSlipsToSSA(S, l, S', varLabel)
	requires MatchingSlips(S', SV', varLabel)
	requires MatchingSlipsFromSSA(SV', varLabel, res, l)
	// ==>
	requires MatchingSlips(S, res, l)
	requires NoSelfAssignments(S')
	requires MergedVars1(S', S, XLsToSSA, X)	// ToSSA Postcondition
	requires Substatement(SV', S')				// ComputeFISlice Postcondition
	requires NoSelfAssignments(SV')
	requires MergedVars1(SV', res, XLsToSSA, X) // FromSSA Postcondition
	ensures Substatement(slipOf(res, l), slipOf(S, l))
	decreases maxLabelSize(S) - |l|
{
	var slipOfS := slipOf(S, l);
	var slipOfRes := slipOf(res, l);
	var slipOfSV' := slipOf(SV', varLabel);
	var slipOfS' := slipOf(S', varLabel);

	match slipOfS {
	case Skip =>				assert slipOfRes == Skip; // There is no statement to slice from, therefore slipOfRes is also skip		
	case Assignment(LHS,RHS) =>	match slipOfRes { // Assignment or Skip
								case Skip =>						assert Substatement(Skip, Assignment(LHS,RHS));
								case Assignment(resLHS,resRHS) =>	assert Subassignment(resLHS, resRHS, LHS, RHS) by {
																		assert IsAssignment(slipOfSV');/* by {
																			assert MatchingSlipsFromSSA(SV', varLabel, res, l);
																		}*/
																		match slipOfSV' {
																		case Assignment(SV'LHS,SV'RHS) => L22(S, S', SV', res, X, XLsToSSA, l, varLabel);
																		}
																	}
								case SeqComp(resS1,resS2) =>		assert false by { L30(S, res, l); }
								case IF(resB0,resSthen,resSelse) => assert false by { L30(S, res, l); }
								case DO(resB,resSloop) =>			assert false by { L30(S, res, l); }
								}
	case SeqComp(S1,S2) =>		match slipOfRes { // SeqComp or Skip
								case Skip =>						assert Substatement(Skip, SeqComp(S1,S2));
								case Assignment(resLHS,resRHS) =>	assert false by { L31(S, res, l); }
								case SeqComp(resS1,resS2) =>		assert ValidLabel(l+[1], S) by {
																		assert slipOfS == slipOf(S, l);
																		assert ValidLabel([1], slipOfS) by {
																			assert IsSeqComp(slipOfS);
																		}
																		LemmaValidLabelOfSlip(l, [1], S);
																	}
																	assert ValidLabel(l+[1], res) by { LemmaValidLabelOfSlip(l, [1], res); }
																	assert ValidLabel(varLabel+[1], S') by { LemmaValidLabelOfSlip(varLabel, [1], S'); }
																	assert ValidLabel(varLabel+[1], SV') by { LemmaValidLabelOfSlip(varLabel, [1], SV'); }

																	assert ValidLabel(l+[2], S) by { LemmaValidLabelOfSlip(l, [2], S); }
																	assert ValidLabel(l+[2], res) by { LemmaValidLabelOfSlip(l, [2], res); }
																	assert ValidLabel(varLabel+[2], S') by { LemmaValidLabelOfSlip(varLabel, [2], S'); }
																	assert ValidLabel(varLabel+[2], SV') by { LemmaValidLabelOfSlip(varLabel, [2], SV'); }
																	
																	assert MatchingSlipsToSSA(S, l+[1], S', varLabel+[1]) by { L34SeqComp(S, l, l+[1], S', varLabel, varLabel+[1]); }
																	assert MatchingSlips(S', SV', varLabel+[1]) by { L35SeqComp(S', SV', varLabel, varLabel+[1]); }
																	assert MatchingSlipsFromSSA(SV', varLabel+[1], res, l+[1]) by { L36SeqComp(SV', varLabel, varLabel+[1], res, l, l+[1]); }
																	assert MatchingSlips(S, res, l+[1]) by { L37SeqComp(S, S', SV', res, l, l+[1], varLabel, varLabel+[1]); }
																	
																	assert MatchingSlipsToSSA(S, l+[2], S', varLabel+[2]) by { L34SeqComp(S, l, l+[2], S', varLabel, varLabel+[2]); }
																	assert MatchingSlips(S', SV', varLabel+[2]) by { L35SeqComp(S', SV', varLabel, varLabel+[2]); }
																	assert MatchingSlipsFromSSA(SV', varLabel+[2], res, l+[2]) by { L36SeqComp(SV', varLabel, varLabel+[2], res, l, l+[2]); }
																	assert MatchingSlips(S, res, l+[2]) by { L37SeqComp(S, S', SV', res, l, l+[2], varLabel, varLabel+[2]); }
											
																	assert maxLabelSize(S) >= |l|  by { LemmaBoundedLabelLength(S, l); }
																	assert maxLabelSize(S) - |l| >= 1 by { LemmaBoundedLabelLength(S, l+[1]); }

																	L20(S, S', SV', res, X, XLsToSSA, l+[1], varLabel+[1]);
																	L20(S, S', SV', res, X, XLsToSSA, l+[2], varLabel+[2]);	
																	
																	assert Substatement(slipOf(res, l), slipOf(S, l)) by { L39(S, res, l); }	
								case IF(resB0,resSthen,resSelse) =>	assert false by { L31(S, res, l); }
								case DO(resB,resSloop) =>			assert false by { L31(S, res, l); }
								}
	case IF(B0,Sthen,Selse) =>	match slipOfRes { // IF or Skip
								case Skip =>						assert Substatement(Skip, IF(B0,Sthen,Selse));
								case Assignment(resLHS,resRHS) =>	assert false by { L32(S, res, l); }
								case SeqComp(resS1,resS2) =>		assert false by { L32(S, res, l); }
								case IF(resB0,resSthen,resSelse) => assume SameBooleanExpressions(B0, resB0);
																	assert ValidLabel(l+[1], S) by { LemmaValidLabelOfSlip(l, [1], S); }
																	assert ValidLabel(l+[1], res) by { LemmaValidLabelOfSlip(l, [1], res); }
																	assert ValidLabel(varLabel+[1,1], S') by {
																		L50(S, l, S', varLabel);
																		LemmaValidLabelOfSlip(varLabel, [1,1], S');
																	}
																	assert ValidLabel(varLabel+[1,1], SV') by {
																		L50(S, l, S', varLabel);
																		LemmaValidLabelOfSlip(varLabel, [1,1], SV');
																	}

																	assert ValidLabel(l+[2], S) by { LemmaValidLabelOfSlip(l, [2], S); }
																	assert ValidLabel(l+[2], res) by { LemmaValidLabelOfSlip(l, [2], res); }
																	assert ValidLabel(varLabel+[2,1], S') by {
																		L50(S, l, S', varLabel);
																		LemmaValidLabelOfSlip(varLabel, [2,1], S');
																	}
																	assert ValidLabel(varLabel+[2,1], SV') by {
																		L50(S, l, S', varLabel);
																		LemmaValidLabelOfSlip(varLabel, [2,1], SV');
																	}

																	assert MatchingSlipsToSSA(S, l+[1], S', varLabel+[1,1]) by { L34IF(S, l, l+[1], S', varLabel, varLabel+[1,1]); }
																	assert MatchingSlips(S', SV', varLabel+[1,1]) by { L35IF(S', SV', varLabel, varLabel+[1,1]); }
																	assert MatchingSlipsFromSSA(SV', varLabel+[1,1], res, l+[1]) by { L36IF(SV', varLabel, varLabel+[1,1], res, l, l+[1]); }
																	assert MatchingSlips(S, res, l+[1]) by { L37IF(S, S', SV', res, l, l+[1], varLabel, varLabel+[1,1]); }
																	
																	assert MatchingSlipsToSSA(S, l+[2], S', varLabel+[2,1]) by { L34IF(S, l, l+[2], S', varLabel, varLabel+[2,1]); }
																	assert MatchingSlips(S', SV', varLabel+[2,1]) by { L35IF(S', SV', varLabel, varLabel+[2,1]); }
																	assert MatchingSlipsFromSSA(SV', varLabel+[2,1], res, l+[2]) by { L36IF(SV', varLabel, varLabel+[2,1], res, l, l+[2]); }
																	assert MatchingSlips(S, res, l+[2]) by { L37IF(S, S', SV', res, l, l+[2], varLabel, varLabel+[2,1]); }
																	
																	assert maxLabelSize(S) >= |l|  by { LemmaBoundedLabelLength(S, l); }
																	assert maxLabelSize(S) - |l| >= 1 by { LemmaBoundedLabelLength(S, l+[1]); }

																	L20(S, S', SV', res, X, XLsToSSA, l+[1], varLabel+[1,1]);
																	L20(S, S', SV', res, X, XLsToSSA, l+[2], varLabel+[2,1]);
																	
																	assert Substatement(slipOf(res, l), slipOf(S, l)) by { L40(S, res, l); }	
								case DO(resB,resSloop) =>			assert false by { L32(S, res, l); }
								}	
	case DO(B,Sloop) =>			match slipOfRes { // DO or Skip
								case Skip =>						assert Substatement(Skip, DO(B,Sloop));
								case Assignment(resLHS,resRHS) =>	assert false by { L33(S, res, l); }
								case SeqComp(resS1,resS2) =>		assert false by { L33(S, res, l); }
								case IF(resB0,resSthen,resSelse) => assert false by { L33(S, res, l); }
								case DO(resB,resSloop) =>			assume SameBooleanExpressions(B, resB);
																	assert ValidLabel(l+[1], S) by { LemmaValidLabelOfSlip(l, [1], S); }
																	assert ValidLabel(l+[1], res) by { LemmaValidLabelOfSlip(l, [1], res); }
																	assert ValidLabel(varLabel+[2,1,1], S') by {
																		L51(S, l, S', varLabel);
																		LemmaValidLabelOfSlip(varLabel, [2,1,1], S');
																	}
																	assert ValidLabel(varLabel+[2,1,1], SV') by {																	
																		L51(res, l, SV', varLabel);
																		LemmaValidLabelOfSlip(varLabel, [2,1,1], SV');
																	}
																	
																	assert MatchingSlipsToSSA(S, l+[1], S', varLabel+[2,1,1]) by { L34DO(S, l, l+[1], S', varLabel, varLabel+[2,1,1]); }
																	assert MatchingSlips(S', SV', varLabel+[2,1,1]) by { L35DO(S', SV', varLabel, varLabel+[2,1,1]); }
																	assert MatchingSlipsFromSSA(SV', varLabel+[2,1,1], res, l+[1]) by { L36DO(SV', varLabel, varLabel+[2,1,1], res, l, l+[1]); }
																	assert MatchingSlips(S, res, l+[1]) by { L37DO(S, S', SV', res, l, l+[1], varLabel, varLabel+[2,1,1]); }
																	
																	assert maxLabelSize(S) >= |l|  by { LemmaBoundedLabelLength(S, l); }
																	assert maxLabelSize(S) - |l| >= 1 by { LemmaBoundedLabelLength(S, l+[1]); }

																	L20(S, S', SV', res, X, XLsToSSA, l+[1], varLabel+[2,1,1]);
																	assert Substatement(slipOf(res, l), slipOf(S, l)) by { L41(S, res, l); }	
								}	
	}
	assert Substatement(slipOf(res, l), slipOf(S, l));
}

lemma LemmaBoundedLabelLength(S: Statement, l: Label)
	requires Valid(S) && Core(S)
	requires ValidLabel(l, S)
	ensures maxLabelSize(S) >= |l|


lemma {:verify false}LemmaValidLabelOfSlip(l1: Label, l2: Label, S: Statement)
	requires Valid(S) && Core(S)
	requires ValidLabel(l1, S)
	requires ValidLabel(l2, slipOf(S, l1))
	ensures ValidLabel(l1+l2, S)
{
	if l1 == [] {
		assert ValidLabel(l1+l2, S) by {
			assert []+l2 == l2;
			assert ValidLabel(l2, slipOf(S, []));
			assert ValidLabel(l2, S);
		}
	}
	else {
		match S {
		case Skip =>				assert false;
		case Assignment(LHS,RHS) =>	assert false;
		case SeqComp(S1,S2) =>		if l1[0] == 1 { LemmaValidLabelOfSlip(l1[1..], l2, S1); } else { LemmaValidLabelOfSlip(l1[1..], l2, S2); }
		case IF(B0,Sthen,Selse) =>	if l1[0] == 1 { LemmaValidLabelOfSlip(l1[1..], l2, Sthen); } else { LemmaValidLabelOfSlip(l1[1..], l2, Selse); }
		case DO(B,Sloop) =>			if l1[0] == 1 { LemmaValidLabelOfSlip(l1[1..], l2, Sloop); } else { assert false; }
		}
	}

	assert ValidLabel(l1+l2, S);
}

lemma {:verify true}L30(S: Statement, res: Statement, l: Label)
	requires Valid(S) && Valid(res)
	requires Core(S) && Core(res)
	requires ValidLabel(l, S)
	requires ValidLabel(l, res)
	requires IsAssignment(slipOf(S, l))
	requires !IsAssignment(slipOf(res, l)) && !IsSkip(slipOf(res, l))
	requires MatchingSlips(S, res, l)
	ensures Substatement(slipOf(res, l), slipOf(S, l))
{
	var slipOfS := slipOf(S, l);
	var slipOfRes := slipOf(res, l);

	assert !IsAssignment(slipOfRes) && !IsSkip(slipOfRes);
	assert IsAssignment(slipOfRes) || IsSkip(slipOfRes) by {
		assert MatchingSlips(S, res, l) && IsAssignment(slipOfS);
	}
	// ==>
	assert Substatement(slipOfRes, slipOfS);
}

lemma {:verify true}L31(S: Statement, res: Statement, l: Label)
	requires Valid(S) && Valid(res)
	requires Core(S) && Core(res)
	requires ValidLabel(l, S)
	requires ValidLabel(l, res)
	requires IsSeqComp(slipOf(S, l))
	requires !IsSeqComp(slipOf(res, l)) && !IsSkip(slipOf(res, l))
	requires MatchingSlips(S, res, l)
	ensures Substatement(slipOf(res, l), slipOf(S, l))
{
	var slipOfS := slipOf(S, l);
	var slipOfRes := slipOf(res, l);

	assert !IsSeqComp(slipOfRes) && !IsSkip(slipOfRes);
	assert IsSeqComp(slipOfRes) || IsSkip(slipOfRes) by {
		assert MatchingSlips(S, res, l) && IsSeqComp(slipOfS);
	}
	// ==>
	assert Substatement(slipOfRes, slipOfS);
}

lemma {:verify true}L32(S: Statement, res: Statement, l: Label)
	requires Valid(S) && Valid(res)
	requires Core(S) && Core(res)
	requires ValidLabel(l, S)
	requires ValidLabel(l, res)
	requires IsIF(slipOf(S, l))
	requires !IsIF(slipOf(res, l)) && !IsSkip(slipOf(res, l))
	requires MatchingSlips(S, res, l)
	ensures Substatement(slipOf(res, l), slipOf(S, l))
{
	var slipOfS := slipOf(S, l);
	var slipOfRes := slipOf(res, l);

	assert !IsIF(slipOfRes) && !IsSkip(slipOfRes);
	assert IsIF(slipOfRes) || IsSkip(slipOfRes) by {
		assert MatchingSlips(S, res, l) && IsIF(slipOfS);
	}
	// ==>
	assert Substatement(slipOfRes, slipOfS);
}

lemma {:verify true}L33(S: Statement, res: Statement, l: Label)
	requires Valid(S) && Valid(res)
	requires Core(S) && Core(res)
	requires ValidLabel(l, S)
	requires ValidLabel(l, res)
	requires IsDO(slipOf(S, l))
	requires !IsDO(slipOf(res, l)) && !IsSkip(slipOf(res, l))
	requires MatchingSlips(S, res, l)
	ensures Substatement(slipOf(res, l), slipOf(S, l))
{
	var slipOfS := slipOf(S, l);
	var slipOfRes := slipOf(res, l);

	assert !IsDO(slipOfRes) && !IsSkip(slipOfRes);
	assert IsDO(slipOfRes) || IsSkip(slipOfRes) by {
		assert MatchingSlips(S, res, l) && IsDO(slipOfS);
	}
	// ==>
	assert Substatement(slipOfRes, slipOfS);
}

lemma {:verify true}L22(S: Statement, S': Statement, SV': Statement, res: Statement, X: seq<Variable>, XLsToSSA: seq<set<Variable>>, l: Label, varLabel: Label)
	requires Valid(S) && Valid(S') && Valid(SV') && Valid(res)
	requires Core(S) && Core(S') && Core(SV') && Core(res)
	requires ValidLabel(l, S)
	requires ValidLabel(l, res)
	requires ValidLabel(varLabel, SV')
	requires ValidLabel(varLabel, S')
	requires MatchingSlipsToSSA(S, l, S', varLabel) // add to tossa postcodition
	requires MatchingSlips(S', SV', varLabel)
	requires MatchingSlipsFromSSA(SV', varLabel, res, l) // add to fromssa postcodition
	// ==>
	requires MatchingSlips(S, res, l)
	requires NoSelfAssignments(S')
	requires MergedVars1(S', S, XLsToSSA, X) // ToSSA Postcondition
	requires Substatement(SV', S')	
	requires NoSelfAssignments(SV')
	requires MergedVars1(SV', res, XLsToSSA, X) // FromSSA Postcondition
	requires IsAssignment(slipOf(S,l))
	requires IsAssignment(slipOf(res,l))
	requires exists LHS,RHS,resLHS,resRHS :: slipOf(S,l) == Assignment(LHS,RHS) && slipOf(res,l) == Assignment(resLHS,resRHS) 
	ensures forall LHS,RHS,resLHS,resRHS :: slipOf(S,l) == Assignment(LHS,RHS) && slipOf(res,l) == Assignment(resLHS,resRHS) ==> Subassignment(resLHS, resRHS, LHS, RHS)
{
	var slipOfS := slipOf(S,l);
	var slipOfRes := slipOf(res,l);
	var slipOfSV' := slipOf(SV',varLabel);
	var slipOfS' := slipOf(S',varLabel);
	match slipOfS {	
	case Assignment(LHS,RHS) =>
		match slipOfRes {	
		case Assignment(resLHS,resRHS) =>
			assert Subassignment(resLHS, resRHS, LHS, RHS) by { // sum := 0 <= sum,prod := 0,1 
				assert IsAssignment(slipOfSV') by { assert MatchingSlipsFromSSA(SV', varLabel, res, l); }
				assert IsAssignment(slipOfS');
				assert Substatement(slipOfSV', slipOfS') by { L38(SV', S', varLabel); /* Prove lemma! */}
				
				assert RemoveEmptyAssignments(Rename(slipOf(SV', varLabel), XLsToSSA, X)) == slipOf(res, l) by { L42(SV', varLabel, res, l, X, XLsToSSA); /* Prove lemma! */}
				assert RemoveEmptyAssignments(Rename(slipOf(S', varLabel), XLsToSSA, X)) == slipOf(S, l) by { L43(S', varLabel, S, l, X, XLsToSSA); /* Prove lemma! */}
				L44(S, S', SV', res, l, varLabel, X, XLsToSSA);	/* Prove lemma! */
			}
	
			assert Subassignment(resLHS, resRHS, LHS, RHS);				 
		}

		assert forall resLHS,resRHS :: slipOfRes == Assignment(resLHS,resRHS) ==> Subassignment(resLHS, resRHS, LHS, RHS);
	}

	assert forall LHS,RHS,resLHS,resRHS :: slipOfS == Assignment(LHS,RHS) && slipOfRes == Assignment(resLHS,resRHS) ==> Subassignment(resLHS, resRHS, LHS, RHS);
}


predicate MatchingSlips(S: Statement, S': Statement, l: Label)
	reads *
	requires Valid(S) && Valid(S')
	requires Core(S) && Core(S')
	requires ValidLabel(l, S)
	requires ValidLabel(l, S')
{
	var slipOfS := slipOf(S, l);
	var slipOfS' := slipOf(S', l);
	
	match slipOfS {
	case Skip =>				IsSkip(slipOfS')
	case Assignment(LHS,RHS) =>	IsSkip(slipOfS') || IsAssignment(slipOfS')
	case SeqComp(S1,S2) =>		IsSkip(slipOfS') || IsSeqComp(slipOfS')
	case IF(B,Sthen,Selse) =>	IsSkip(slipOfS') || IsIF(slipOfS')
	case DO(B,Sloop) =>			IsSkip(slipOfS') || IsDO(slipOfS')
	}	
}

predicate MatchingSlipsToSSA(S: Statement, l: Label, S': Statement, l': Label)
	reads *
	requires Valid(S) && Valid(S')
	requires Core(S) && Core(S')
	requires ValidLabel(l, S)
	requires ValidLabel(l', S')
	//ensures IsIF(slipOf(S, l)) ==> ValidLabel([1,1], slipOf(S', l')) //call lemma instead
	//ensures IsIF(slipOf(S, l)) ==> ValidLabel([2,1], slipOf(S', l')) //call lemma instead
	//ensures IsDO(slipOf(S, l)) ==> ValidLabel([2,1,1], slipOf(S', l')) //call lemma instead
{
	var slipOfS := slipOf(S, l);
	var slipOfS' := slipOf(S', l');
	
	match slipOfS {
	case Skip =>				IsSkip(slipOfS')
	case Assignment(LHS,RHS) =>	IsAssignment(slipOfS')
	case SeqComp(S1,S2) =>		IsSeqComp(slipOfS')
	case IF(B,Sthen,Selse) =>	IsIF(slipOfS') &&
								match slipOfS' {
								case IF(B',Sthen',Selse') => 
									IsSeqComp(Sthen') && IsSeqComp(Selse')
								}
	case DO(B,Sloop) =>			IsSeqComp(slipOfS') &&
								match slipOfS' {
								case SeqComp(S1',S2') =>
									IsAssignment(S1') && IsDO(S2') &&
									match S2' {
									case DO(B', Sloop') => /*assert IsDO(slipOf(S, l)) ==> ValidLabel([2,1,1], slipOf(S', l')) by {
															   assert IsDO(slipOf(S, l)) && IsSeqComp(slipOfS') ==> ValidLabel([2], slipOf(S', l'));
															   assert IsDO(slipOf(S, l)) && IsSeqComp(slipOfS') && IsDO(S2') ==> ValidLabel([2,1], slipOf(S', l'));
															   assert IsDO(slipOf(S, l)) && IsSeqComp(slipOfS') && IsDO(S2') && IsSeqComp(Sloop') ==> ValidLabel([2,1,1], slipOf(S', l'));
														   }*/
														   IsSeqComp(Sloop') // maybe add another match
									}
								}
	}	
}

predicate MatchingSlipsFromSSA(S': Statement, l': Label, S: Statement, l: Label)
	reads *
	requires Valid(S) && Valid(S')
	requires Core(S) && Core(S')
	requires ValidLabel(l, S)
	requires ValidLabel(l', S')
{
	MatchingSlipsToSSA(S, l, S', l')
}

lemma L50(S: Statement, l: Label, S': Statement, l': Label)
	requires Valid(S) && Valid(S')
	requires Core(S) && Core(S')
	requires ValidLabel(l, S)
	requires ValidLabel(l', S')
	requires MatchingSlipsToSSA(S, l, S', l')
	requires IsIF(slipOf(S, l))
	ensures exists b :: ValidLabel([b,1], slipOf(S', l'))

lemma L51(S: Statement, l: Label, S': Statement, l': Label)
	requires Valid(S) && Valid(S')
	requires Core(S) && Core(S')
	requires ValidLabel(l, S)
	requires ValidLabel(l', S')
	requires MatchingSlipsToSSA(S, l, S', l')
	requires IsDO(slipOf(S, l))
	ensures ValidLabel([2,1,1], slipOf(S', l'))

lemma L34SeqComp(S: Statement, l: Label, newL: Label, S': Statement, varLabel: Label, newVarLabel: Label)
	requires Valid(S) && Valid(S')
	requires Core(S) && Core(S')
	requires ValidLabel(l, S) && ValidLabel(newL, S)
	requires ValidLabel(varLabel, S') && ValidLabel(newVarLabel, S')
	requires IsSeqComp(slipOf(S, l))
	requires exists b :: newVarLabel == varLabel + [b] && newL == l + [b]
	requires MatchingSlipsToSSA(S, l, S', varLabel)
	ensures MatchingSlipsToSSA(S, newL, S', newVarLabel)

lemma L34IF(S: Statement, l: Label, newL: Label, S': Statement, varLabel: Label, newVarLabel: Label)
	requires Valid(S) && Valid(S')
	requires Core(S) && Core(S')
	requires ValidLabel(l, S) && ValidLabel(newL, S)
	requires ValidLabel(varLabel, S') && ValidLabel(newVarLabel, S')
	requires IsIF(slipOf(S, l))
	requires exists b :: newVarLabel == varLabel + [b,1] && newL == l + [b]
	requires MatchingSlipsToSSA(S, l, S', varLabel)
	ensures MatchingSlipsToSSA(S, newL, S', newVarLabel)

lemma L34DO(S: Statement, l: Label, newL: Label, S': Statement, varLabel: Label, newVarLabel: Label)
	requires Valid(S) && Valid(S')
	requires Core(S) && Core(S')
	requires ValidLabel(l, S) && ValidLabel(newL, S)
	requires ValidLabel(varLabel, S') && ValidLabel(newVarLabel, S')
	requires IsDO(slipOf(S, l))
	requires newVarLabel == varLabel + [2,1,1] && newL == l + [1]
	requires MatchingSlipsToSSA(S, l, S', varLabel)
	ensures MatchingSlipsToSSA(S, newL, S', newVarLabel)

lemma L35SeqComp(S': Statement, SV': Statement, varLabel: Label, newVarLabel: Label)
	requires Valid(S') && Valid(SV')
	requires Core(S') && Core(SV')
	requires ValidLabel(varLabel, S') && ValidLabel(newVarLabel, S')
	requires ValidLabel(varLabel, SV') && ValidLabel(newVarLabel, SV')
	requires IsSeqComp(slipOf(S', varLabel))
	requires exists b :: newVarLabel == varLabel + [b]
	requires MatchingSlips(S', SV', varLabel)
	ensures MatchingSlips(S', SV', newVarLabel)
	
lemma L35IF(S': Statement, SV': Statement, varLabel: Label, newVarLabel: Label)
	requires Valid(S') && Valid(SV')
	requires Core(S') && Core(SV')
	requires ValidLabel(varLabel, S') && ValidLabel(newVarLabel, S')
	requires ValidLabel(varLabel, SV') && ValidLabel(newVarLabel, SV')
	requires IsIF(slipOf(S', varLabel))
	requires exists b :: newVarLabel == varLabel + [b,1]
	requires MatchingSlips(S', SV', varLabel)
	ensures MatchingSlips(S', SV', newVarLabel)

lemma L35DO(S': Statement, SV': Statement, varLabel: Label, newVarLabel: Label)
	requires Valid(S') && Valid(SV')
	requires Core(S') && Core(SV')
	requires ValidLabel(varLabel, S') && ValidLabel(newVarLabel, S')
	requires ValidLabel(varLabel, SV') && ValidLabel(newVarLabel, SV')
	//requires IsDO(slipOf(S', varLabel))
	requires newVarLabel == varLabel + [2,1,1]
	requires MatchingSlips(S', SV', varLabel)
	ensures MatchingSlips(S', SV', newVarLabel)

lemma L36SeqComp(SV': Statement, varLabel: Label, newVarLabel: Label, res: Statement, l: Label, newL: Label)
	requires Valid(SV') && Valid(res)
	requires Core(SV') && Core(res)
	requires ValidLabel(varLabel, SV') && ValidLabel(newVarLabel, SV')
	requires ValidLabel(l, res) && ValidLabel(newL, res)
	requires IsSeqComp(slipOf(SV', varLabel))
	requires exists b :: newVarLabel == varLabel + [b] && newL == l + [b]
	requires MatchingSlipsFromSSA(SV', varLabel, res, l)
	ensures MatchingSlipsFromSSA(SV', newVarLabel, res, newL)

lemma L36IF(SV': Statement, varLabel: Label, newVarLabel: Label, res: Statement, l: Label, newL: Label)
	requires Valid(SV') && Valid(res)
	requires Core(SV') && Core(res)
	requires ValidLabel(varLabel, SV') && ValidLabel(newVarLabel, SV')
	requires ValidLabel(l, res) && ValidLabel(newL, res)
	requires IsIF(slipOf(SV', varLabel))
	requires exists b :: newVarLabel == varLabel + [b,1] && newL == l + [b]
	requires MatchingSlipsFromSSA(SV', varLabel, res, l)
	ensures MatchingSlipsFromSSA(SV', newVarLabel, res, newL)

lemma L36DO(SV': Statement, varLabel: Label, newVarLabel: Label, res: Statement, l: Label, newL: Label)
	requires Valid(SV') && Valid(res)
	requires Core(SV') && Core(res)
	requires ValidLabel(varLabel, SV') && ValidLabel(newVarLabel, SV')
	requires ValidLabel(l, res) && ValidLabel(newL, res)
	//requires IsDO(slipOf(SV', varLabel))
	requires newVarLabel == varLabel + [2,1,1] && newL == l + [1]
	requires MatchingSlipsFromSSA(SV', varLabel, res, l)
	ensures MatchingSlipsFromSSA(SV', newVarLabel, res, newL)

lemma L37SeqComp(S: Statement, S': Statement, SV': Statement, res: Statement, l: Label, newL: Label, varLabel: Label, newVarLabel: Label)
	requires Valid(S) && Valid(S') && Valid(SV') && Valid(res)
	requires Core(S) && Core(S') && Core(SV') && Core(res)
	requires ValidLabel(l, S) && ValidLabel(newL, S)
	requires ValidLabel(varLabel, S') && ValidLabel(newVarLabel, S')
	requires ValidLabel(varLabel, SV') && ValidLabel(newVarLabel, SV')
	requires ValidLabel(l, res) && ValidLabel(newL, res)
	requires IsSeqComp(slipOf(S, l))
	requires exists b :: newVarLabel == varLabel + [b] && newL == l + [b]
	requires MatchingSlips(S, res, l)
	requires MatchingSlipsToSSA(S, newL, S', newVarLabel)
	requires MatchingSlips(S', SV', newVarLabel)
	requires MatchingSlipsFromSSA(SV', newVarLabel, res, newL)
	ensures MatchingSlips(S, res, newL)

lemma L37IF(S: Statement, S': Statement, SV': Statement, res: Statement, l: Label, newL: Label, varLabel: Label, newVarLabel: Label)
	requires Valid(S) && Valid(S') && Valid(SV') && Valid(res)
	requires Core(S) && Core(S') && Core(SV') && Core(res)
	requires ValidLabel(l, S) && ValidLabel(newL, S)
	requires ValidLabel(varLabel, S') && ValidLabel(newVarLabel, S')
	requires ValidLabel(varLabel, SV') && ValidLabel(newVarLabel, SV')
	requires ValidLabel(l, res) && ValidLabel(newL, res)
	requires IsIF(slipOf(S, l))
	requires exists b :: newVarLabel == varLabel + [b,1] && newL == l + [b]
	requires MatchingSlips(S, res, l)
	requires MatchingSlipsToSSA(S, newL, S', newVarLabel)
	requires MatchingSlips(S', SV', newVarLabel)
	requires MatchingSlipsFromSSA(SV', newVarLabel, res, newL)
	ensures MatchingSlips(S, res, newL)

lemma L37DO(S: Statement, S': Statement, SV': Statement, res: Statement, l: Label, newL: Label, varLabel: Label, newVarLabel: Label)
	requires Valid(S) && Valid(S') && Valid(SV') && Valid(res)
	requires Core(S) && Core(S') && Core(SV') && Core(res)
	requires ValidLabel(l, S) && ValidLabel(newL, S)
	requires ValidLabel(varLabel, S') && ValidLabel(newVarLabel, S')
	requires ValidLabel(varLabel, SV') && ValidLabel(newVarLabel, SV')
	requires ValidLabel(l, res) && ValidLabel(newL, res)
	requires IsDO(slipOf(S, l))
	requires newVarLabel == varLabel + [2,1,1] && newL == l + [1]
	requires MatchingSlips(S, res, l)
	requires MatchingSlipsToSSA(S, newL, S', newVarLabel)
	requires MatchingSlips(S', SV', newVarLabel)
	requires MatchingSlipsFromSSA(SV', newVarLabel, res, newL)
	ensures MatchingSlips(S, res, newL)

lemma {:verify true}L38(SV': Statement, S': Statement, varLabel: Label)
	requires Valid(SV') && Valid(S')
	requires Core(SV') && Core(S')
	requires Substatement(SV', S')
	requires ValidLabel(varLabel, SV')
	requires ValidLabel(varLabel, S')
	requires MatchingSlips(S', SV', varLabel)
	ensures Substatement(slipOf(SV',varLabel), slipOf(S',varLabel))
	decreases |varLabel|
{
	if varLabel == [] { assert Substatement(slipOf(SV',[]), slipOf(S',[])); }
	else 
	{
	match S' {
	case Skip =>				assert SV' == Skip;
	case Assignment(LHS,RHS) =>	match SV' {
								case Skip =>					assert true;
								case Assignment(LHS',RHS') =>	assert Subassignment(LHS', RHS', LHS, RHS);
								case SeqComp(S1',S2') =>		assert false;
								case IF(B0',Sthen',Selse') =>	assert false;
								case DO(B',Sloop') =>			assert false;
								}
	case SeqComp(S1,S2) =>		match SV' {
								case Skip =>					assert true;
								case Assignment(LHS',RHS') =>	assert false;
								case SeqComp(S1',S2') =>		if varLabel[0] == 1 { L38(S1', S1, varLabel[1..]); } 
																else { L38(S2', S2, varLabel[1..]); }
								case IF(B0',Sthen',Selse') =>	assert false;
								case DO(B',Sloop') =>			assert false;
								}	
	case IF(B0,Sthen,Selse) =>	match SV' {
								case Skip => assert true;
								case Assignment(LHS',RHS') =>	assert false;
								case SeqComp(S1',S2') =>		assert false;								
								case IF(B0',Sthen',Selse') =>	assert SameBooleanExpressions(B0, B0') by { assert Substatement(SV', S'); }
																if varLabel[0] == 1 { L38(Sthen', Sthen, varLabel[1..]); }
																else { L38(Selse', Selse, varLabel[1..]); }
								case DO(B',Sloop') =>			assert false;
								}
	case DO(B,Sloop) =>			match SV' {
								case Skip =>					assert true;
								case Assignment(LHS',RHS') =>	assert false;
								case SeqComp(S1',S2') =>		assert false;								
								case IF(B0',Sthen',Selse') =>	assert false;
								case DO(B',Sloop') =>			assert SameBooleanExpressions(B, B') by { assert Substatement(SV', S'); }
																L38(Sloop', Sloop, varLabel[1..]);
								}
	}
	}
}

lemma L39(S: Statement, res: Statement, l: Label)
	requires Valid(S) && Core(S) && Valid(res) && Core(res)
	requires ValidLabel(l, S) && ValidLabel(l, res)
	requires IsSeqComp(slipOf(S,l)) && IsSeqComp(slipOf(res,l))
	requires ValidLabel(l+[1], S) && ValidLabel(l+[1], res)
	requires ValidLabel(l+[2], S) && ValidLabel(l+[2], res)
	requires MatchingSlips(S, res, l)
	requires Substatement(slipOf(res, l+[1]), slipOf(S, l+[1]))
	requires Substatement(slipOf(res, l+[2]), slipOf(S, l+[2]))
	ensures Substatement(slipOf(res, l), slipOf(S, l))

lemma L40(S: Statement, res: Statement, l: Label)
	requires Valid(S) && Core(S) && Valid(res) && Core(res)
	requires ValidLabel(l, S) && ValidLabel(l, res)
	requires IsIF(slipOf(S,l)) && IsIF(slipOf(res,l))
	requires ValidLabel(l+[1], S) && ValidLabel(l+[1], res)
	requires ValidLabel(l+[2], S) && ValidLabel(l+[2], res)
	requires MatchingSlips(S, res, l)
	requires Substatement(slipOf(res, l+[1]), slipOf(S, l+[1]))
	requires Substatement(slipOf(res, l+[2]), slipOf(S, l+[2]))
	ensures Substatement(slipOf(res, l), slipOf(S, l))

lemma L41(S: Statement, res: Statement, l: Label)
	requires Valid(S) && Core(S) && Valid(res) && Core(res)
	requires ValidLabel(l, S) && ValidLabel(l, res)
	requires IsDO(slipOf(S,l)) && IsDO(slipOf(res,l))
	requires ValidLabel(l+[1], S) && ValidLabel(l+[1], res)
	requires MatchingSlips(S, res, l)
	requires Substatement(slipOf(res, l+[1]), slipOf(S, l+[1]))
	ensures Substatement(slipOf(res, l), slipOf(S, l))
	
lemma L42(SV': Statement, varLabel: Label, res: Statement, l: Label, X: seq<Variable>, XLsToSSA: seq<set<Variable>>)
	requires Valid(SV') && Core(SV') && Valid(res) && Core(res)
	requires RemoveEmptyAssignments(Rename(SV', XLsToSSA, X)) == res
	requires ValidLabel(l, res)
	requires ValidLabel(varLabel, SV')
	requires IsAssignment(slipOf(SV', varLabel))
	requires IsAssignment(slipOf(res, l))
	requires MatchingSlipsFromSSA(SV', varLabel, res, l)
	ensures RemoveEmptyAssignments(Rename(slipOf(SV', varLabel), XLsToSSA, X)) == slipOf(res, l) // slipOfSV': sum2 := 0  slipOfRes: sum := 0

lemma L43(S': Statement, varLabel: Label, S: Statement, l: Label, X: seq<Variable>, XLsToSSA: seq<set<Variable>>)
	requires Valid(S') && Core(S') && Valid(S) && Core(S)
	requires RemoveEmptyAssignments(Rename(S', XLsToSSA, X)) == S
	requires ValidLabel(l, S)
	requires ValidLabel(varLabel, S')
	requires IsAssignment(slipOf(S', varLabel))
	requires IsAssignment(slipOf(S, l))
	requires MatchingSlipsToSSA(S, l, S', varLabel)
	ensures RemoveEmptyAssignments(Rename(slipOf(S', varLabel), XLsToSSA, X)) == slipOf(S, l) // slipOfS': sum2 := 0  slipOfS: sum := 0

lemma L44(S: Statement, S': Statement, SV': Statement, res: Statement, l: Label, varLabel: Label, X: seq<Variable>, XLsToSSA: seq<set<Variable>>)
	requires Valid(S) && Valid(S') && Valid(SV') && Valid(res)
	requires Core(S) && Core(S') && Core(SV') && Core(res)
	requires ValidLabel(l, S) && ValidLabel(varLabel, S') && ValidLabel(varLabel, SV') && ValidLabel(l, res)
	requires IsAssignment(slipOf(S, l)) && IsAssignment(slipOf(S', varLabel)) && IsAssignment(slipOf(SV', varLabel)) && IsAssignment(slipOf(res, l))
	requires MatchingSlips(S, res, l)
	requires MatchingSlipsToSSA(S, l, S', varLabel)
	requires MatchingSlips(S', SV', varLabel)
	requires MatchingSlipsFromSSA(SV', varLabel, res, l)
	requires Substatement(SV', S')
	requires RemoveEmptyAssignments(Rename(slipOf(SV', varLabel), XLsToSSA, X)) == slipOf(res, l)
	requires RemoveEmptyAssignments(Rename(slipOf(S', varLabel), XLsToSSA, X)) == slipOf(S, l)
	ensures Substatement(slipOf(res, l), slipOf(S, l))