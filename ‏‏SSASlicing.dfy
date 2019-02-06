include "Definitions.dfy"
include "Substitutions.dfy"
include "Util.dfy"
include "CorrectnessSSA.dfy"
include "SlideDG.dfy"
include "VarSlideDG.dfy"
include "SSA.dfy"
include "Slicing.dfy"
include "ProofUtil.dfy"

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
	requires NoSelfAssignments(S) && NoEmptyAssignments(S)
	requires Valid(S) && Core(S)
	decreases *
	ensures SliceOf(S,V).1 == res 
{
	var varSlideDG := ComputeVarSlideDG(S); // not needed

	res := ComputeSSASlice(S, V, varSlideDG);
}

method {:verify true}ComputeSSASlice(S: Statement, V: set<Variable>, ghost varSlideDG: VarSlideDG) returns (res: Statement)
	requires NoSelfAssignments(S) && NoEmptyAssignments(S)
	requires Valid(S) && Core(S)
	requires VarSlideDGOf(varSlideDG, S)
	decreases *
	ensures Valid(res) && Core(res)
	//ensures var varSlidesRes: set<VarSlide> := varSlidesOf(res, V); forall Sm :: Sm in varSlidesRes <==> (Sm.0 in V || (exists Sn: VarSlide :: Sn.0 in V && VarSlideDGReachable(varSlideDG, Sm, Sn, varSlideDG.1)))	 // Implement VarSlideDGReachable
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
	assume Substatement(SV', S'); /////////////////////////////////////////////////////////////////////
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
	
	// From SSA
	var XL1i := liveOnEntryXSeq;
	var XL2f := liveOnExitXSeq;
	res := FromSSA(SV', X, XL1i, XL2f, Y, XLs, vsSSA, V, S', V', varSlideDGS');
	var XLsSeq := XLsToSeq(X, XLs, vsSSA);
	assert res == RemoveEmptyAssignments(Rename(SV', XLsSeq, X)); // FromSSA Post-condition

	//assert forall U: set<Variable> :: slidesOf(res, U) <= slidesOf(S, U) <= slidesOf(S, def(S));

	assert Substatement(res, S);
	assert Substatement(SliceOfSV.1, S);
	
	assume def(res) <= def(S);// by { assert Core(S) && Substatement(res,S); }
	assert allSlidesOf(res) == slidesOf(res, def(S)) == SlideDGOf(S, CFGOf(S)).1;
	assume def(SliceOfSV.1) <= def(S);// by { assert Core(S) && Substatement(SliceOfSV,S); }
	assert allSlidesOf(SliceOfSV.1) == slidesOf(SliceOfSV.1, def(S));
	assert slidesOf(res, def(S)) <= slidesOf(S, def(S));
	assert slidesSV == slidesOf(SliceOfSV.1, def(S)) == SliceOfSV.0 <= slidesOf(S, def(S));

	// ensures SliceOfSV == res :
	assert slidesOf(res, def(S)) == slidesOf(SliceOfSV.1, def(S)) by {
		forall slide | slide in slidesOf(S, def(S)) ensures slide in slidesOf(res, def(S)) <==> slide in slidesOf(SliceOfSV.1, def(S)) {
			LemmaSlidesSVToVarSlidesSV(slide, S, S', SV', slidesSV, varSlidesSV, X, V, V', varSlideDGS', vsSSA);
			//assert forall slide :: slide in SlideDGOf(S, CFGOf(S)).1 ==> (slide in slidesSV <==> VarSlideOf(S, S', slide) in varSlidesSV);
			assert slide in slidesSV <==> VarSlideOf(S, S', slide) in varSlidesSV;

			LemmaVarSlidesSVToRes(slide, S, S', SV', res, slidesSV, varSlidesSV, X, V, V', varSlideDGS', vsSSA, XLsSeq, glob(S));
			//assert forall slide :: slide in /*SlideDGOf(S, CFGOf(S)).1*/ slidesOf(S, def(S)) ==> (VarSlideOf(S, S', slide) in varSlidesSV <==> slide in slidesOf(res, def(S)));
			assert VarSlideOf(S, S', slide) in varSlidesSV <==> slide in slidesOf(res, def(S));
		}
	}
	
	LemmaIdenticalSlices(S, SliceOfSV.1, res);
}

lemma LemmaIdenticalSlices(S: Statement, S1: Statement, S2: Statement)
	requires Valid(S) && Valid(S1) && Valid(S2)
	requires Core(S) && Core(S1) && Core(S2)
	//requires Substatement(S1, S)
	//requires Substatement(S2, S)
	requires allSlidesOf(S1) == allSlidesOf(S2) // check multiple assignments
	ensures S1 == S2

lemma LemmaVarSlidesSVToRes(slide: Slide, S: Statement, S': Statement, SV': Statement, res: Statement, slidesSV: set<Slide>, varSlidesSV: set<VarSlide>, X: seq<Variable>, V: set<Variable>, V': set<Variable>, varSlideDGS': VarSlideDG, vsSSA: VariablesSSA, XLs: seq<set<Variable>>, globS: set<Variable>)
	requires NoSelfAssignments(S) && NoEmptyAssignments(S)
	requires ValidXLs(globS, XLs, X)
	requires Valid(S) && Core(S)
	requires Valid(S') && Core(S')
	requires Valid(SV') && Core(SV')
	requires Valid(res) && Core(res)
	requires ValidVsSSA(vsSSA)
	requires slide in slidesOf(S, def(S))
	requires Substatement(res, S)
	requires Substatement(SV', S')
	requires res == RemoveEmptyAssignments(Rename(SV', XLs, X)) // FromSSA Post-condition
	requires forall Sm :: Sm in slidesSV <==> (Sm in slidesOf(S,def(S)) && exists Sn :: Sn in finalDefSlides(S, SlideDGOf(S, CFGOf(S)), CFGOf(S), V) && SlideDGReachable(SlideDGOf(S, CFGOf(S)), Sm, Sn, SlideDGOf(S, CFGOf(S)).1));
	requires forall vSlide :: vSlide in varSlidesSV ==> (vSlide in varSlidesOf(S,def(S)) && exists Sn: VarSlide :: Sn.0 in V' && VarSlideDGReachable(varSlideDGS', vSlide, Sn, varSlideDGS'.1))
	requires slide in slidesSV <==> VarSlideOf(S, S', slide) in varSlidesSV
	ensures VarSlideOf(S, S', slide) in varSlidesSV <==> slide in slidesOf(res, def(S))
{
	assert VarSlideOf(S, S', slide) in varSlidesSV <==> slide in slidesOf(res, def(S)) by {
		var vSlide := VarSlideOf(S, S', slide);

		if (vSlide in varSlidesSV)
		{
			L60(slide, vSlide, S, S', SV', res, slidesSV, varSlidesSV, V, V', varSlideDGS', X, XLs, globS);
			assert slide in slidesOf(res, def(S));
		}
		else // vSlide !in varSlidesS
		{
			L61(slide, vSlide, S, S', SV', res, slidesSV, varSlidesSV, V, V', varSlideDGS');
			assert slide !in slidesOf(res, def(S));
		}
	}
}

lemma L60(slide: Slide, vSlide: VarSlide, S: Statement, S': Statement, SV': Statement, res: Statement, slidesSV: set<Slide>, varSlidesSV: set<VarSlide>, V: set<Variable>, V': set<Variable>, varSlideDGS': VarSlideDG, X: seq<Variable>, XLs: seq<set<Variable>>, globS: set<Variable>)
	requires NoSelfAssignments(S) && NoEmptyAssignments(S)
	requires ValidXLs(globS, XLs, X)
	requires Valid(S) && Core(S)
	requires Valid(S') && Core(S')
	requires Valid(SV') && Core(SV')
	requires Valid(res) && Core(res)
	requires slide in slidesOf(S, def(S))
	requires vSlide == VarSlideOf(S, S', slide) && vSlide in varSlidesSV
	requires Substatement(res, S)
	requires Substatement(SV', S')
	requires forall Sm :: Sm in slidesSV <==> (Sm in slidesOf(S,def(S)) && exists Sn :: Sn in finalDefSlides(S, SlideDGOf(S, CFGOf(S)), CFGOf(S), V) && SlideDGReachable(SlideDGOf(S, CFGOf(S)), Sm, Sn, SlideDGOf(S, CFGOf(S)).1));
	requires forall vSlide :: vSlide in varSlidesSV ==> (vSlide in varSlidesOf(S,def(S)) && exists Sn: VarSlide :: Sn.0 in V' && VarSlideDGReachable(varSlideDGS', vSlide, Sn, varSlideDGS'.1))
	requires slide in slidesSV <==> VarSlideOf(S, S', slide) in varSlidesSV
	requires res == RemoveEmptyAssignments(Rename(SV', XLs, X)) // FromSSA Post-condition
	ensures slide in slidesOf(res, def(S))
{
	assert slide in slidesOf(S, def(S));
	assert slide in slidesSV by { assert slide in slidesSV <==> VarSlideOf(S, S', slide) in varSlidesSV; }
	assert forall vSlide :: vSlide in varSlidesSV ==> (vSlide in varSlidesOf(S,def(S)) && exists Sn: VarSlide :: Sn.0 in V' && VarSlideDGReachable(varSlideDGS', vSlide, Sn, varSlideDGS'.1));
	assert vSlide in varSlidesOf(S,def(S)) && exists Sn: VarSlide :: Sn.0 in V' && VarSlideDGReachable(varSlideDGS', vSlide, Sn, varSlideDGS'.1);
					
	var v := slide.1;
	match slide.0 {
	case Node(l) => 
		var vLabel := VarLabelOf(S, S', l);
		assert ValidLabel(vLabel, S');
			
		assert ValidLabel(l, res) && IsAssignment(slipOf(res, l)) && v in def(slipOf(res, l)) by {
			assert ValidLabel(l, res) by {
				assert ValidLabel(l, S);
				ghost var allLabelsRenameSV' := allLabelsOf(Rename(SV', XLs, X));
				ghost var selfEmptyLabelsSV' := selfEmptyLabelsOf(Rename(SV', XLs, X), allLabelsRenameSV');
				var l' := LabelOf(selfEmptyLabelsSV', vLabel);
				assume ValidLabel(vLabel, SV');
				assume ValidLabel(l', res);
				IdenticalLabels(S, S', SV', res, l, vLabel, l', XLs, X, selfEmptyLabelsSV', globS);
			}
			assert IsAssignment(slipOf(res, l)) by {
				assert ValidLabel(l, S);
				assume IsAssignment(slipOf(S, l));
				assert Substatement(res, S);
				assume !IsSkip(slipOf(res, l));
				//assume ValidLabel(vLabel, SV');
				//assume MatchingSlipsFromSSA(SV', vLabel, res, l);
				assume MatchingSlips(S, res, l);
			}
			assert v in def(slipOf(res, l)) by {
				assert Substatement(res, S);
			}
		}
	case Exit => assert slide in slidesOf(res, def(S)); // מיותר?
	case Entry => assert slide in slidesOf(res, def(S)); // מיותר?
	}		
}

predicate ValidXLs(globS: set<Variable>, XLs: seq<set<Variable>>, X: seq<Variable>)
{
	|X| == |XLs| &&
	(forall i,j :: 0 <= i < j < |XLs| ==> XLs[i] !! XLs[j]) && // or: XLs[i] * XLs[j] == {}
	(forall s :: s in XLs ==> s !! globS) // or: s * globS == {}
}

lemma IdenticalLabels(S: Statement, S': Statement, SV': Statement, res: Statement, l: Label, varLabel: Label, l': Label, XLs: seq<set<Variable>>, X: seq<Variable>, selfEmptyLabelsSV': set<Label>, globS: set<Variable>)
	requires NoSelfAssignments(S) && NoEmptyAssignments(S)
	requires ValidXLs(globS, XLs, X)
	requires Valid(S) && Core(S)
	requires Valid(S') && Core(S')
	requires Valid(SV') && Core(SV')
	requires Valid(res) && Core(res)
	requires ValidLabel(l, S)
	requires varLabel == VarLabelOf(S, S', l)
	requires ValidLabel(varLabel, SV')
	requires l' == LabelOf(selfEmptyLabelsSV', varLabel)
	requires ValidLabel(l', res) // ?
	requires l' == LabelOf(selfEmptyLabelsSV', VarLabelOf(S, S', l))
	//requires S == RemoveEmptyAssignments(Rename(S', XLs, X)) // ?
	requires Substatement(SV', S')
	requires res == RemoveEmptyAssignments(Rename(SV', XLs, X))

	ensures LabelOf(selfEmptyLabelsSV', VarLabelOf(S, S', l)) == l
{
	/*assert allLabelsOf(SV') == allLabelsOf(Rename(SV', XLs, X)) by {
		forall l1 | l1 in allLabelsOf(SV') ensures l1 in allLabelsOf(Rename(SV', XLs, X)) {
			L70(l1, SV', XLs, X);
		}
		forall l1 | l1 in allLabelsOf(Rename(SV', XLs, X)) ensures l1 in allLabelsOf(SV') {
			L71(l1, SV', XLs, X);
		}
	}*/
	assert LabelOf(selfEmptyLabelsSV', VarLabelOf(S, S', l)) == l by 
	{
		if (l == [])
		{
			assert varLabel == [];
			assert l' == [];		
			assert LabelOf(selfEmptyLabelsSV', VarLabelOf(S, S', l)) == l;
		}
		else
		{
		
			match S {
			case Skip =>				assert varLabel == [];
										assert l' == [];
			case Assignment(LHS,RHS) =>	assert varLabel == [];
										assert l' == [];
			case SeqComp(S1,S2) =>		assert l[0] == varLabel[0];
										assert varLabel[0] == l'[0] by { // כלומר למה זה לא נמחק

										/*
										l:			2,2,2,1,1
										varLabel:	2,2,2,2,1,1,1    , {3,5}
										l':			2,2,2,1,1
										*/

											var newLabel := if varLabel[0] == 1 then [2] else [1];
											assert newLabel !in selfEmptyLabelsSV';
										}

										if (l[0] == 1) {
											IdenticalLabels(S1, S', SV', res, l[1..], varLabel[1..], l'[1..], XLs, X, selfEmptyLabelsSV', globS); }
										else {
											IdenticalLabels(S2, S', SV', res, l[1..], varLabel[1..], l'[1..], XLs, X, selfEmptyLabelsSV', globS); }
			case IF(B0,Sthen,Selse) =>	/*assert l[0] == varLabel[0];
										assert varLabel[0] == l'[0];
										IdenticalLabels(S, S', SV', res, l[1..], varLabel[2..], l'[1..], XLs, X, selfEmptyLabelsSV');*/
			case DO(B,Sloop) =>			/*assert varLabel[0] == 2;
										IdenticalLabels(S, S', SV', res, l[1..], varLabel[3..], l'[1..], XLs, X, selfEmptyLabelsSV');*/
			}
		}
	}
}

lemma L70(l1: Label, SV': Statement, XLs: seq<set<Variable>>, X: seq<Variable>)
	requires Valid(SV') && Core(SV')
	requires l1 in allLabelsOf(SV')
	ensures l1 in allLabelsOf(Rename(SV', XLs, X))

lemma L71(l1: Label, SV': Statement, XLs: seq<set<Variable>>, X: seq<Variable>)
	requires Valid(SV') && Core(SV')
	requires l1 in allLabelsOf(Rename(SV', XLs, X))
	ensures l1 in allLabelsOf(SV')

lemma L62(S: Statement, SV': Statement, res: Statement)
/*	ensures forall l,l',v,v' :: ValidLabel(l, S) && IsAssignment(slipOf(S, l)) && CorrespondingLabels(l, l', S) && 
								ValidLabel(l', SV') && IsAssignment(slipOf(SV', l')) && v == Rename(v') ==>
								ValidLabel(l, res) && IsAssignment(slipOf(res, l)) && 
								(v in def(slipOf(res, l)) <==> v' in def(slipOf(SV', l')))*/

lemma L61(slide: Slide, vSlide: VarSlide, S: Statement, S': Statement, SV': Statement, res: Statement, slidesSV: set<Slide>, varSlidesSV: set<VarSlide>, V: set<Variable>, V': set<Variable>, varSlideDGS': VarSlideDG)
	requires Valid(S) && Core(S)
	requires Valid(S') && Core(S')
	requires Valid(SV') && Core(SV')
	requires Valid(res) && Core(res)
	requires slide in slidesOf(S, def(S))
	requires vSlide == VarSlideOf(S, S', slide) && vSlide !in varSlidesSV
	requires Substatement(res, S)
	requires forall Sm :: Sm in slidesSV <==> (Sm in slidesOf(S,def(S)) && exists Sn :: Sn in finalDefSlides(S, SlideDGOf(S, CFGOf(S)), CFGOf(S), V) && SlideDGReachable(SlideDGOf(S, CFGOf(S)), Sm, Sn, SlideDGOf(S, CFGOf(S)).1));
	requires forall vSlide :: vSlide in varSlidesSV ==> (vSlide in varSlidesOf(S,def(S)) && exists Sn: VarSlide :: Sn.0 in V' && VarSlideDGReachable(varSlideDGS', vSlide, Sn, varSlideDGS'.1))
	requires slide in slidesSV <==> VarSlideOf(S, S', slide) in varSlidesSV
	ensures slide !in slidesOf(res, def(S))
{
	assert slide !in slidesOf(res, def(S)) by {
		var u:= slide.1;
		match slide.0 {
		case Node(l) => // להראות בתזה דוגמא של 3 האופציות
			assert !ValidLabel(l, res) || IsSkip(slipOf(res, l)) || (IsAssignment(slipOf(res, l)) && u !in def(slipOf(res, l))) by {
				assert vSlide == VarSlideOf(S, S', slide);
				assert vSlide !in varSlidesSV;
				var u' := vSlide.0;
				var varLabel := vSlide.2;
				/////////////////// לבדוק את השורות הבאות
				//assert ValidLabel(l, S);
				assert ValidLabel(varLabel, S') && IsAssignment(slipOf(S', varLabel)) && u' in def(slipOf(S', varLabel));
				assert !ValidLabel(varLabel, SV') || IsSkip(slipOf(SV', varLabel)) || (IsAssignment(slipOf(SV', varLabel)) && u' !in def(slipOf(SV', varLabel)));
			}
		}
	}	
}

lemma LemmaSlidesSVToVarSlidesSV(slide: Slide, S: Statement, S': Statement, SV': Statement, slidesSV: set<Slide>, varSlidesSV: set<VarSlide>, X: seq<Variable>, V: set<Variable>, V': set<Variable>, varSlideDGS': VarSlideDG, vsSSA: VariablesSSA)
	requires Valid(S) && Core(S)
	requires Valid(S') && Core(S')
	requires Valid(SV') && Core(SV')
	requires ValidVsSSA(vsSSA)
	requires slide in slidesOf(S, def(S))
	requires forall Sm :: Sm in slidesSV <==> (Sm in slidesOf(S,def(S)) && exists Sn :: Sn in finalDefSlides(S, SlideDGOf(S, CFGOf(S)), CFGOf(S), V) && SlideDGReachable(SlideDGOf(S, CFGOf(S)), Sm, Sn, SlideDGOf(S, CFGOf(S)).1));
	requires forall vSlide :: vSlide in varSlidesSV ==> (vSlide in varSlidesOf(S,def(S)) && exists Sn: VarSlide :: Sn.0 in V' && VarSlideDGReachable(varSlideDGS', vSlide, Sn, varSlideDGS'.1))
	ensures slide in slidesSV <==> VarSlideOf(S, S', slide) in varSlidesSV
{
	assert slide in slidesSV <==> VarSlideOf(S, S', slide) in varSlidesSV by {
		if (slide in slidesSV)
		{
			// p ==> q:	
			L1(slide, setOf(X), S, S', SV', slidesSV, varSlidesSV, vsSSA, V, V', varSlideDGS');
			assert VarSlideOf(S, S', slide) in varSlidesSV;
		}
		else
		{
			assert forall vSlide :: vSlide in varSlidesSV ==> (vSlide in varSlidesOf(S,def(S)) && exists Sn: VarSlide :: Sn.0 in V' && VarSlideDGReachable(varSlideDGS', vSlide, Sn, varSlideDGS'.1));
			// ^p ==> ^q:
			L2(slide, S, S', SV', slidesSV, varSlidesSV, V, V', varSlideDGS', vsSSA);
			assert VarSlideOf(S, S', slide) !in varSlidesSV;
			//assert forall slide :: slide in SlideDGOf(S, CFGOf(S)).1 - slidesSV ==> VarSlideOf(S, S', slide) !in varSlidesSV;
		}
	}
}

lemma {:verify false}L1(slide: Slide, X: set<Variable>, S: Statement, S': Statement, SV': Statement, slidesSV: set<Slide>, varSlidesSV: set<VarSlide>, vsSSA: VariablesSSA, V: set<Variable>, V': set<Variable>, varSlideDG: VarSlideDG)
	requires Valid(S) && Core(S)
	requires Valid(S') && Core(S')
	requires Valid(SV') && Core(SV')
	requires ValidVsSSA(vsSSA)
	requires slide in slidesSV
	ensures VarSlideOf(S, S', slide) in varSlidesSV
{
	assert slide in slidesSV;
	var varSlide := VarSlideOf(S, S', slide);
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
				
			var finalDefVarSlide := VarSlideOf(S, S', finalDefSlide);
			assert varSlide == VarSlideOf(S, S', slide);
			assert VarSlideDGReachable(varSlideDG, varSlide, finalDefVarSlide, varSlideDG.1) by {
				PathCorrespondence(slideDG, varSlideDG, slide, finalDefSlide, S, S');
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
					//var finalDefVarSlides := set slide, varSlide | slide in finalDefSlides(S, slideDG, cfg, V) && varSlide == VarSlideOf(S, S', slide) :: varSlide;
					var finalDefVarSlides := set slide, varSlide | slide in finalDefSlides(S, slideDG, cfg, V) && varSlide in varSlidesOf(S,def(S)) && varSlide == VarSlideOf(S, S', slide) :: varSlide;
					//////////////L4(X, vsSSA, v', V', instancesOfFinalDefSlide, finalDefSlide, S, slideDG, cfg, V, slide, slidesSV, slideOfV', finalDefVarSlides, varSlideDG, SV');
				}
			}
		}
	}
}

// Working
lemma {:verify false}L2(slide: Slide, S: Statement, S': Statement, SV': Statement, slidesSV: set<Slide>, varSlidesSV: set<VarSlide>, V: set<Variable>, V': set<Variable>, varSlideDG: VarSlideDG, vsSSA: VariablesSSA)
	requires Valid(S) && Core(S)
	requires Valid(S') && Core(S')
	requires Valid(SV') && Core(SV')
	requires var slideDG := SlideDGOf(S, CFGOf(S)); forall Sm :: Sm in slidesSV <==> (Sm in slidesOf(S,def(S)) && exists Sn :: Sn in finalDefSlides(S, slideDG, CFGOf(S), V) && SlideDGReachable(slideDG, Sm, Sn, slideDG.1));
	requires forall vSlide :: vSlide in varSlidesSV ==> (vSlide in varSlidesOf(S,def(S)) && exists Sn: VarSlide :: Sn.0 in V' && VarSlideDGReachable(varSlideDG, vSlide, Sn, varSlideDG.1));
	requires slide !in slidesSV
	ensures VarSlideOf(S, S', slide) !in varSlidesSV;
{
	var cfg := ComputeCFG(S);
	var slideDG := SlideDGOf(S, cfg); 
	assume slideDG == SlideDGOf(S, cfg); 
	assume cfg == CFGOf(S);

	var varSlide := VarSlideOf(S, S', slide);
	assert varSlide == VarSlideOf(S, S', slide);
		
	assert !(slide in slidesOf(S,def(S)) && exists Sn :: Sn in finalDefSlides(S, slideDG, cfg, V) && SlideDGReachable(slideDG, slide, Sn, slideDG.1)) by {
		assert forall Sm :: Sm in slidesSV <==> (Sm in slidesOf(S,def(S)) && exists Sn :: Sn in finalDefSlides(S, slideDG, cfg, V) && SlideDGReachable(slideDG, Sm, Sn, slideDG.1));
		assert slide !in slidesSV;
	} 
		 
	assert varSlide !in varSlidesSV by {
		calc {
			varSlide in varSlidesSV;
		==> { assert forall vSlide :: vSlide in varSlidesSV ==> (vSlide in varSlidesOf(S,def(S)) && exists Sn: VarSlide :: Sn.0 in V' && VarSlideDGReachable(varSlideDG, vSlide, Sn, varSlideDG.1)); }
			varSlide in varSlidesOf(S,def(S)) && exists Sn: VarSlide :: Sn.0 in V' && VarSlideDGReachable(varSlideDG, varSlide/*i1*/, Sn/*sum4*/, varSlideDG.1);
		==> { assert varSlide == VarSlideOf(S, S', slide);
			  L5(slide, varSlide, S, S', SV', V, V', slideDG, cfg, varSlideDG, vsSSA); }
			slide in slidesOf(S,def(S)) && exists Sn :: Sn in finalDefSlides(S, slideDG, cfg, V) && SlideDGReachable(slideDG, slide, Sn, slideDG.1);
		==> { assert !(slide in slidesOf(S,def(S)) && exists Sn :: Sn in finalDefSlides(S, slideDG, cfg, V) && SlideDGReachable(slideDG, slide, Sn, slideDG.1)); }	
			false;
		}
	}	
}

lemma {:verify false}L5(slide: Slide, varSlide: VarSlide, S: Statement, S': Statement, SV': Statement, V: set<Variable>, V': set<Variable>, slideDG: SlideDG, cfg: CFG, varSlideDG: VarSlideDG, vsSSA: VariablesSSA)
	requires Valid(S) && Core(S)
	requires Valid(S') && Core(S')
	requires Valid(SV') && Core(SV')
	requires varSlide.1 == Regular
	requires varSlide == VarSlideOf(S, S', slide) 
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


lemma EdgeToVarPhiPath(slide1: Slide, slide2: Slide, slideDG: SlideDG, varSlideDG: VarSlideDG, S: Statement, S': Statement)
	requires Valid(S) && Core(S)
	requires Valid(S') && Core(S')
	requires slide2 in slideDG.2
	requires slide1 in slideDG.2[slide2]
	//requires connection between SV and SV'
	ensures VarSlideDGReachablePhi(varSlideDG, VarSlideOf(S, S', slide1), VarSlideOf(S, S', slide2), varSlideDG.1)
// לכתוב למה עבור קשת מסלייד1 לסלייד2, קיים מסלול מוארסלייד1 לוארסלייד2 שעובר דרך 0 או יותר קודקודי פי
// והפוך, ממסלול לקשת

lemma VarPhiPathToEdge(slide1: Slide, slide2: Slide, slideDG: SlideDG, varSlideDG: VarSlideDG, S: Statement, S': Statement)
	requires Valid(S) && Core(S)
	requires Valid(S') && Core(S')
	requires VarSlideDGReachablePhi(varSlideDG, VarSlideOf(S, S', slide1), VarSlideOf(S, S', slide2), varSlideDG.1)
	//requires connection between SV and SV'
	ensures slide2 in slideDG.2
	ensures slide1 in slideDG.2[slide2]

//  למה עבור מסלול מוארסלייד1 לוארסלייד2 שעובר דרך 0 או יותר קודקודי פי, קיימת קשת מסלייד1 לסלייד2

lemma PathBackCorrespondence(slideDG: SlideDG, varSlideDG: VarSlideDG, slide1: Slide, slide2: Slide, S: Statement, S': Statement)
	requires Valid(S) && Core(S)
	requires Valid(S') && Core(S')
	requires VarSlideOf(S, S', slide1).1 == Regular && VarSlideOf(S, S', slide2).1 == Regular
	requires VarSlideDGReachable(varSlideDG, VarSlideOf(S, S', slide1), VarSlideOf(S, S', slide2), varSlideDG.1)
	//requires connection between SV and SV'
	ensures SlideDGReachable(slideDG, slide1, slide2, slideDG.1)

*/
lemma {:verify false}PathCorrespondence(slideDG: SlideDG, varSlideDG: VarSlideDG, slide1: Slide, slide2: Slide, S: Statement, S': Statement)
	requires Valid(S) && Core(S)
	requires Valid(S') && Core(S')
	requires SlideDGReachable(slideDG, slide1, slide2, slideDG.1)
	//requires connection between S and S'
	ensures VarSlideDGReachable(varSlideDG, VarSlideOf(S, S', slide1), VarSlideOf(S, S', slide2), varSlideDG.1)
	
	

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
	ensures Valid(SV) && Core(SV)
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