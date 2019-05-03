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
	ensures forall Sm :: Sm in SliceOf(S,V).0 <==> (Sm in slidesOf(S,def(S)) && exists Sn :: Sn in finalDefSlides(S, SlideDGOf(S, CFGOf(S)), CFGOf(S), V) && SlideDGReachable(SlideDGOf(S, CFGOf(S)), Sm, Sn, SlideDGSlides(SlideDGOf(S, CFGOf(S)))))
	ensures Valid(SliceOf(S,V).1) && Core(SliceOf(S,V).1)
{
	var cfg := ComputeCFG(S);
	assert cfg == CFGOf(S);
	var slideDG := SlideDGOf(S, cfg);
	var slidesSV := set Sm | (Sm in slidesOf(S,def(S)) && exists Sn :: Sn in finalDefSlides(S, slideDG, cfg, V) && SlideDGReachable(slideDG, Sm, Sn, SlideDGSlides(slideDG)));

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
	requires IsVarSlideDGOf(varSlideDG, S)
	decreases *
	ensures Valid(res) && Core(res)
	//ensures var varSlidesRes: set<VarSlide> := varSlidesOf(res, V); forall Sm :: Sm in varSlidesRes <==> (VarSlideVariable(Sm) in V || (exists Sn: VarSlide :: VarSlideVariable(Sn) in V && VarSlideDGReachable(varSlideDG, Sm, Sn, VarSlideDGVarSlides(varSlideDG))))	 // Implement VarSlideDGReachable
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
	assert IsVarSlideDGOf(varSlideDGS', S');

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
	//assert forall Sm :: Sm in varSlidesSV <==> (exists Sn: VarSlide :: VarSlideVariable(Sn) in V' && VarSlideDGReachable(varSlideDGS', Sm, Sn, VarSlideDGVarSlides(varSlideDGS')));	 // Implement VarSlideDGReachable
	assert forall vSlide :: vSlide in varSlidesSV ==> (vSlide in varSlidesOf(S,def(S)) && exists Sn: VarSlide :: VarSlideVariable(Sn) in V' && VarSlideDGReachable(varSlideDGS', vSlide, Sn, VarSlideDGVarSlides(varSlideDGS')));
	
	assert Valid(S) && Core(S);
	ghost var allSlides := slidesOf(S,def(S));
	//ghost var SV := SliceOf(S,V);
	ghost var SliceOfSV := SliceOf(S,V);
	ghost var SV := SliceOfSV.1;
	assert Valid(SV) && Core(SV); 
	//ghost var slidesSV := slidesOf(SV,V);
	ghost var slidesSV := SliceOfSV.0;
	assert forall Sm :: Sm in slidesSV <==> (Sm in slidesOf(S,def(S)) && exists Sn :: Sn in finalDefSlides(S, SlideDGOf(S, CFGOf(S)), CFGOf(S), V) && SlideDGReachable(SlideDGOf(S, CFGOf(S)), Sm, Sn, SlideDGSlides(SlideDGOf(S, CFGOf(S)))));
	assume slidesSV <= allSlides;
	
	// From SSA
	var XL1i := liveOnEntryXSeq;
	var XL2f := liveOnExitXSeq;
	res := FromSSA(SV', X, XL1i, XL2f, Y, XLs, vsSSA, V, S', V', varSlideDGS');
	var XLsSeq := XLsToSeq(X, XLs, vsSSA);
	assert res == RemoveEmptyAssignments(Rename(SV', XLsSeq, X)); // FromSSA Post-condition

	//assert forall U: set<Variable> :: slidesOf(res, U) <= slidesOf(S, U) <= slidesOf(S, def(S));

	assert Substatement(res, S);
	assert Substatement(SV, S);
	
	assume def(res) <= def(S);// by { assert Core(S) && Substatement(res,S); }
	assert allSlidesOf(res) == slidesOf(res, def(S)) == SlideDGSlides(SlideDGOf(S, CFGOf(S)));
	assume def(SV) <= def(S);// by { assert Core(S) && Substatement(SliceOfSV,S); }
	assert allSlidesOf(SV) == slidesOf(SV, def(S));
	assert slidesOf(res, def(S)) <= slidesOf(S, def(S));
	assert slidesSV == slidesOf(SV, def(S)) == slidesSV <= slidesOf(S, def(S));

	// ensures SliceOfSV == res :
	assert slidesOf(res, def(S)) == slidesOf(SV, def(S)) by {
		forall slide | slide in slidesOf(S, def(S)) ensures slide in slidesOf(res, def(S)) <==> slide in slidesOf(SV, def(S)) {
			LemmaSlidesSVToVarSlidesSV(slide, S, S', SV', slidesSV, varSlidesSV, X, V, V', varSlideDGS', vsSSA, XLsSeq);
			//assert forall slide :: slide in SlideDGSlides(SlideDGOf(S, CFGOf(S))) ==> (slide in slidesSV <==> VarSlideOf(S, S', slide) in varSlidesSV);
			assert slide in slidesSV <==> VarSlideOf(S, S', slide) in varSlidesSV;

			LemmaVarSlidesSVToRes(slide, S, S', SV', res, slidesSV, varSlidesSV, X, V, V', varSlideDGS', vsSSA, XLsSeq, glob(S));
			//assert forall slide :: slide in /*SlideDGSlides(SlideDGOf(S, CFGOf(S)))*/ slidesOf(S, def(S)) ==> (VarSlideOf(S, S', slide) in varSlidesSV <==> slide in slidesOf(res, def(S)));
			assert VarSlideOf(S, S', slide) in varSlidesSV <==> slide in slidesOf(res, def(S));
		}
	}
	
	LemmaIdenticalSlices(S, SV, res);

	///////////////////////////////////////////

	assert slipOf(SV, []) == slipOf(res, []) by {
		assert SV == SV;
		LemmaIdenticalSlicesUsingSlips(S, S', SV', res, SV, V, V', XLsSeq, X, [], slidesSV, varSlidesSV, varSlideDGS');
	}

	LemmaIdenticalSlices2(SV, res);
}

lemma LemmaIdenticalSlices2(S1: Statement, S2: Statement)
	requires Valid(S1) && Valid(S2)
	requires Core(S1) && Core(S2)
	requires slipOf(S1, []) == slipOf(S2, [])
	ensures S1 == S2
{

}

lemma LemmaIdenticalSlicesUsingSlips(S: Statement, S': Statement, SV': Statement, res: Statement, SV: Statement, V: set<Variable>, V': set<Variable>, XLs: seq<set<Variable>>, X: seq<Variable>, l: Label, slidesSV: set<Slide>, varSlidesSV: set<VarSlide>, varSlideDGS': VarSlideDG) // should be called with l==[]
	requires Valid(S) && Valid(S') && Valid(SV') && Valid(res) && Valid(SV) 
	requires Core(S) && Core(S') && Core(SV') && Core(res) && Core(SV) 
	requires SliceOf(S,V).1 == SV
	requires RemoveEmptyAssignments(Rename(S', XLs, X)) == S
	requires Substatement(SV', S')
	requires RemoveEmptyAssignments(Rename(SV', XLs, X)) == res
	requires forall Sm :: Sm in slidesSV <==> (Sm in slidesOf(S,def(S)) && exists Sn :: Sn in finalDefSlides(S, SlideDGOf(S, CFGOf(S)), CFGOf(S), V) && SlideDGReachable(SlideDGOf(S, CFGOf(S)), Sm, Sn, SlideDGSlides(SlideDGOf(S, CFGOf(S)))))
	requires forall vSlide :: vSlide in varSlidesSV ==> (vSlide in varSlidesOf(S,def(S)) && exists Sn: VarSlide :: VarSlideVariable(Sn) in V' && VarSlideDGReachable(varSlideDGS', vSlide, Sn, VarSlideDGVarSlides(varSlideDGS')))
	requires forall slide :: slide in SlideDGSlides(SlideDGOf(S, CFGOf(S))) ==> (slide in slidesSV <==> VarSlideOf(S, S', slide) in varSlidesSV)
	requires ValidLabel(l, S) && ValidLabel(l, SV) && ValidLabel(l, res)
	ensures slipOf(SV, l) == slipOf(res, l)
	decreases maxLabelSize(S) - |l|
{
	assert slipOf(SV, l) == slipOf(res, l) by {
		assert MatchingSlips(S, res, l) by {
			var varLabel := VarLabelOf(S, S', l);
			assert ValidLabel(varLabel, SV');
			assert MatchingSlipsToSSA(S, l, S', varLabel) by { L96(S, l, S', varLabel, XLs, X); }
			assert MatchingSlips(S', SV', varLabel) by { L97(S', SV', varLabel); }
			assert MatchingSlipsFromSSA(SV', varLabel, res, l) by { L98(SV', varLabel, res, l, XLs, X); }
			LemmaMatchingSlips(S, S', SV', res, l, varLabel);
		}
		//assume MatchingSlips(S, SV, l);// by {}
		
		assert IsSkip(slipOf(SV, l)) <==> IsSkip(slipOf(res, l)) by {
			L90(S, V, SV, res, SV', V', XLs, X, l, slidesSV, varSlidesSV, varSlideDGS');
		}

		if (IsSkip(slipOf(SV, l)))
		{			
			assert IsSkip(slipOf(res, l));
			assert slipOf(SV, l) == slipOf(res, l);
		}
		else
		{			
			assert !IsSkip(slipOf(res, l));	

			match slipOf(SV, l) {
			case Assignment(LHS_SV,RHS_SV) =>
				assert Substatement(SV, S);
				assert IsAssignment(slipOf(S, l)) by { SubstatementOfSlips(SV, S, l); }
				assert IsAssignment(slipOf(res, l)) by { assert MatchingSlips(S, res, l) && !IsSkip(slipOf(res, l)); }
				assert GetLHS(slipOf(res, l)) == LHS_SV && GetRHS(slipOf(res, l)) == RHS_SV by {
					var varLabel := VarLabelOf(S, SV', l); /////////////// Maybe S' instead of SV'? 
					var preLabel := PrefixOfSlideLabel(slidesSV, l); // קבוצת הסליידים שלייבל זה הרישא שלהם
					var preVarLabel := PrefixOfVarSlideLabel(varSlidesSV, varLabel);  // קבוצת הואר-סליידים שואר-לייבל זה הרישא שלהם
					assert |preLabel| == |preVarLabel| == |LHS_SV| == |GetLHS(slipOf(res, l))|;
					assert forall v,s :: s in preLabel && v == SlideVariable(s) ==> exists v',s' :: s' in preVarLabel && v' == VarSlideVariable(s') && v == instanceToVariable(v', XLs, X);
					assert forall v1,s1,v2,s2 :: s1 in preLabel && v1 == SlideVariable(s1) && s2 in preLabel && v2 == SlideVariable(s2) && v1 == v2 ==> s1 == s2;
				}
				assert slipOf(SV, l) == slipOf(res, l);
			case SeqComp(S1_SV,S2_SV) =>
				assert IsSeqComp(slipOf(S, l)) by { SubstatementOfSlips(SV, S, l); }
				assert IsSeqComp(slipOf(res, l)) by { assert MatchingSlips(S, res, l) && !IsSkip(slipOf(res, l)); }
				assert ValidLabel(l+[1], S) by { LemmaValidLabelOfSlip(l, [1], S); }
				assert ValidLabel(l+[1], SV) by { LemmaValidLabelOfSlip(l, [1], SV); }
				assert ValidLabel(l+[1], res) by { LemmaValidLabelOfSlip(l, [1], res); }
				assert ValidLabel(l+[2], S) by { LemmaValidLabelOfSlip(l, [2], S); }
				assert ValidLabel(l+[2], SV) by { LemmaValidLabelOfSlip(l, [2], SV); }
				assert ValidLabel(l+[2], res) by { LemmaValidLabelOfSlip(l, [2], res); }
				LemmaIdenticalSlicesUsingSlips(S, S', SV', res, SV, V, V', XLs, X, l+[1], slidesSV, varSlidesSV, varSlideDGS');
				LemmaIdenticalSlicesUsingSlips(S, S', SV', res, SV, V, V', XLs, X, l+[2], slidesSV, varSlidesSV, varSlideDGS');
				assert slipOf(SV, l) == slipOf(res, l) by { L93(SV, res, l); }
			case IF(B0_SV,Sthen_SV,Selse_SV) =>
				assert IsIF(slipOf(S, l)) by { SubstatementOfSlips(SV, S, l); }
				assert IsIF(slipOf(res, l)) by { assert MatchingSlips(S, res, l) && !IsSkip(slipOf(res, l)); }
				assume SameBooleanExpressions(B0_SV, GetIfBool(slipOf(res, l))); //////////////////////////////////////// TODO
				assert ValidLabel(l+[1], S) by { LemmaValidLabelOfSlip(l, [1], S); }
				assert ValidLabel(l+[1], SV) by { LemmaValidLabelOfSlip(l, [1], SV); }
				assert ValidLabel(l+[1], res) by { LemmaValidLabelOfSlip(l, [1], res); }
				assert ValidLabel(l+[2], S) by { LemmaValidLabelOfSlip(l, [2], S); }
				assert ValidLabel(l+[2], SV) by { LemmaValidLabelOfSlip(l, [2], SV); }
				assert ValidLabel(l+[2], res) by { LemmaValidLabelOfSlip(l, [2], res); }
				LemmaIdenticalSlicesUsingSlips(S, S', SV', res, SV, V, V', XLs, X, l+[1], slidesSV, varSlidesSV, varSlideDGS');
				LemmaIdenticalSlicesUsingSlips(S, S', SV', res, SV, V, V', XLs, X, l+[2], slidesSV, varSlidesSV, varSlideDGS');
				assert slipOf(SV, l) == slipOf(res, l) by { L94(SV, res, l); }
			case DO(B_SV,S_SV) =>
				assert IsDO(slipOf(S, l)) by { SubstatementOfSlips(SV, S, l); }
				assert IsDO(slipOf(res, l)) by { assert MatchingSlips(S, res, l) && !IsSkip(slipOf(res, l)); }
				assume SameBooleanExpressions(B_SV, GetLoopBool(slipOf(res, l))); /////////////////////////////////////// TODO
				assert ValidLabel(l+[1], S) by { LemmaValidLabelOfSlip(l, [1], S); }
				assert ValidLabel(l+[1], SV) by { LemmaValidLabelOfSlip(l, [1], SV); }
				assert ValidLabel(l+[1], res) by { LemmaValidLabelOfSlip(l, [1], res); }
				LemmaIdenticalSlicesUsingSlips(S, S', SV', res, SV, V, V', XLs, X, l+[1], slidesSV, varSlidesSV, varSlideDGS');
				assert slipOf(SV, l) == slipOf(res, l) by { L95(SV, res, l); }
			}
		}
	}
}

lemma L90(S: Statement, V: set<Variable>, SV: Statement, res: Statement, SV': Statement, V': set<Variable>, XLs: seq<set<Variable>>, X: seq<Variable>, l: Label, slidesSV: set<Slide>, varSlidesSV: set<VarSlide>, varSlideDGS': VarSlideDG) // should be called with l==[]
	requires Valid(S) && Valid(SV) && Valid(SV') && Valid(res)
	requires Core(S) && Core(SV) && Core(SV') && Core(res)
	requires SliceOf(S,V).1 == SV
	requires RemoveEmptyAssignments(Rename(SV', XLs, X)) == res
	requires forall Sm :: Sm in slidesSV <==> (Sm in slidesOf(S,def(S)) && exists Sn :: Sn in finalDefSlides(S, SlideDGOf(S, CFGOf(S)), CFGOf(S), V) && SlideDGReachable(SlideDGOf(S, CFGOf(S)), Sm, Sn, SlideDGSlides(SlideDGOf(S, CFGOf(S)))))
	requires forall vSlide :: vSlide in varSlidesSV ==> (vSlide in varSlidesOf(S,def(S)) && exists Sn: VarSlide :: VarSlideVariable(Sn) in V' && VarSlideDGReachable(varSlideDGS', vSlide, Sn, VarSlideDGVarSlides(varSlideDGS')))
	requires forall slide :: slide in SlideDGSlides(SlideDGOf(S, CFGOf(S))) ==> (slide in slidesSV <==> VarSlideOf(S, S', slide) in varSlidesSV)
	requires ValidLabel(l, S) && ValidLabel(l, SV) && ValidLabel(l, res)
	requires MatchingSlips(S, res, l)
	ensures IsSkip(slipOf(SV, l)) <==> IsSkip(slipOf(res, l))
{
	assert IsSkip(slipOf(SV, l)) <==> IsSkip(slipOf(res, l)) by {
		if (IsSkip(slipOf(SV, l)))
		{
			L91(S, V, SV, res, SV', V', XLs, X, l, slidesSV, varSlidesSV, varSlideDGS');
		}
		else
		{
			L92(S, V, SV, res, SV', V', XLs, X, l, slidesSV, varSlidesSV, varSlideDGS');
		}
	}
}

lemma L91(S: Statement, V: set<Variable>, SV: Statement, res: Statement, SV': Statement, V': set<Variable>, XLs: seq<set<Variable>>, X: seq<Variable>, l: Label, slidesSV: set<Slide>, varSlidesSV: set<VarSlide>, varSlideDGS': VarSlideDG) // should be called with l==[]
	requires Valid(S) && Valid(SV) && Valid(SV') && Valid(res)
	requires Core(S) && Core(SV) && Core(SV') && Core(res)
	requires SliceOf(S,V).1 == SV
	requires RemoveEmptyAssignments(Rename(SV', XLs, X)) == res
	requires forall Sm :: Sm in slidesSV <==> (Sm in slidesOf(S,def(S)) && exists Sn :: Sn in finalDefSlides(S, SlideDGOf(S, CFGOf(S)), CFGOf(S), V) && SlideDGReachable(SlideDGOf(S, CFGOf(S)), Sm, Sn, SlideDGSlides(SlideDGOf(S, CFGOf(S)))))
	requires forall vSlide :: vSlide in varSlidesSV ==> (vSlide in varSlidesOf(S,def(S)) && exists Sn: VarSlide :: VarSlideVariable(Sn) in V' && VarSlideDGReachable(varSlideDGS', vSlide, Sn, VarSlideDGVarSlides(varSlideDGS')))
	requires forall slide :: slide in SlideDGSlides(SlideDGOf(S, CFGOf(S))) ==> (slide in slidesSV <==> VarSlideOf(S, S', slide) in varSlidesSV)
	requires ValidLabel(l, S) && ValidLabel(l, SV) && ValidLabel(l, res)
	requires MatchingSlips(S, res, l)
	requires IsSkip(slipOf(SV, l))
	ensures IsSkip(slipOf(res, l))
{
	if (IsSkip(slipOf(S, l)))
	{
		assert IsSkip(slipOf(res, l)) by { assert MatchingSlips(S, res, l); }
	}
	else // נגדם
	{
		assert IsSkip(slipOf(res, l)) by { }
	}
}

lemma L92(S: Statement, V: set<Variable>, SV: Statement, res: Statement, SV': Statement, V': set<Variable>, XLs: seq<set<Variable>>, X: seq<Variable>, l: Label, slidesSV: set<Slide>, varSlidesSV: set<VarSlide>, varSlideDGS': VarSlideDG) // should be called with l==[]
	requires Valid(S) && Valid(SV) && Valid(SV') && Valid(res)
	requires Core(S) && Core(SV) && Core(SV') && Core(res)
	requires SliceOf(S,V).1 == SV
	requires RemoveEmptyAssignments(Rename(SV', XLs, X)) == res
	requires forall Sm :: Sm in slidesSV <==> (Sm in slidesOf(S,def(S)) && exists Sn :: Sn in finalDefSlides(S, SlideDGOf(S, CFGOf(S)), CFGOf(S), V) && SlideDGReachable(SlideDGOf(S, CFGOf(S)), Sm, Sn, SlideDGSlides(SlideDGOf(S, CFGOf(S)))))
	requires forall vSlide :: vSlide in varSlidesSV ==> (vSlide in varSlidesOf(S,def(S)) && exists Sn: VarSlide :: VarSlideVariable(Sn) in V' && VarSlideDGReachable(varSlideDGS', vSlide, Sn, VarSlideDGVarSlides(varSlideDGS')))
	requires forall slide :: slide in SlideDGSlides(SlideDGOf(S, CFGOf(S))) ==> (slide in slidesSV <==> VarSlideOf(S, S', slide) in varSlidesSV)
	requires ValidLabel(l, S) && ValidLabel(l, SV) && ValidLabel(l, res)
	requires !IsSkip(slipOf(SV, l))
	ensures !IsSkip(slipOf(res, l))
{
	var varLabel := VarLabelOf(S, SV', l); /////////////// Maybe S' instead of SV'? 
	var preLabel := PrefixOfSlideLabel(slidesSV, l); // l is prefix of all slides in x
	var preVarLabel := PrefixOfVarSlideLabel(varSlidesSV, varLabel); // varLabel is prefix of all slides in y
	
	/*var preLabel :=	קבוצת הסליידים שלייבל זה הרישא שלהם מתוך slidesSV
		הקבוצה לא ריקה לכן !IsSkip(slipOf(SV,l))
		preLabel == {} <==> IsSkip(slipOf(SV,l))
	var preVarLabel :=	קבוצת הסליידים שואר-לייבל זה הרישא שלהם מתוך varSlidesSV שהם רגולר
		הקבוצה לא ריקה לכן !IsSkip(slipOf(SV', varLabel))
		preVarLabel == {} <==> IsSkip(slipOf(SV', varLabel))*/

	assert !IsSkip(slipOf(res, l)) by {
		calc {
			preLabel != {}; // כי במינימום יש בקבוצה את הסלייד שמייצג את הלייבל l
		==> { assert |preLabel| == |preVarLabel|; }
			preVarLabel != {};
		==> { assert forall vSlide :: vSlide in preVarLabel ==> varLabel <= VarSlideLabel(vSlide); }
			exists vLabel :: ValidLabel(vLabel, SV') && varLabel <= vLabel && IsAssignment(slipOf(SV', vLabel));
		==>
			!IsSkip(slipOf(SV', varLabel));
		==> { L83(slipOf(SV', varLabel), XLs, X); }
			!IsSkip(Rename(slipOf(SV', varLabel), XLs, X));
		==> { L84(Rename(slipOf(SV', varLabel), XLs, X)); }
			!IsSkip(RemoveEmptyAssignments(Rename(slipOf(SV', varLabel), XLs, X)));
		== { L81(SV', XLs, X, varLabel, l); } 
			!IsSkip(slipOf(RemoveEmptyAssignments(Rename(SV', XLs, X)), l));
		==> { assert RemoveEmptyAssignments(Rename(SV', XLs, X)) == res; }
			!IsSkip(slipOf(res, l));
		}
	}
}

lemma L93(SV: Statement, res: Statement, l: Label)
	requires Valid(SV) && Valid(res)
	requires Core(SV) && Core(res)
	requires ValidLabel(l, SV) && ValidLabel(l, res)
	requires IsSeqComp(slipOf(SV, l))
	requires IsSeqComp(slipOf(res, l))
	requires ValidLabel(l+[1], SV) &&  ValidLabel(l+[1], res)
	requires ValidLabel(l+[2], SV) &&  ValidLabel(l+[2], res)
	requires slipOf(SV, l+[1]) == slipOf(res, l+[1])
	requires slipOf(SV, l+[2]) == slipOf(res, l+[2])
	ensures slipOf(SV, l) == slipOf(res, l) 

lemma L94(SV: Statement, res: Statement, l: Label)
	requires Valid(SV) && Valid(res)
	requires Core(SV) && Core(res)
	requires ValidLabel(l, SV) && ValidLabel(l, res)
	requires IsIF(slipOf(SV, l))
	requires IsIF(slipOf(res, l))
	requires ValidLabel(l+[1], SV) &&  ValidLabel(l+[1], res)
	requires ValidLabel(l+[2], SV) &&  ValidLabel(l+[2], res)
	requires slipOf(SV, l+[1]) == slipOf(res, l+[1])
	requires slipOf(SV, l+[2]) == slipOf(res, l+[2])
	requires SameBooleanExpressions(GetIfBool(slipOf(SV, l)), GetIfBool(slipOf(res, l)))
	ensures slipOf(SV, l) == slipOf(res, l) 

lemma L95(SV: Statement, res: Statement, l: Label)
	requires Valid(SV) && Valid(res)
	requires Core(SV) && Core(res)
	requires ValidLabel(l, SV) && ValidLabel(l, res)
	requires IsDO(slipOf(SV, l))
	requires IsDO(slipOf(res, l))
	requires ValidLabel(l+[1], SV) &&  ValidLabel(l+[1], res)
	requires slipOf(SV, l+[1]) == slipOf(res, l+[1])
	requires SameBooleanExpressions(GetLoopBool(slipOf(SV, l)), GetLoopBool(slipOf(res, l)))
	ensures slipOf(SV, l) == slipOf(res, l) 

lemma {:verify false}LemmaMatchingSlips(S: Statement, S': Statement, SV': Statement, res: Statement, l: Label, varLabel: Label) // varLabel := VarLabelOf(S, S', l)
	requires Valid(S) &&  Valid(S') && Valid(SV') && Valid(res)
	requires Core(S) &&  Core(S') && Core(SV') && Core(res)
	requires ValidLabel(l, S) && ValidLabel(varLabel, S') && ValidLabel(varLabel, SV') && ValidLabel(l, res)
	requires MatchingSlipsToSSA(S, l, S', varLabel)
	requires MatchingSlips(S', SV', varLabel)
	requires MatchingSlipsFromSSA(SV', varLabel, res, l)
	ensures MatchingSlips(S, res, l)
{
	var slipOfS := slipOf(S, l);
	var slipOfS' := slipOf(S', varLabel);
	var slipOfSV' := slipOf(SV', varLabel);
	var slipOfRes := slipOf(res, l);
	
	match slipOfS {
	case Skip =>
		assert IsSkip(slipOfRes);
	case Assignment(LHS,RHS) =>
		assert IsSkip(slipOfRes) || IsAssignment(slipOfRes) by {}
	case SeqComp(S1,S2) =>
		assert IsSkip(slipOfRes) || IsSeqComp(slipOfRes) by {
			assert IsSeqComp(slipOfS') by { assert MatchingSlipsToSSA(S, l, S', varLabel); }
			assert IsSeqComp(slipOfSV') || IsSkip(slipOfSV') by { assert MatchingSlips(S', SV', varLabel); }
			assert !IsDO(slipOfRes) by {
				calc {
					IsDO(slipOfRes);
				==> { assert MatchingSlipsFromSSA(SV', varLabel, res, l); }
					IsSeqComp(slipOfSV') && IsAssignment(GetS1(slipOfSV')) && IsDO(GetS2(slipOfSV')) && IsSeqComp(GetLoopBody(GetS2(slipOfSV')));
				==> { assert MatchingSlips(S', SV', varLabel); }
					IsSeqComp(slipOfS') && IsAssignment(GetS1(slipOfS')) && IsDO(GetS2(slipOfS')) && IsSeqComp(GetLoopBody(GetS2(slipOfS')));
				==> { assert MatchingSlipsToSSA(S, l, S', varLabel); }
					IsDO(slipOfS);
				==>
					false;
				}
			}
		}
	case IF(B,Sthen,Selse) =>
		assert IsSkip(slipOfRes) || IsIF(slipOfRes) by {}
	case DO(B,Sloop) =>
		assert IsSkip(slipOfRes) || IsDO(slipOfRes) by {
			assert IsSeqComp(slipOfS') by { assert MatchingSlipsToSSA(S, l, S', varLabel); }
			assert IsSeqComp(slipOfSV') || IsSkip(slipOfSV') by { assert MatchingSlips(S', SV', varLabel); }		
			assert !IsSeqComp(slipOfRes) by {
				calc {
					IsSeqComp(slipOfRes);
				==> { assert MatchingSlipsFromSSA(SV', varLabel, res, l); }
					IsSeqComp(slipOfSV') && !(IsAssignment(GetS1(slipOfSV')) && IsDO(GetS2(slipOfSV')) && IsSeqComp(GetLoopBody(GetS2(slipOfSV'))));
				==> { assert MatchingSlips(S', SV', varLabel); }
					IsSeqComp(slipOfS') && !(IsAssignment(GetS1(slipOfS')) && IsDO(GetS2(slipOfS')) && IsSeqComp(GetLoopBody(GetS2(slipOfS'))));
				==> { assert MatchingSlipsToSSA(S, l, S', varLabel); }
					IsSeqComp(slipOfS);
				==>
					false;
				}
			}
		}
	}	
}

lemma {:verify false}L96(S: Statement, l: Label, S': Statement, l': Label, XLs: seq<set<Variable>>, X: seq<Variable>)
	requires Valid(S) && Valid(S')
	requires Core(S) && Core(S')
	requires ValidLabel(l, S)
	requires ValidLabel(l', S')
	requires RemoveEmptyAssignments(Rename(S', XLs, X)) == S
	ensures MatchingSlipsToSSA(S, l, S', l')
{
	var slipOfS := slipOf(S, l);
	var slipOfS' := slipOf(S', l');
	
	match slipOfS {
	case Skip =>
		assert IsSkip(slipOfS') by {
			calc {
				!IsSkip(slipOfS');
			==>	{ L83(slipOfS', XLs, X); }
				!IsSkip(Rename(slipOfS', XLs, X));
			==>	{ L84(Rename(slipOfS', XLs, X)); }
				!IsSkip(RemoveEmptyAssignments(Rename(slipOfS', XLs, X)));
			==>	{ L81(S', XLs, X, l', l); }
				!IsSkip(slipOf(RemoveEmptyAssignments(Rename(S', XLs, X)), l));
			==>	assert RemoveEmptyAssignments(Rename(S', XLs, X)) == S;
				!IsSkip(slipOf(S, l));
			==>
				false;	
			}
		}
	case Assignment(LHS,RHS) =>	
		assert IsAssignment(slipOfS') by {}
	case SeqComp(S1,S2) =>		
		assert IsSeqComp(slipOfS') by {}
	case IF(B,Sthen,Selse) =>	
		assert IsIF(slipOfS') && IsSeqComp(GetIfThen(slipOfS')) && IsSeqComp(GetIfElse(slipOfS')) by {}
	case DO(B,Sloop) =>			
		assert IsSeqComp(slipOfS') && IsAssignment(GetS1(slipOfS')) && IsDO(GetS2(slipOfS')) && IsSeqComp(GetLoopBody(GetS2(slipOfS'))) by {}
	}	
}

lemma {:verify false}L97(S': Statement, SV': Statement, l': Label)
	requires Valid(S') && Valid(SV')
	requires Core(S') && Core(SV')
	requires ValidLabel(l', S')
	requires ValidLabel(l', SV')
	requires Substatement(SV', S')
	ensures MatchingSlips(S', SV', l')
{
	var slipOfS' := slipOf(S', l');
	var slipOfSV' := slipOf(SV', l');
	
	match slipOfS' {
	case Skip =>
		assert IsSkip(slipOfSV');
	case Assignment(LHS,RHS) =>
		assert IsSkip(slipOfSV') || IsAssignment(slipOfSV') by {}
	case SeqComp(S1,S2) =>
		assert IsSkip(slipOfSV') || IsSeqComp(slipOfSV') by {}
	case IF(B,Sthen,Selse) =>
		assert IsSkip(slipOfSV') || IsIF(slipOfSV') by {}
	case DO(B,Sloop) =>
		assert IsSkip(slipOfSV') || IsDO(slipOfSV') by {}
	}	
}

lemma L98(SV': Statement, l': Label, res: Statement, l: Label, XLs: seq<set<Variable>>, X: seq<Variable>)
	requires Valid(SV') && Valid(res)
	requires Core(SV') && Core(res)
	requires ValidLabel(l', SV')
	requires ValidLabel(l, res)
	requires RemoveEmptyAssignments(Rename(SV', XLs, X)) == res
	ensures MatchingSlipsFromSSA(SV', l', res, l)
{
	L96(res, l, SV', l', XLs, X);
}

function PrefixOfSlideLabel(slidesSV: set<Slide>, l: Label): set<Slide>
	//requires exists s :: s in slidesSV ==> match SlideCFGNode(s) { case Node(ls) => l == ls }
	//ensures PrefixOfSlideLabel(slidesSV, l) != {}
{
	if slidesSV == {} then {} else
	var s :| s in slidesSV;
	match SlideCFGNode(s) {
	case Node(ls) => if l <= ls then PrefixOfSlideLabel(slidesSV - {s}, l) + {s} else PrefixOfSlideLabel(slidesSV - {s}, l)
	}
}

function PrefixOfVarSlideLabel(varSlidesSV: set<VarSlide>, l: Label): set<VarSlide>
	ensures forall s :: s in PrefixOfVarSlideLabel(varSlidesSV, l) ==> l <= VarSlideLabel(s)
{
	if varSlidesSV == {} then {} else
	var s :| s in varSlidesSV;
	if l <= VarSlideLabel(s) then PrefixOfVarSlideLabel(varSlidesSV - {s}, l) + {s} else PrefixOfVarSlideLabel(varSlidesSV - {s}, l)
}

lemma SubstatementOfSlips(S1: Statement, S2: Statement, l: Label)
	requires Valid(S1) && Core(S1)
	requires Valid(S2) && Core(S2)
	requires ValidLabel(l, S1)
	requires ValidLabel(l, S2)
	requires Substatement(S1, S2)
	ensures Substatement(slipOf(S1, l), slipOf(S2, l))

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
	requires forall Sm :: Sm in slidesSV <==> (Sm in slidesOf(S,def(S)) && exists Sn :: Sn in finalDefSlides(S, SlideDGOf(S, CFGOf(S)), CFGOf(S), V) && SlideDGReachable(SlideDGOf(S, CFGOf(S)), Sm, Sn, SlideDGSlides(SlideDGOf(S, CFGOf(S)))));
	requires forall vSlide :: vSlide in varSlidesSV ==> (vSlide in varSlidesOf(S,def(S)) && exists Sn: VarSlide :: VarSlideVariable(Sn) in V' && VarSlideDGReachable(varSlideDGS', vSlide, Sn, VarSlideDGVarSlides(varSlideDGS')))
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
	requires forall Sm :: Sm in slidesSV <==> (Sm in slidesOf(S,def(S)) && exists Sn :: Sn in finalDefSlides(S, SlideDGOf(S, CFGOf(S)), CFGOf(S), V) && SlideDGReachable(SlideDGOf(S, CFGOf(S)), Sm, Sn, SlideDGSlides(SlideDGOf(S, CFGOf(S)))));
	requires forall vSlide :: vSlide in varSlidesSV ==> (vSlide in varSlidesOf(S,def(S)) && exists Sn: VarSlide :: VarSlideVariable(Sn) in V' && VarSlideDGReachable(varSlideDGS', vSlide, Sn, VarSlideDGVarSlides(varSlideDGS')))
	requires slide in slidesSV <==> VarSlideOf(S, S', slide) in varSlidesSV
	requires res == RemoveEmptyAssignments(Rename(SV', XLs, X)) // FromSSA Post-condition
	ensures slide in slidesOf(res, def(S))
{
	assert slide in slidesOf(S, def(S));
	assert slide in slidesSV by { assert slide in slidesSV <==> VarSlideOf(S, S', slide) in varSlidesSV; }
	assert forall vSlide :: vSlide in varSlidesSV ==> (vSlide in varSlidesOf(S,def(S)) && exists Sn: VarSlide :: VarSlideVariable(Sn) in V' && VarSlideDGReachable(varSlideDGS', vSlide, Sn, VarSlideDGVarSlides(varSlideDGS')));
	assert vSlide in varSlidesOf(S,def(S)) && exists Sn: VarSlide :: VarSlideVariable(Sn) in V' && VarSlideDGReachable(varSlideDGS', vSlide, Sn, VarSlideDGVarSlides(varSlideDGS'));
					
	var v := SlideVariable(slide);
	match SlideCFGNode(slide) {
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
	requires forall Sm :: Sm in slidesSV <==> (Sm in slidesOf(S,def(S)) && exists Sn :: Sn in finalDefSlides(S, SlideDGOf(S, CFGOf(S)), CFGOf(S), V) && SlideDGReachable(SlideDGOf(S, CFGOf(S)), Sm, Sn, SlideDGSlides(SlideDGOf(S, CFGOf(S)))));
	requires forall vSlide :: vSlide in varSlidesSV ==> (vSlide in varSlidesOf(S,def(S)) && exists Sn: VarSlide :: VarSlideVariable(Sn) in V' && VarSlideDGReachable(varSlideDGS', vSlide, Sn, VarSlideDGVarSlides(varSlideDGS')))
	requires slide in slidesSV <==> VarSlideOf(S, S', slide) in varSlidesSV
	ensures slide !in slidesOf(res, def(S))
{
	assert slide !in slidesOf(res, def(S)) by {
		var u := SlideVariable(slide);
		match SlideCFGNode(slide) {
		case Node(l) => // להראות בתזה דוגמא של 3 האופציות
			assert !ValidLabel(l, res) || IsSkip(slipOf(res, l)) || (IsAssignment(slipOf(res, l)) && u !in def(slipOf(res, l))) by {
				assert vSlide == VarSlideOf(S, S', slide);
				assert vSlide !in varSlidesSV;
				var u' := VarSlideVariable(vSlide);
				var varLabel := VarSlideLabel(vSlide);
				/////////////////// לבדוק את השורות הבאות
				//assert ValidLabel(l, S);
				assert ValidLabel(varLabel, S') && IsAssignment(slipOf(S', varLabel)) && u' in def(slipOf(S', varLabel));
				assert !ValidLabel(varLabel, SV') || IsSkip(slipOf(SV', varLabel)) || (IsAssignment(slipOf(SV', varLabel)) && u' !in def(slipOf(SV', varLabel)));
			}
		}
	}	
}

lemma LemmaSlidesSVToVarSlidesSV(slide: Slide, S: Statement, S': Statement, SV': Statement, slidesSV: set<Slide>, varSlidesSV: set<VarSlide>, X: seq<Variable>, V: set<Variable>, V': set<Variable>, varSlideDGS': VarSlideDG, vsSSA: VariablesSSA, XLs: seq<set<Variable>>)
	requires Valid(S) && Core(S)
	requires Valid(S') && Core(S')
	requires Valid(SV') && Core(SV')
	requires ValidVsSSA(vsSSA)
	requires RemoveEmptyAssignments(Rename(S', XLs, X)) == S
	requires slide in slidesOf(S, def(S))
	requires forall Sm :: Sm in slidesSV <==> (Sm in slidesOf(S,def(S)) && exists Sn :: Sn in finalDefSlides(S, SlideDGOf(S, CFGOf(S)), CFGOf(S), V) && SlideDGReachable(SlideDGOf(S, CFGOf(S)), Sm, Sn, SlideDGSlides(SlideDGOf(S, CFGOf(S)))));
	requires forall vSlide :: vSlide in varSlidesSV ==> (vSlide in varSlidesOf(S,def(S)) && exists Sn: VarSlide :: VarSlideVariable(Sn) in V' && VarSlideDGReachable(varSlideDGS', vSlide, Sn, VarSlideDGVarSlides(varSlideDGS')))
	ensures slide in slidesSV <==> VarSlideOf(S, S', slide) in varSlidesSV
{
	assert slide in slidesSV <==> VarSlideOf(S, S', slide) in varSlidesSV by {
		if (slide in slidesSV)
		{
			// p ==> q:	
			L1(slide, S, S', SV', slidesSV, varSlidesSV, vsSSA, V, V', varSlideDGS', XLs, X);
			assert VarSlideOf(S, S', slide) in varSlidesSV;
		}
		else
		{
			assert forall vSlide :: vSlide in varSlidesSV ==> (vSlide in varSlidesOf(S,def(S)) && exists Sn: VarSlide :: VarSlideVariable(Sn) in V' && VarSlideDGReachable(varSlideDGS', vSlide, Sn, VarSlideDGVarSlides(varSlideDGS')));
			// ^p ==> ^q:
			L2(slide, S, S', SV', slidesSV, varSlidesSV, V, V', varSlideDGS', vsSSA);
			assert VarSlideOf(S, S', slide) !in varSlidesSV;
			//assert forall slide :: slide in SlideDGSlides(SlideDGOf(S, CFGOf(S))) - slidesSV ==> VarSlideOf(S, S', slide) !in varSlidesSV;
		}
	}
}

lemma {:verify true}L1(slide: Slide, S: Statement, S': Statement, SV': Statement, slidesSV: set<Slide>, varSlidesSV: set<VarSlide>, vsSSA: VariablesSSA, V: set<Variable>, V': set<Variable>, varSlideDG: VarSlideDG, XLs: seq<set<Variable>>, X: seq<Variable>)
	requires Valid(S) && Core(S)
	requires Valid(S') && Core(S')
	requires Valid(SV') && Core(SV')
	requires ValidVsSSA(vsSSA)
	requires RemoveEmptyAssignments(Rename(S', XLs, X)) == S
	requires slide in slidesSV
	ensures VarSlideOf(S, S', slide) in varSlidesSV
{
	assert slide in slidesSV;
	var varSlide := VarSlideOf(S, S', slide);
	var cfg := ComputeCFG(S);
	var slideDG := SlideDGOf(S, cfg);

	assert varSlide in varSlidesSV by {
		assert exists Sn: VarSlide :: VarSlideVariable(Sn) in V' && VarSlideDGReachable(varSlideDG, varSlide/*i1*/, Sn/*sum4*/, VarSlideDGVarSlides(varSlideDG)) by {
			var finalDefSlide;
			if slide in finalDefSlides(S, slideDG, cfg, V)
			{
				finalDefSlide := slide;
				assert SlideDGReachable(slideDG, slide, finalDefSlide, SlideDGSlides(slideDG));
			}
			else
			{ // i1 --> sum5 --> sum4 , sum5 is pre of sum4 via phi only
				finalDefSlide :| finalDefSlide in finalDefSlides(S, slideDG, cfg, V) && SlideDGReachable(slideDG, slide, finalDefSlide, SlideDGSlides(slideDG));
			} 
				
			var finalDefVarSlide := VarSlideOf(S, S', finalDefSlide);
			assert varSlide == VarSlideOf(S, S', slide);
			assert VarSlideDGReachable(varSlideDG, varSlide, finalDefVarSlide, VarSlideDGVarSlides(varSlideDG)) by {
				PathCorrespondence(slideDG, varSlideDG, slide, finalDefSlide, S, S', XLs, X);
			}

			assert VarSlideDGReachable(varSlideDG, varSlide, finalDefVarSlide, VarSlideDGVarSlides(varSlideDG));

			assert vsSSA.existsInstance(SlideVariable(finalDefSlide));
			var instancesOfFinalDefSlideSeq := vsSSA.getInstancesOfVaribleFunc(SlideVariable(finalDefSlide));
			var instancesOfFinalDefSlide := setOf(instancesOfFinalDefSlideSeq);
			assert |instancesOfFinalDefSlide * V'| == 1;
			var v' :| v' in instancesOfFinalDefSlide * V';
			var slideOfV': VarSlide :| VarSlideVariable(slideOfV') == v';

			if VarSlideTag(slideOfV') == Regular
			{
				assert slideOfV' == finalDefVarSlide;
				assert VarSlideVariable(slideOfV') in V' && VarSlideDGReachable(varSlideDG, varSlide/*i1*/, slideOfV'/*sum5*/, VarSlideDGVarSlides(varSlideDG));
				// Done
			}
			else // Phi
			{
				assert slideOfV' != finalDefVarSlide; // צריך להוכיח מסלול ביניהם
				//assert VarSlideDGReachable(varSlideDG, finalDefVarSlide/*sum5*/, slideOfV'/*sum4*/, VarSlideDGVarSlides(varSlideDG));
				assert finalDefVarSlide in RegularPredecessorSlides(slideOfV', varSlideDG, varSlidesOf(SV', V')) by {
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
	requires var slideDG := SlideDGOf(S, CFGOf(S)); forall Sm :: Sm in slidesSV <==> (Sm in slidesOf(S,def(S)) && exists Sn :: Sn in finalDefSlides(S, slideDG, CFGOf(S), V) && SlideDGReachable(slideDG, Sm, Sn, SlideDGSlides(slideDG)));
	requires forall vSlide :: vSlide in varSlidesSV ==> (vSlide in varSlidesOf(S,def(S)) && exists Sn: VarSlide :: VarSlideVariable(Sn) in V' && VarSlideDGReachable(varSlideDG, vSlide, Sn, VarSlideDGVarSlides(varSlideDG)));
	requires slide !in slidesSV
	ensures VarSlideOf(S, S', slide) !in varSlidesSV;
{
	var cfg := ComputeCFG(S);
	var slideDG := SlideDGOf(S, cfg); 
	assume slideDG == SlideDGOf(S, cfg); 
	assume cfg == CFGOf(S);

	var varSlide := VarSlideOf(S, S', slide);
	assert varSlide == VarSlideOf(S, S', slide);
		
	assert !(slide in slidesOf(S,def(S)) && exists Sn :: Sn in finalDefSlides(S, slideDG, cfg, V) && SlideDGReachable(slideDG, slide, Sn, SlideDGSlides(slideDG))) by {
		assert forall Sm :: Sm in slidesSV <==> (Sm in slidesOf(S,def(S)) && exists Sn :: Sn in finalDefSlides(S, slideDG, cfg, V) && SlideDGReachable(slideDG, Sm, Sn, SlideDGSlides(slideDG)));
		assert slide !in slidesSV;
	} 
		 
	assert varSlide !in varSlidesSV by {
		calc {
			varSlide in varSlidesSV;
		==> { assert forall vSlide :: vSlide in varSlidesSV ==> (vSlide in varSlidesOf(S,def(S)) && exists Sn: VarSlide :: VarSlideVariable(Sn) in V' && VarSlideDGReachable(varSlideDG, vSlide, Sn, VarSlideDGVarSlides(varSlideDG))); }
			varSlide in varSlidesOf(S,def(S)) && exists Sn: VarSlide :: VarSlideVariable(Sn) in V' && VarSlideDGReachable(varSlideDG, varSlide/*i1*/, Sn/*sum4*/, VarSlideDGVarSlides(varSlideDG));
		==> { assert varSlide == VarSlideOf(S, S', slide);
			  L5(slide, varSlide, S, S', SV', V, V', slideDG, cfg, varSlideDG, vsSSA); }
			slide in slidesOf(S,def(S)) && exists Sn :: Sn in finalDefSlides(S, slideDG, cfg, V) && SlideDGReachable(slideDG, slide, Sn, SlideDGSlides(slideDG));
		==> { assert !(slide in slidesOf(S,def(S)) && exists Sn :: Sn in finalDefSlides(S, slideDG, cfg, V) && SlideDGReachable(slideDG, slide, Sn, SlideDGSlides(slideDG))); }	
			false;
		}
	}	
}

lemma {:verify false}L5(slide: Slide, varSlide: VarSlide, S: Statement, S': Statement, SV': Statement, V: set<Variable>, V': set<Variable>, slideDG: SlideDG, cfg: CFG, varSlideDG: VarSlideDG, vsSSA: VariablesSSA)
	requires Valid(S) && Core(S)
	requires Valid(S') && Core(S')
	requires Valid(SV') && Core(SV')
	requires VarSlideTag(varSlide) == Regular
	requires varSlide == VarSlideOf(S, S', slide) 
	requires varSlide in varSlidesOf(S,def(S)) && exists varSn: VarSlide :: VarSlideVariable(varSn) in V' && VarSlideDGReachable(varSlideDG, varSlide/*i1*/, varSn/*sum4*/, VarSlideDGVarSlides(varSlideDG))
	ensures slide in slidesOf(S,def(S)) && exists Sn :: Sn in finalDefSlides(S, slideDG, cfg, V) && SlideDGReachable(slideDG, slide, Sn, SlideDGSlides(slideDG))
/*{
	var varSn: VarSlide :| VarSlideVariable(varSn) in V' && VarSlideDGReachable(varSlideDG, varSlide, varSn, VarSlideDGVarSlides(varSlideDG));
	var Sn;

	if VarSlideTag(varSn) == Regular
	{
		Sn := SlideOf(SV, SV', varSn);
		PathBackCorrespondence(slideDG, varSlideDG, slide, Sn, SV, SV');
		assert SlideDGReachable(slideDG, slide, Sn, SlideDGSlides(slideDG)); // From PathBackCorrespondence
		assert Sn in finalDefSlides(S, slideDG, cfg, V) by {
			L6(varSn, V, V', S, SV, SV', slideDG, cfg);
		}
		assert Sn in finalDefSlides(S, slideDG, cfg, V) && SlideDGReachable(slideDG, slide, Sn, SlideDGSlides(slideDG)); // From the two above
	}
	else
	{
		var rpsVarSn := RegularPredecessorSlides(varSn, varSlideDG, varSlidesOf(SV', V'));
		var Sn' :| Sn' in rpsVarSn && VarSlideDGReachable(varSlideDG, varSlide, Sn', VarSlideDGVarSlides(varSlideDG)) && vsSSA.getVariableInRegularFormFunc(VarSlideVariable(Sn')) in V;
		Sn := SlideOf(SV, SV', Sn');
		PathBackCorrespondence(slideDG, varSlideDG, slide, Sn, SV, SV');
		assert SlideDGReachable(slideDG, slide, Sn, SlideDGSlides(slideDG)); // From PathBackCorrespondence
		assert Sn in finalDefSlides(S, slideDG, cfg, V) by {
			L7(varSn, V, V', S, SV, SV', slideDG, cfg, varSlideDG, varSlide, Sn', rpsVarSn, vsSSA);
		}
		assert Sn in finalDefSlides(S, slideDG, cfg, V) && SlideDGReachable(slideDG, slide, Sn, SlideDGSlides(slideDG)); // From the two above
	}
}*/
/*
lemma L6(varSn: VarSlide, V: set<Variable>, V': set<Variable>, S: Statement, SV: Statement, SV': Statement, slideDG: SlideDG, cfg: CFG)
	requires Valid(S) && Core(S)
	requires Valid(SV) && Core(SV)
	requires Valid(SV') && Core(SV')
	requires VarSlideTag(varSn) == Regular
	requires VarSlideVariable(varSn) in V'
	ensures SlideOf(SV, SV', varSn) in finalDefSlides(S, slideDG, cfg, V)

lemma L7(varSn: VarSlide, V: set<Variable>, V': set<Variable>, S: Statement, SV: Statement, SV': Statement, slideDG: SlideDG, cfg: CFG,
		 varSlideDG: VarSlideDG, varSlide: VarSlide, Sn': VarSlide, rpsVarSn: set<VarSlide>, vsSSA: VariablesSSA)
	requires VarSlideTag(varSn) == Phi
	requires VarSlideVariable(varSn) in V'
	requires Sn' in rpsVarSn && VarSlideDGReachable(varSlideDG, varSlide, Sn', VarSlideDGVarSlides(varSlideDG)) && vsSSA.getVariableInRegularFormFunc(VarSlideVariable(Sn')) in V
	ensures SlideOf(SV, SV', Sn') in finalDefSlides(S, slideDG, cfg, V)

*/
lemma EdgeToVarPhiPath(slide1: Slide, slide2: Slide, slideDG: SlideDG, varSlideDG: VarSlideDG, S: Statement, S': Statement, XLs: seq<set<Variable>>, X: seq<Variable>)
	requires Valid(S) && Core(S)
	requires Valid(S') && Core(S')
	requires IsSlideDGOf(slideDG, S)
	requires IsVarSlideDGOf(varSlideDG, S)
	requires ExistsEdge(slide1, slide2, slideDG)
	// ==>
	requires SlideDGReachable(slideDG, slide1, slide2, SlideDGSlides(slideDG))
	requires RemoveEmptyAssignments(Rename(S', XLs, X)) == S
	ensures VarSlideDGReachablePhi(varSlideDG, VarSlideOf(S, S', slide1), VarSlideOf(S, S', slide2), VarSlideDGVarSlides(varSlideDG))
// לכתוב למה עבור קשת מסלייד1 לסלייד2, קיים מסלול מוארסלייד1 לוארסלייד2 שעובר דרך 0 או יותר קודקודי פי
// והפוך, ממסלול לקשת
{
	var via :| SlideDGReachableVia(slideDG, slide1, via, slide2, SlideDGSlides(slideDG));
	assert IsExtendSlideDGPath(via) by {
		assert slide1 != slide2; // add to preconditions?		
	}
	assert IsEmptySlideDGPath(GetPrefixSlideDGPath(via)) by {
		assert slide1 in SlideDGMap(slideDG)[slide2];
	}
	assert GetNSlideDGPath(via) == slide1;
	
	EdgeToVarPhiPathVia(slideDG, varSlideDG, slide1, slide2, S, S', XLs, X, via);
}

lemma EdgeToVarPhiPathVia(slideDG: SlideDG, varSlideDG: VarSlideDG, slide1: Slide, slide2: Slide, S: Statement, S': Statement, XLs: seq<set<Variable>>, X: seq<Variable>, via: SlideDGPath)
	requires Valid(S) && Core(S)
	requires Valid(S') && Core(S')
	requires IsSlideDGOf(slideDG, S)
	requires IsVarSlideDGOf(varSlideDG, S)
	requires slide2 in SlideDGMap(slideDG)
	requires slide1 in SlideDGMap(slideDG)[slide2]
	// ==>
	requires SlideDGReachable(slideDG, slide1, slide2, SlideDGSlides(slideDG))
	requires RemoveEmptyAssignments(Rename(S', XLs, X)) == S
	ensures VarSlideDGReachablePhi(varSlideDG, VarSlideOf(S, S', slide1), VarSlideOf(S, S', slide2), VarSlideDGVarSlides(varSlideDG))
	decreases via
{
	var varslide1 := VarSlideOf(S, S', slide1);
	var varslide2 := VarSlideOf(S, S', slide2);

	match via {
	case Empty => ///////////////
		assert varslide1 == varslide2 by { assert slide1 == slide2; }////////////////////
	case Extend(prefix, n) =>
	//		 (prefix) 
	// slide1 ------> n -> slide2
		assert n in SlideDGSlides(slideDG) && slide2 in SlideDGNeighbours(slideDG, n) && SlideDGReachableVia(slideDG, slide1, prefix, n, SlideDGSlides(slideDG));
		
		if (varslide2 in VarSlideDGNeighbours(varSlideDG, varslide1)) {
			assert VarSlideDGReachablePhi(varSlideDG, varslide1, varslide2, VarSlideDGVarSlides(varSlideDG));
		}
		dfsdf
		else {
			// נניח בשלילה שלפחות אחד מהקודקודים על המסלול אינו פי כלומר רגולר.
			// נסיק שאם אחד מהקודקודים על המסלול הוא רגולר אז הקשת המקורית בין הסליידים לא קיימת כי אין סלייד-דיפנדנס.
			// (כי יש עוד דף למשתנה על המסלול בסיאףג'י)
			var n' := VarSlideOf(S, S', n);
			assert VarSlideDGReachablePhi(varSlideDG, varslide1, varslide2, VarSlideDGVarSlides(varSlideDG)) by {
				calc {
					!VarSlideDGReachablePhi(varSlideDG, varslide1, varslide2, VarSlideDGVarSlides(varSlideDG));
				==>
					!(exists via: VarSlideDGPath :: VarSlideDGReachableVia(varSlideDG, varslide1, via, varslide2, VarSlideDGVarSlides(varSlideDG)))


				==>
					!(n' in VarSlideDGVarSlides(varSlideDG) && varslide2 in VarSlideDGNeighbours(varSlideDG, n')
					&& n'.1 == Phi && VarSlideDGReachableVia(varSlideDG, varslide1, prefix, n', VarSlideDGVarSlides(varSlideDG)))
				==
					
			




					!SlideDependence(CFGOf(S), slide1, slide2, S); // בטוח נכון כי יש קשת
				==>
					false;
				}
			}
		}
		
		/*var n' := VarSlideOf(S, S', n);
		EdgeToVarPhiPath(n, slide2, slideDG, varSlideDG, S, S', XLs, X);
		assert VarSlideDGReachablePhi(varSlideDG, n', varslide2, VarSlideDGVarSlides(varSlideDG));
		// ==>
		assert VarSlideDGReachable(varSlideDG, n', varslide2, VarSlideDGVarSlides(varSlideDG));
		assert VarSlideDGReachable(varSlideDG, varslide1, n', VarSlideDGVarSlides(varSlideDG)) by {
			PathCorrespondenceVia(slideDG, varSlideDG, slide1, n, S, S', XLs, X, prefix);
		}
		// ==> lemma: (from', n') && (n', to') ==> (from', to')
		assert VarSlideDGReachable(varSlideDG, varslide1, varslide2, VarSlideDGVarSlides(varSlideDG));*/
	}
}

/*
lemma VarPhiPathToEdge(slide1: Slide, slide2: Slide, slideDG: SlideDG, varSlideDG: VarSlideDG, S: Statement, S': Statement)
	requires Valid(S) && Core(S)
	requires Valid(S') && Core(S')
	requires VarSlideDGReachablePhi(varSlideDG, VarSlideOf(S, S', slide1), VarSlideOf(S, S', slide2), VarSlideDGVarSlides(varSlideDG))
	//requires connection between SV and SV'
	ensures slide2 in SlideDGMap(slideDG)
	ensures slide1 in SlideDGMap(slideDG)[slide2]

//  למה עבור מסלול מוארסלייד1 לוארסלייד2 שעובר דרך 0 או יותר קודקודי פי, קיימת קשת מסלייד1 לסלייד2

lemma PathBackCorrespondence(slideDG: SlideDG, varSlideDG: VarSlideDG, slide1: Slide, slide2: Slide, S: Statement, S': Statement)
	requires Valid(S) && Core(S)
	requires Valid(S') && Core(S')
	requires VarSlideTag(VarSlideOf(S, S', slide1)) == Regular && VarSlideTag(VarSlideOf(S, S', slide2)) == Regular
	requires VarSlideDGReachable(varSlideDG, VarSlideOf(S, S', slide1), VarSlideOf(S, S', slide2), VarSlideDGVarSlides(varSlideDG))
	//requires connection between SV and SV'
	ensures SlideDGReachable(slideDG, slide1, slide2, SlideDGSlides(slideDG))
*/

lemma {:verify false}PathCorrespondence(slideDG: SlideDG, varSlideDG: VarSlideDG, slide1: Slide, slide2: Slide, S: Statement, S': Statement, XLs: seq<set<Variable>>, X: seq<Variable>)
	requires Valid(S) && Core(S)
	requires Valid(S') && Core(S')
	requires IsSlideDGOf(slideDG, S)
	requires IsVarSlideDGOf(varSlideDG, S)
	requires RemoveEmptyAssignments(Rename(S', XLs, X)) == S
	requires SlideDGReachable(slideDG, slide1, slide2, SlideDGSlides(slideDG))
	ensures VarSlideDGReachable(varSlideDG, VarSlideOf(S, S', slide1), VarSlideOf(S, S', slide2), VarSlideDGVarSlides(varSlideDG))
{
	var via :| SlideDGReachableVia(slideDG, slide1, via, slide2, SlideDGSlides(slideDG));

	PathCorrespondenceVia(slideDG, varSlideDG, slide1, slide2, S, S', XLs, X, via);
}

lemma {:verify false}PathCorrespondenceVia(slideDG: SlideDG, varSlideDG: VarSlideDG, slide1: Slide, slide2: Slide, S: Statement, S': Statement, XLs: seq<set<Variable>>, X: seq<Variable>, via: SlideDGPath)
	requires Valid(S) && Core(S)
	requires Valid(S') && Core(S')
	requires IsSlideDGOf(slideDG, S)
	requires IsVarSlideDGOf(varSlideDG, S)
	requires RemoveEmptyAssignments(Rename(S', XLs, X)) == S
	requires SlideDGReachable(slideDG, slide1, slide2, SlideDGSlides(slideDG))
	ensures VarSlideDGReachable(varSlideDG, VarSlideOf(S, S', slide1), VarSlideOf(S, S', slide2), VarSlideDGVarSlides(varSlideDG))
	decreases via
{
	var varslide1 := VarSlideOf(S, S', slide1);
	var varslide2 := VarSlideOf(S, S', slide2);

	match via {
	case Empty => 
		assert varslide1 == varslide2 by { assert slide1 == slide2; }
	case Extend(prefix, n) =>
	//		 (prefix) 
	// slide1 ------> n -> slide2
		assert n in SlideDGSlides(slideDG) && slide2 in SlideDGNeighbours(slideDG, n) && SlideDGReachableVia(slideDG, slide1, prefix, n, SlideDGSlides(slideDG));
		var n' := VarSlideOf(S, S', n);
		EdgeToVarPhiPath(n, slide2, slideDG, varSlideDG, S, S', XLs, X);
		assert VarSlideDGReachablePhi(varSlideDG, n', varslide2, VarSlideDGVarSlides(varSlideDG));
		// ==>
		assert VarSlideDGReachable(varSlideDG, n', varslide2, VarSlideDGVarSlides(varSlideDG));
		assert VarSlideDGReachable(varSlideDG, varslide1, n', VarSlideDGVarSlides(varSlideDG)) by {
			PathCorrespondenceVia(slideDG, varSlideDG, slide1, n, S, S', XLs, X, prefix);
		}
		// ==> lemma: (from', n') && (n', to') ==> (from', to')
		assert VarSlideDGReachable(varSlideDG, varslide1, varslide2, VarSlideDGVarSlides(varSlideDG));
	}
}
	

/*lemma L4(X: set<Variable>, vsSSA: VariablesSSA, v': Variable, V': set<Variable>, instancesOfFinalDefSlide: set<Variable>,
		 finalDefSlide: Slide, S: Statement, slideDG: SlideDG, cfg: CFG, V: set<Variable>, slide: Slide, slidesSV: set<Slide>,
		 slideOfV': VarSlide, finalDefVarSlides: set<VarSlide>, varSlideDG: VarSlideDG, SV': Statement)
	//requires forall Sm :: Sm in finalDefSlides(S, slideDG, cfg, V) || (exists Sn :: Sn in finalDefSlides(S, slideDG, cfg, V) && SlideDGReachable(slideDG, slide, Sn, SlideDGSlides(slideDG)))	
	requires slide in slidesSV
	requires slide !in finalDefSlides(S, slideDG, cfg, V)
	requires finalDefSlide in finalDefSlides(S, slideDG, cfg, V) && SlideDGReachable(slideDG, slide, finalDefSlide, SlideDGSlides(slideDG))
	requires instancesOfFinalDefSlide == setOf(vsSSA.getInstancesOfVaribleFunc(SlideVariable(finalDefSlide)))
	requires {v'} == instancesOfFinalDefSlide * V'
	requires slideOfV' == varslideof(v') // TODO
	requires VarSlideTag(slideOfV') == Phi
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
	requires IsVarSlideDGOf(varSlideDG, S) // varSlideDG is of S
	ensures var varSlidesSV: set<VarSlide> := varSlidesOf(SV, V); forall Sm :: Sm in varSlidesSV <==> (VarSlideVariable(Sm) in V || (exists Sn: VarSlide :: VarSlideVariable(Sn) in V && VarSlideDGReachable(varSlideDG, Sm, Sn, VarSlideDGVarSlides(varSlideDG))))	 // Implement VarSlideDGReachable
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