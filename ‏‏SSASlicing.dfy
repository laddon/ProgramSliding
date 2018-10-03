include "Definitions.dfy"
include "Substitutions.dfy"
include "Util.dfy"
include "CorrectnessSSA.dfy"
include "SlideDG.dfy"
include "VarSlideDG.dfy"
include "SSA.dfy"
include "Slicing.dfy"

/*lemma {:verify false}IdenticalSlices(S: Statement, V: set<Variable>, slidesSV: set<Slide>, varSlidesSV: set<VarSlide>, slideDG: SlideDG, cfg: CFG, varSlideDG: VarSlideDG)
	//  var varSlidesSV: set<VarSlide> := varSlidesOf(res, V); // from ComputeSSASlice
	requires Valid(S)					// for statementOf
	requires Core(S)					// for statementOf
	requires slidesSV <= allSlides(S)	// for statementOf
	requires VarSlideDGOf(varSlideDG, S)
	requires SlideDGOf(slideDG, S)
	requires forall Sm :: Sm in slidesSV <==> (Sm in finalDefSlides(S, slideDG, cfg, V) || (exists Sn :: Sn in finalDefSlides(S, slideDG, cfg, V) && SlideDGReachable(slideDG, Sm, Sn, slideDG.1)))	 
	requires forall Sm :: Sm in varSlidesSV <==> (Sm.0 in V || (exists Sn: VarSlide :: Sn.0 in V && VarSlideDGReachable(/*slideDG,*/ Sm, Sn, varSlideDG.1)))
	ensures statementOf(slidesSV, S) == varStatementOf(varSlidesSV, S)
*/



function {:verify false}SliceOf(S: Statement, V: set<Variable>): Statement
	ensures Valid(SliceOf(S,V)) && Core(SliceOf(S,V))
{
	var cfg := ComputeCFG(S);
	var slideDG := SlideDG(S, cfg);
	var slidesSV := set Sm | Sm in slidesOf(S,def(S)) && (exists Sn :: Sn in finalDefSlides(S, slideDG, cfg, V) && SlideDGReachable(slideDG, Sm, Sn, slideDG.1));

	statementOf(slidesSV, S)
}

method {:verify false}SSASlice(S: Statement, V: set<Variable>) returns (res: Statement)
	requires Valid(S)
	requires Core(S)
	decreases *
	ensures SliceOf(S,V) == res 
{
	var varSlideDG := ComputeVarSlideDG(S); // not needed

	res := ComputeSSASlice(S, V, varSlideDG);
}

method {:verify false}ComputeSSASlice(S: Statement, V: set<Variable>, ghost varSlideDG: VarSlideDG) returns (res: Statement)
	requires NoSelfAssignments(S) // requires there are no self assignments TODO
	requires Valid(S)
	requires Core(S)
	requires VarSlideDGOf(varSlideDG, S)
	decreases *
	ensures Valid(res)
	ensures Core(res)
	ensures var varSlidesRes: set<VarSlide> := varSlidesOf(res, V); forall Sm :: Sm in varSlidesRes <==> (Sm.0 in V || (exists Sn: VarSlide :: Sn.0 in V && VarSlideDGReachable(varSlideDG, Sm, Sn, varSlideDG.1)))	 // Implement VarSlideDGReachable
	ensures Substatement(res, S)
	//ensures var SV := SliceOf(S,V); MergeVars(SV) == res 
	//ensures SliceOf(S,V) == res
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
	assert forall i :: i in liveOnEntryX ==> vsSSA.existsVariable2(i);
	assert forall i :: i in liveOnExitX ==> vsSSA.existsVariable2(i);
	assert forall v :: v in X ==> vsSSA.existsInstance(v);
	var S' := ToSSA(S, X, liveOnEntryX, liveOnExitX, Y, XLs, vsSSA);

	// Create varSlideDG' for S'
	ghost var varSlideDG' := ComputeVarSlideDG(S');
	assert VarSlideDGOf(varSlideDG', S');

	// V' := foreach v in V find liveOnExit v
	var VSeq := setToSeq(V);
	assert forall v :: v in VSeq ==> vsSSA.existsInstance(v);
	var instancesOfVSeq := vsSSA.getInstancesOfVaribleSeq(VSeq);
	var V' := setOf(instancesOfVSeq) * liveOnExitX;

	// Flow-Insensitive Slice
	var SV' := ComputeFISlice(S', V', varSlideDG');
	ghost var varSlidesSV: set<VarSlide> := varSlidesOf(SV', V');
	assert forall Sm :: Sm in varSlidesSV <==> (exists Sn: VarSlide :: Sn.0 in V' && VarSlideDGReachable(varSlideDG', Sm, Sn, varSlideDG'.1));	 // Implement VarSlideDGReachable
	
	ghost var allSlides := slidesOf(S,def(S));
	ghost var SV := SliceOf(S,V);
	assert Valid(SV) && Core(SV); 
	ghost var slidesSV := slidesOf(SV,V);
	assert slidesSV <= allSlides;

	assert forall slide :: slide in SlideDGOf(S).1 ==> (slide in slidesSV <==> VarSlideOf(SV, SV', slide) in varSlidesSV) by {
		// p ==> q:	
		L1(setOf(X), S, SV, SV', slidesSV, varSlidesSV, vsSSA, V, V', varSlideDG/******/);
		assert forall slide :: slide in slidesSV ==> VarSlideOf(SV, SV', slide) in varSlidesSV;

		// ^p ==> ^q:
		L2(S, SV, SV', slidesSV, varSlidesSV, V, V', varSlideDG/******/, vsSSA);
		//assert forall slide :: slide !in slidesSV ==> VarSlideOf(SV, SV', slide) !in varSlidesSV;
		assert forall slide :: slide in SlideDGOf(S).1 - slidesSV ==> VarSlideOf(SV, SV', slide) !in varSlidesSV;
	}

	// From SSA
	var XL1i := liveOnEntryXSeq;
	var XL2f := liveOnExitXSeq;
	res := FromSSA(SV', X, XL1i, XL2f, Y, XLs, vsSSA, V, S', V', varSlideDG, varSlideDG');
	assert Substatement(res, S); // TODO!!!

	// להוכיח שקילות בין הסליידים של res
	// לבין varSlidesSV
	// בדומה לשורה 94.
	// וזה חובה להוכחת L9

	//assert forall varSlide :: varSlide in varSlidesSV <==> SlideOf(res, SV', varSlide) in slidesOf(res);


	/*
		;
	105    ;
		106  107
		
	(105;(106;107))

	        ;
		 ;    107
	 105   106
	
	 ((105;106);107)
	 */



	// Done. Now the proof:
	// ensures SliceOf(S,V) == res :

	// Option 1:
	// forall slide in slidesSV find VarSlideOf, then find statementOf(varSlide), then run FromSSA and get the original slide
	// (L8)
	// a*(b+c) = a*b+a*c
	// mergeStatements


	// Option 2:
	L9(S, V, res, SV, SV', slidesSV, varSlidesSV, varSlideDG, V'); // ensures allLabelsOf(SliceOf(S,V)) == allLabelsOf(res)
	// call L10 on different slides
	forall l | l in allLabelsOf(SliceOf(S,V)) /*&& l represents multiple assignment*/ ensures slipOf(SliceOf(S,V), l) == slipOf(res, l) {
		//////L10(SliceOf(S,V), res ,l); // ensures slipOf(SliceOf(S,V), l) == slipOf(res, l)
	}
	
	//assert allLabelsOf(SliceOf(S,V)) == allLabelsOf(res) && forall l: Label :: l in allLabelsOf(SliceOf(S,V)) ==> slipOf(SliceOf(S,V), l) == slipOf(res, l);
}

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
	requires NoSelfAssignments(S)
	requires Valid(S) && Core(S)
	requires Valid(SV) && Core(SV)
	requires Valid(SV') && Core(SV')
	requires var slideDG := SlideDGOf(S); forall Sm :: Sm in slidesSV <==> (Sm in slidesOf(S,def(S)) && exists Sn :: Sn in finalDefSlides(S, slideDG, CFGOf(S), V) && SlideDGReachable(slideDG, Sm, Sn, slideDG.1));
	requires forall vSlide :: vSlide in varSlidesSV ==> (vSlide in varSlidesOf(S,def(S)) && exists Sn: VarSlide :: Sn.0 in V' && VarSlideDGReachable(varSlideDG, vSlide, Sn, varSlideDG.1));
	requires forall slide :: slide in slidesSV <==> VarSlideOf(SV, SV', slide) in varSlidesSV

	ensures allLabelsOf(SliceOf(S,V)) == allLabelsOf(res)


function {:verify false}slipOf(S: Statement, l: Label): Statement
	requires ValidLabel(l, S) // l matching S
	ensures Valid(slipOf(S, l)) && Core(slipOf(S, l))
{
	if l == [] then S
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

lemma {:verify false}L1(X: set<Variable>, S: Statement, SV: Statement, SV': Statement, slidesSV: set<Slide>, varSlidesSV: set<VarSlide>, vsSSA: VariablesSSA, V: set<Variable>, V': set<Variable>, varSlideDG: VarSlideDG)
	requires Valid(S) && Core(S)
	requires Valid(SV) && Core(SV)
	requires Valid(SV') && Core(SV')
	requires ValidVsSSA(vsSSA)
	ensures forall slide :: slide in slidesSV ==> VarSlideOf(SV, SV', slide) in varSlidesSV
{
	forall slide | slide in slidesSV ensures VarSlideOf(SV, SV', slide) in varSlidesSV {
		assert slide in slidesSV;
		
		var varSlide := VarSlideOf(SV, SV', slide);
		var cfg := ComputeCFG(S);
		var slideDG := SlideDG(S, cfg);

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
	requires var slideDG := SlideDGOf(S); forall Sm :: Sm in slidesSV <==> (Sm in slidesOf(S,def(S)) && exists Sn :: Sn in finalDefSlides(S, slideDG, CFGOf(S), V) && SlideDGReachable(slideDG, Sm, Sn, slideDG.1));
	requires forall vSlide :: vSlide in varSlidesSV ==> (vSlide in varSlidesOf(S,def(S)) && exists Sn: VarSlide :: Sn.0 in V' && VarSlideDGReachable(varSlideDG, vSlide, Sn, varSlideDG.1));
	ensures forall slide :: slide in SlideDGOf(S).1 - slidesSV ==> VarSlideOf(SV, SV', slide) !in varSlidesSV;
{
	var cfg := ComputeCFG(S);
	var slideDG := SlideDG(S, cfg); 
	assume slideDG == SlideDGOf(S); 
	assume cfg == CFGOf(S);
	assert forall slide :: slide in SlideDGOf(S).1 - slidesSV ==> VarSlideOf(SV, SV', slide) !in varSlidesSV by {

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
	requires slides <= allSlides(S)
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
	case Node(l) => 	assert ValidLabel(l, S);
						var S' := statementOfSlide(slide, l, S);
						var rest := statementOf(slides - {slide}, S);
						mergeStatements(S', rest, S)
	case Entry =>		Skip // ?
	case Exit =>		Skip // ?
	}
}

function {:verify true}allSlides(S: Statement) : set<Slide>
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
	|l| >= 1 && |l| <= maxLabelSize(S)
}

function {:verify true}maxLabelSize(S: Statement): int
	reads *
	requires Valid(S)
	requires Core(S)
{
	match S {
	case Skip => 1
	case Assignment(LHS,RHS) =>	1
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
	match S {
	case Skip => Skip
	case Assignment(LHS,RHS) => S
	case SeqComp(S1,S2) =>		if l[0] == 1 then SeqComp(statementOfSlide(slide, l[1..], S1), Skip)  else SeqComp(Skip, statementOfSlide(slide, l[1..], S2))
	case IF(B0,Sthen,Selse) =>	if l[0] == 1 then IF(B0, statementOfSlide(slide, l[1..], Sthen), Skip) else IF(B0, Skip, statementOfSlide(slide, l[1..], Selse))
	case DO(B,Sloop) =>			DO(B, statementOfSlide(slide, l[1..], Sloop))
	}
}

function {:verify true}mergeStatements(S1: Statement, S2: Statement, S: Statement) : Statement
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
{
	match S1 {
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
	}
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
								case Assignment(LHS',RHS') => |LHS'| <= |LHS| && |RHS'| <= |RHS| && SubAssignment(LHS', RHS', LHS, RHS)
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
								case IF(B0',Sthen',Selse') => B0 == B0' && Substatement(Sthen', Sthen) && Substatement(Selse', Selse)
								case DO(B',Sloop') => false
								}
	case DO(B,Sloop) =>			match S' {
								case Skip => true
								case Assignment(LHS',RHS') => false
								case SeqComp(S1',S2') => false								
								case IF(B0',Sthen',Selse') => false
								case DO(B',Sloop') => B == B' && Substatement(Sloop', Sloop)
								}
	}
}

predicate {:verify true}SubAssignment(LHS': seq<Variable>, RHS': seq<Expression>, LHS: seq<Variable>, RHS: seq<Expression>)
	requires |LHS'| <= |LHS| && |RHS'| <= |RHS| && |LHS'| == |RHS'| && |LHS| == |RHS|
{
	// S:   x,y,z := 1,2,3;
	// S':  z,x := 3,1;

	if LHS' == [] then true
	else
		if LHS'[0] !in LHS then false
		else
			var i := findVariableInSeq(LHS'[0], LHS);
			if RHS'[0] != RHS[i] then false
			else
				SubAssignment(LHS'[1..], RHS'[1..], LHS, RHS)		
}

function {:verify true}findVariableInSeq(v: Variable, vars: seq<Variable>): int
	requires v in vars
	ensures 0 <= findVariableInSeq(v, vars) < |vars|
{
	if vars[0] == v then 0
	else findVariableInSeq(v, vars[1..]) + 1
}


///////////////////////////////////////////////////////////////////////////////////////////////////



/*if y == 0
	x := 1;
else
	x := 2;



if y == 0
	x1 := 1;
	x3 := x1;
else
	x2 := 2;
	x3 := x2;



if y == 0
	x := 1;
else
	;


if y == 0
	x1 := 1;
	;
else
	;*/

/*
// Original S:

i=0
sum=0
prod=1
while i<a.len do
	sum=sum+a[i]
	prod=prod*a[i]
	i=i+1
od
i=0

// FISlice Of {prod}

i=0

prod=1
while i<a.len do

	prod=prod*a[i]
	i=i+1
od
i=0


// To SSA:

|[ var i0,sum0,prod0,i1,i4,i7,i8,sum2,sum4,sum5,prod3,prod4,prod6,prod7;

i0,sum0,prod0=i,sum,prod

i1=0
sum2=0
prod3=1
i4,sum4,prod4=i1,sum2,prod3
while i4<a.len do
	sum5=sum4+a[i4]
	prod6=prod4*a[i4]
	i7=i4+1
	i4,sum4,prod4=i7,sum5,prod6
od
i8=0

i,sum,prod=i8,sum4,prod4 ]|


// FISlice:

V={prod}
V'={prod4}

|[ var i0,sum0,prod0,i1,i4,i7,i8,sum2,sum4,sum5,prod3,prod4,prod6,prod7;

i0,sum0,prod0=i,sum,prod

i1=0

prod3=1
i4,prod4=i1,prod3
while i4<a.len do
	
	prod6=prod4*a[i4]
	i7=i4+1
	i4,prod4=i7,prod6
od


i,sum,prod=i8,sum4,prod4 ]|

glob(slides(prod4))={prod4,prod3,prod6,i4,a}
U1={prod4,prod3,prod6,i4}
V1={prod4,prod3,prod6,i4}
glob(slides(prod4,prod3,prod6,i4))={prod4,prod3,prod6,i1,i4,i7,a}
U2={prod4,prod3,prod6,i1,i4,i7}
V2={prod4,prod3,prod6,i1,i4,i7} - VStar


// From SSA:

i=0
prod=1
while i<a.len do
	prod=prod*a[i]
	i=i+1
od


*/


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



lemma {:verify false}L20(S: Statement, S': Statement, SV': Statement, res: Statement, X: seq<Variable>, XLs: seq<set<Variable>>, l: Label, varLabel: Label) // called with l==varLabel==[]
	requires Valid(S) && Valid(S') && Valid(SV') && Valid(res)
	requires Core(S) && Core(S') && Core(SV') && Core(res)
	requires ValidLabel(l, S)
	requires ValidLabel(l, res)
	requires ValidLabel(varLabel, SV')
	requires ValidLabel(varLabel, S')
	requires MatchingLabels(res, l, SV', varLabel)
	requires MergedVars1(SV', res, XLs, X) // FromSSA Postcondition
	ensures Substatement(res, S)
{
	var slipOfS := slipOf(S, l);
	var slipOfRes := slipOf(res, l);
	var slipOfSV' := slipOf(SV', varLabel);

	match slipOfS {
	case Skip =>				assert slipOfRes == Skip; // There is no statement to slice from, therefore slipOfRes is also skip		
	case Assignment(LHS,RHS) =>	match slipOfRes { // Assignment or Skip
								case Skip =>						assert Substatement(Skip, Assignment(LHS,RHS));
								case Assignment(resLHS,resRHS) =>	assert SubAssignment(resLHS, resRHS, LHS, RHS) by {
																		match slipOfSV' {
																		case Assignment(SV'LHS,SV'RHS) => L22(S, S', SV', res, X, XLs, l, varLabel);
																		case SeqComp(SV'S1,SV'S2) => L22(S, S', SV', res, X, XLs, l, varLabel+[1]); // The last assignment of while or if
																		}
																	}
								case SeqComp(resS1,resS2) =>		assert false;
								case IF(resB0,resSthen,resSelse) => assert false;
								case DO(resB,resSloop) =>			assert false;
								}
	case SeqComp(S1,S2) =>		match slipOfRes { // SeqComp or Skip
								case Skip =>						assert Substatement(Skip, SeqComp(S1,S2));
								case Assignment(resLHS,resRHS) =>	assert false;
								case SeqComp(resS1,resS2) =>		L20(S, S', SV', res, X, XLs, l+[1], varLabel+[1]);
																	L20(S, S', SV', res, X, XLs, l+[2], varLabel+[2]);
								case IF(resB0,resSthen,resSelse) => assert false;
								case DO(resB,resSloop) =>			assert false;
								}	
	case IF(B0,Sthen,Selse) =>	match slipOfRes { // IF or Skip
								case Skip =>						assert Substatement(Skip, IF(B0,Sthen,Selse));
								case Assignment(resLHS,resRHS) =>	assert false;
								case SeqComp(resS1,resS2) =>		assert false;
								case IF(resB0,resSthen,resSelse) => assert EqualBooleanExpressions(B0, resB0);
																	L20(S, S', SV', res, X, XLs, l+[1], varLabel+[1]);
																	L20(S, S', SV', res, X, XLs, l+[2], varLabel+[2]);
								case DO(resB,resSloop) =>			assert false;
								}
	case DO(B,Sloop) =>			match slipOfRes { // DO or Skip
								case Skip =>						assert Substatement(Skip, DO(B,Sloop));
								case Assignment(resLHS,resRHS) =>	assert false;
								case SeqComp(resS1,resS2) =>		assert false;
								case IF(resB0,resSthen,resSelse) => assert false;
								case DO(resB,resSloop) =>			assert EqualBooleanExpressions(B, resB);
																	L20(S, S', SV', res, X, XLs, l+[1], varLabel+[2,1]);
								}
	}
}

lemma {:verify false}L22(S: Statement, S': Statement, SV': Statement, res: Statement, X: seq<Variable>, XLs: seq<set<Variable>>, l: Label, varLabel: Label)
	requires Valid(S) && Valid(S') && Valid(SV') && Valid(res)
	requires Core(S) && Core(S') && Core(SV') && Core(res)
	requires ValidLabel(l, S)
	requires ValidLabel(l, res)
	requires ValidLabel(varLabel, SV')
	requires ValidLabel(varLabel, S')
	requires MatchingLabels(res, l, SV', varLabel)
	requires exists LHS,RHS :: S == Assignment(LHS,RHS)
	requires exists resLHS,resRHS :: res == Assignment(resLHS,resRHS)
	requires Substatement(SV', S')
	ensures forall LHS,RHS,resLHS,resRHS :: S == Assignment(LHS,RHS) && res == Assignment(resLHS,resRHS) ==> SubAssignment(resLHS, resRHS, LHS, RHS)
{
	var slipOfS := slipOf(S,l);
	var slipOfRes := slipOf(res,l);
	var slipOfSV' := slipOf(SV',varLabel);
	var slipOfS' := slipOf(S',varLabel);

	match slipOfS {	
	case Assignment(LHS,RHS) => match slipOfRes {	
								case Assignment(resLHS,resRHS) => assert SubAssignment(resLHS, resRHS, LHS, RHS) by {
																	  match slipOfSV' {	
																	  case Assignment(SV'LHS,SV'RHS) => assert Rename(slipOfSV', XLs, X) == slipOfRes;
																										match slipOfS' {
																										case Assignment(S'LHS,S'RHS) => // Has to be assignment because Substatement(SV',S')
																											assert SubAssignment(SV'LHS, SV'RHS, S'LHS, S'RHS);
																											assert RenameToSSA(slipOfS, 1).0 == slipOfS';
																										}
																	  }			
																  }
	
								assert SubAssignment(resLHS, resRHS, LHS, RHS);					 
								}

	assert forall resLHS,resRHS :: slipOfRes == Assignment(resLHS,resRHS) ==> SubAssignment(resLHS, resRHS, LHS, RHS);
	}

	assert forall LHS,RHS,resLHS,resRHS :: slipOfS == Assignment(LHS,RHS) && slipOfRes == Assignment(resLHS,resRHS) ==> SubAssignment(resLHS, resRHS, LHS, RHS);
}

predicate MatchingLabels(S: Statement, l: Label, S': Statement, varLabel: Label)
	requires Valid(S) && Valid(S')
	requires Core(S) && Core(S')
	requires ValidLabel(l, S)
	requires ValidLabel(varLabel, S')
{
	var slipOfS := slipOf(S, l);
	var slipOfS' := slipOf(S', varLabel);


	match slipOfS {
	case Skip =>				slipOfS' == Skip
	case Assignment(LHS,RHS) =>	exists LHS1,RHS1 :: slipOfS' == Assignment(LHS1,RHS1)
	case SeqComp(S1,S2) =>		exists S11,S22 :: slipOfS' == SeqComp(S11,S22)
	case IF(B,Sthen,Selse) =>	exists B1,Sthen1,Selse1 :: slipOfS' == IF(B1,Sthen1,Selse1)
	case DO(B,Sloop) =>			exists B1,Sloop1 :: slipOfS' == DO(B1,Sloop1) 
	}	
}