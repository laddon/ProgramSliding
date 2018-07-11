include "Definitions.dfy"
include "Substitutions.dfy"
include "Util.dfy"
include "CorrectnessSSA.dfy"
include "SlideDG.dfy"
include "VarSlideDG.dfy"
include "SSA.dfy"
include "Slicing.dfy"

/*method SSASlice(S: Statement, V: set<Variable>) returns (res: Statement)
	requires Valid(S)
	requires Core(S)
	decreases *
{
	var cfg := ComputeCFG(S);
	var pdgN, pdgE := ComputePDG(S, cfg); // TODO: Change to PDG
	var slideDG := ComputeSlideDG(S, pdgN, pdgE);

	res := ComputeSSASlice(S, V, slideDG, cfg);
}*/


lemma IdenticalSlices(S: Statement, V: set<Variable>, slidesSV: set<Slide>, varSlidesSV: set<VarSlide>, slideDG: SlideDG, cfg: CFG, varSlideDG: VarSlideDG)
	//  var varSlidesSV: set<VarSlide> := varSlidesOf(res, V); // from ComputeSSASlice
	requires Valid(S)					// for statementOf
	requires Core(S)					// for statementOf
	requires slidesSV <= allSlides(S)	// for statementOf
	requires VarSlideDGOf(varSlideDG, S)
	requires SlideDGOf(slideDG, S)
	requires forall Sm :: Sm in slidesSV <==> (Sm in finalDefSlides(S, slideDG, cfg, V) || (exists Sn :: Sn in finalDefSlides(S, slideDG, cfg, V) && SlideDGReachable(Sm, Sn, slideDG.1)))	 
	requires forall Sm :: Sm in varSlidesSV <==> (Sm.0 in V || (exists Sn: VarSlide :: Sn.0 in V && VarSlideDGReachable(Sm, Sn, varSlideDG.1)))

	ensures statementOf(slidesSV, S) == varStatementOf(varSlidesSV, S)
{
	
}

function SliceOf(S: Statement, V: set<Variable>): Statement
{
	var cfg := ComputeCFG(S);
	var pdg := PDG(S, cfg);
	var slideDG := SlideDG(S, pdg);
	var slidesSV := set Sm | Sm in finalDefSlides(S, slideDG, cfg, V) || (exists Sn :: Sn in finalDefSlides(S, slideDG, cfg, V) && SlideDGReachable(Sm, Sn, slideDG.1));

	statementOf(slidesSV, S)
}

method SSASlice(S: Statement, V: set<Variable>) returns (res: Statement)
	requires Valid(S)
	requires Core(S)
	decreases *
	ensures SliceOf(S,V) == res 
{
	var varSlideDG := ComputeVarSlideDG(S);

	res := ComputeSSASlice(S, V, varSlideDG);
}

//method ComputeSSASlice(S: Statement, V: set<Variable>, ghost slideDG: SlideDG, ghost cfg: CFG) returns (res: Statement)
method ComputeSSASlice(S: Statement, V: set<Variable>, ghost varSlideDG: VarSlideDG) returns (res: Statement)
	requires Valid(S)
	requires Core(S)
	requires VarSlideDGOf(varSlideDG, S)
	decreases *
	ensures Valid(res)
	ensures Core(res)
	ensures var varSlidesRes: set<VarSlide> := varSlidesOf(res, V); forall Sm :: Sm in varSlidesRes <==> (Sm.0 in V || (exists Sn: VarSlide :: Sn.0 in V && VarSlideDGReachable(Sm, Sn, varSlideDG.1)))	 // Implement VarSlideDGReachable
	ensures Substatement(res, S)
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

	// Create varSlideDG for S'
	ghost var varSlideDG' := ComputeVarSlideDG(S');
	assert VarSlideDGOf(varSlideDG, S);

	// V' := foreach v in V find liveOnExit v
	var VSeq := setToSeq(V);
	var instancesOfVSeq := vsSSA.getInstancesOfVaribleSeq(VSeq);
	var V' := setOf(instancesOfVSeq) * liveOnExitX;

	// Flow-Insensitive Slice
	var SV' := ComputeFISlice(S', V', varSlideDG');
	ghost var varSlidesSV: set<VarSlide> := varSlidesOf(SV', V');
	assert forall Sm :: Sm in varSlidesSV <==> (Sm.0 in V' || (exists Sn: VarSlide :: Sn.0 in V' && VarSlideDGReachable(Sm, Sn, varSlideDG'.1)));	 // Implement VarSlideDGReachable

	// From SSA
	var XL1i := liveOnEntryXSeq;
	var XL2f := liveOnExitXSeq;
	res := FromSSA(SV', X, XL1i, XL2f, Y, XLs, vsSSA, V, S', V', varSlideDG, varSlideDG');


}

// Moved to Slidedg
/*function slidesOf(S: Statement, V: set<Variable>) : set<Slide>
	reads *
	requires Valid(S)
	requires Core(S)
{
	slidesOf'(S, V, [], {})
}

function slidesOf'(S: Statement, V: set<Variable>, l: Label, nodes: set<CFGNode>) : set<Slide>
	reads *
	requires Valid(S)
	requires Core(S)
{
	match S {
	case Skip => {}
	case Assignment(LHS,RHS) => set v | v in V * setOf(LHS) :: (CFGNode.Node(l), v, nodes)
	case SeqComp(S1,S2) =>		slidesOf'(S1, V, l+[1], nodes) + slidesOf'(S2, V, l+[2], nodes)
	case IF(B0,Sthen,Selse) =>	slidesOf'(Sthen, V, l+[1], nodes + {CFGNode.Node(l)}) + slidesOf'(Selse, V, l+[2], nodes + {CFGNode.Node(l)})
	case DO(B,Sloop) =>			slidesOf'(Sloop, V, l+[1], nodes + {CFGNode.Node(l)})
	}
}*/

function varStatementOf(slides: set<VarSlide>, S: Statement): Statement
{
//type VarSlide = (Variable, VarSlideTag)

	if varSlides == {} then Skip
	else
	var varSlide :| varSlide in varSlides;
	match varSlide.0 {
	/*case Node(l) => 	var S' := statementOfSlide(varSlide, l, S);
						var rest := statementOf(varSlides - {varSlide}, S);
						mergeStatements(S', rest, S)
	case Entry =>		Skip // ?
	case Exit =>		Skip // ?*/
	}
}

function statementOf(slides: set<Slide>, S: Statement): Statement
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
	case Node(l) => 	var S' := statementOfSlide(slide, l, S);
						var rest := statementOf(slides - {slide}, S);
						mergeStatements(S', rest, S)
	case Entry =>		Skip // ?
	case Exit =>		Skip // ?
	}
}

function allSlides(S: Statement) : set<Slide>
	reads *
	requires Valid(S)
	requires Core(S)
{
	slidesOf(S, def(S))
}

function statementOfSlide(slide: Slide, l: Label, S: Statement): Statement
	reads *
	requires Valid(S)
	requires Core(S)
	requires |l| >= 1
	//requires ValidLabel(l, S)?
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

function mergeStatements(S1: Statement, S2: Statement, S: Statement) : Statement
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

function mergeAssignments(LHS1: seq<Variable>, LHS2: seq<Variable>, RHS1: seq<Expression>, RHS2: seq<Expression>, vars: set<Variable>) : (seq<Variable>, seq<Expression>)
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

predicate Substatement(S': Statement, S: Statement)
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
								case Assignment(LHS',RHS') => |LHS'| <= |LHS| && |RHS'| <= |RHS| && assignmentsMatch(LHS, LHS', RHS, RHS')
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

predicate assignmentsMatch(LHS: seq<Variable>, LHS': seq<Variable>, RHS: seq<Expression>, RHS': seq<Expression>)
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
				assignmentsMatch(LHS, LHS'[1..], RHS, RHS'[1..])		
}

function findVariableInSeq(v: Variable, vars: seq<Variable>): int
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
	ensures var varSlidesSV: set<VarSlide> := varSlidesOf(SV, V); forall Sm :: Sm in varSlidesSV <==> (Sm.0 in V || (exists Sn: VarSlide :: Sn.0 in V && VarSlideDGReachable(Sm, Sn, varSlideDG.1)))	 // Implement VarSlideDGReachable
	ensures Substatement(SV, S)
{
	var Vstar := ComputeSlidesDepRtc(S, V);

	SV := ComputeSlides(S, Vstar);
}