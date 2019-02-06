include "VarSlideDG.dfy"
include "SlideDG.dfy"

// Moved to SlideDG.dfy - 28/1/19
/*function slipOf(S: Statement, l: Label): Statement
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
}*/

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

function allLabelsOf(S: Statement): set<Label>
	reads *
	requires Valid(S) && Core(S)
{
	assert ValidLabel([], S);
	allLabelsOfStatement(S, [])
}

function allLabelsOfStatement(S: Statement, l: Label): set<Label>
	reads *
	requires Valid(S) && Core(S)
	ensures forall la :: la in allLabelsOfStatement(S, l) ==> ValidLabel(la, S)
{
	match S {
		case Assignment(LHS,RHS) => {l}
		case SeqComp(S1,S2) =>		{l} + allLabelsOfStatement(S1, l+[1]) + allLabelsOfStatement(S2, l+[2])
		case IF(B0,Sthen,Selse) =>	{l} + allLabelsOfStatement(Sthen, l+[1]) + allLabelsOfStatement(Selse, l+[2])
		case DO(B,S1) =>			{l} + allLabelsOfStatement(S1, l+[1])
		case Skip =>				{l}
	}	
}

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
		case Node(l) => var varLabel := VarLabelOf(S, S', l); var i := InstanceOf(S', varLabel); (i, Regular, varLabel)
		case Entry => ("", Regular, []) // מיותר! הוספתי רק כדי שירוץ
		case Exit => ("", Regular, []) // מיותר! הוספתי רק כדי שירוץ
	}
}

function VarLabelOf(S: Statement, S': Statement, l: Label): Label
	//requires S == RemoveEmptyAssignments(Rename(S', XLs, X))
	reads *
	requires Valid(S)
	requires Valid(S')
	requires Core(S)
	requires Core(S')
	requires ValidLabel(l, S)
	//ensures |VarLabelOf(S, S', l)| >= 1 && |VarLabelOf(S, S', l)| <= maxLabelSize(S')
	ensures ValidLabel(VarLabelOf(S, S', l), S')
{
	match S {
	case Skip =>				assume IsSkip(S');
								assert l == [];
								[]	
	case Assignment(LHS,RHS) =>	assume IsAssignment(S');
								assert l == [];
								[]
	case SeqComp(S1,S2) =>		if l == [] then [] else
								assume IsSeqComp(S');
								match S' {
								case SeqComp(S1',S2') => if l[0] == 1 then [1] + VarLabelOf(S1, S1', l[1..]) else [2] + VarLabelOf(S2, S2', l[1..])
								}	
	case IF(B0,Sthen,Selse) =>	if l == [] then [] else
								assume IsIF(S');
								match S' {							
								case IF(B0',Sthen',Selse') => if l[0] == 1 then [1,1] + VarLabelOf(Sthen, Sthen', l[1..]) else [2,1] + VarLabelOf(Selse, Selse', l[1..])
								}
	case DO(B,Sloop) =>			if l == [] then [2] else
								assume IsSeqComp(S');
								match S' {
								// S1' is the phi assignment and S2' is the DO
								// we should add another [2] in order to go to the loop
								case SeqComp(S1',S2') => assume IsDO(S2');
														 match S2' {
														 case DO(B',Sloop') => assume Valid(Sloop') && Core(Sloop'); [2,1,1] + VarLabelOf(Sloop, Sloop', l[1..])
														 }
								}
	}
}

/*function VarLabelOf(S: Statement, S': Statement, l: Label): Label
	//requires S == RemoveEmptyAssignments(Rename(S', XLs, X))
	reads *
	requires Valid(S)
	requires Valid(S')
	requires Core(S)
	requires Core(S')
	requires ValidLabel(l, S)
	//ensures |VarLabelOf(S, S', l)| >= 1 && |VarLabelOf(S, S', l)| <= maxLabelSize(S')
	ensures ValidLabel(VarLabelOf(S, S', l), S')
{
	if l == [] then []
	else
	match S {
	case Skip =>				assume IsSkip(S');
								match S' {
								case Skip => []
								}		
	case Assignment(LHS,RHS) =>	assume IsAssignment(S');
								match S' {
								case Assignment(LHS',RHS') => []
								}
	case SeqComp(S1,S2) =>		assume IsSeqComp(S');
								match S' {
								case SeqComp(S1',S2') => if l[0] == 1 then [1] + VarLabelOf(S1, S1', l[1..]) else [2] + VarLabelOf(S2, S2', l[1..])
								}	
	case IF(B0,Sthen,Selse) =>	assume IsIF(S');
								match S' {							
								case IF(B0',Sthen',Selse') => if l[0] == 1 then [1,1] + VarLabelOf(Sthen, Sthen', l[1..]) else [2,1] + VarLabelOf(Selse, Selse', l[1..])
								}
	case DO(B,Sloop) =>			assume IsSeqComp(S');
								match S' {
								// S1' is the phi assignment and S2' is the DO
								// we should add another [2] in order to go to the loop
								case SeqComp(S1',S2') => assume IsDO(S2');
														 match S2' {
														 case DO(B',Sloop') => assume Valid(Sloop') && Core(Sloop'); [2,1,1] + VarLabelOf(Sloop, Sloop', l[1..])
														 }
								}
	}
}*/


/*
call LabelOf:
var allLabelsRenameSV' := allLabelsOf(Rename(SV', XLsToSSA, X));
var selfEmptyLabelsSV' := selfEmptyLabelsOf(Rename(SV', XLsToSSA, X));
var nonSelfEmptyLabels := allLabelsRenameSV' - selfEmptyLabelsSV';
var varLabel :| varLabel in nonSelfEmptyLabels;
var l := LabelOf(selfEmptyLabelsSV', varLabel);
*/

function selfEmptyLabelsOf(S: Statement, allLabels: set<Label>): set<Label>
	reads *
	requires Valid(S) && Core(S)
	requires forall l :: l in allLabels ==> ValidLabel(l, S)
	ensures forall l :: l in selfEmptyLabelsOf(S, allLabels) ==> ValidLabel(l, S)
{
	if allLabels == {} then {}
	else
	
		var l :| l in allLabels;

		if IsSelfAssignment(slipOf(S, l)) || IsEmptyAssignment(slipOf(S, l)) then {l} + selfEmptyLabelsOf(S, allLabels - {l})
		else selfEmptyLabelsOf(S, allLabels - {l})
	
}

// varLabel in nonSelfEmptyLabels of SV'
function LabelOf(selfEmptyLabelsSV': set<Label>, varLabel: Label): Label
	//requires forall l :: l in selfEmptyLabelsSV' ==> l is SelfAssignment || l is EmptyAssignment
{
	if varLabel == [] then []
	else 	
		var newLabel := if varLabel[..|varLabel|-1] == [1] then varLabel[..|varLabel|-1] + [2] else varLabel[..|varLabel|-1] + [1];

		if newLabel in selfEmptyLabelsSV' then
			LabelOf(selfEmptyLabelsSV', varLabel[..|varLabel|-1])
		else
			LabelOf(selfEmptyLabelsSV', varLabel[..|varLabel|-1]) + [varLabel[|varLabel|-1]]
}

function {:verify false}LabelOf2(S': Statement, S: Statement, varLabel: Label): Label
	reads *
	requires Valid(S')
	requires Valid(S)
	requires Core(S')
	requires Core(S)
	ensures |LabelOf2(S', S, varLabel)| >= 1 && |LabelOf2(S', S, varLabel)| <= maxLabelSize(S)
	ensures ValidLabel(LabelOf2(S', S, varLabel), S)
{
	var l :| VarLabelOf(S, S', l) == varLabel;
	l
/*	match S' {
	case Skip =>					[]		
	
	case Assignment(LHS',RHS') =>	match S {
									case Assignment(LHS,RHS) => []
									}

	case SeqComp(S1',S2') =>		if IsDO(S2') then
										match S2' {
										case DO(B'',Sloop'') =>
											match Sloop'' {
											case SeqComp(S1''',S2''') =>
												match S {
												case DO(B,Sloop) =>	[1] + LabelOf(S1''', Sloop, varLabel[3..])
												}
											}
										}
									else
										if varLabel[0] == 1 then [1] + LabelOf(S1', S1, varLabel[1..]) else [2] + LabelOf(S2', S2, varLabel[1..])	
	
	case IF(B0',Sthen',Selse') =>	if varLabel[0] == 1 then
									match Sthen' {
									case SeqComp(S1',S2') =>
										match S {
										case IF(B0,Sthen,Selse) => [1] + LabelOf(S1', Sthen, varLabel[1..])
										}
									}
									else
									match Selse' {
									case SeqComp(S1',S2') =>	
										match S {
										case IF(B0,Sthen,Selse) => [1] + LabelOf(S1', Selse, varLabel[1..])
										}
									}
	
	case DO(B',Sloop') =>			[]
	}
*/
}

function {:verify false}InstanceOf(S': Statement, varLabel: Label): Variable
/////////////////////////// Should add v: Variable to the function and return LHS' * vsSSA.getInstancesOf(v).
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

// Moved to SlideDG.dfy - 28/1/19
/*function allSlidesOf(S: Statement) : set<Slide>
	reads *
	requires Valid(S)
	requires Core(S)
{
	slidesOf(S, def(S))
}

predicate ValidLabel(l: Label, S: Statement)
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
}*/

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
	case Assignment(LHS,RHS) => Assignment([slide.1], [CorrespondingRHS(slide.1, LHS, RHS)])
	case SeqComp(S1,S2) =>		if l[0] == 1 then SeqComp(statementOfSlide(slide, l[1..], S1), Skip)  else SeqComp(Skip, statementOfSlide(slide, l[1..], S2))
	case IF(B0,Sthen,Selse) =>	if l[0] == 1 then IF(B0, statementOfSlide(slide, l[1..], Sthen), Skip) else IF(B0, Skip, statementOfSlide(slide, l[1..], Selse))
	case DO(B,Sloop) =>			DO(B, statementOfSlide(slide, l[1..], Sloop))
	}
}

function CorrespondingRHS(v: Variable, LHS: seq<Variable>, RHS: seq<Expression>): Expression
	requires Valid(Assignment(LHS, RHS))
	requires v in LHS
{
	if LHS[0] == v then RHS[0] else CorrespondingRHS(v, LHS[1..], RHS[1..])
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