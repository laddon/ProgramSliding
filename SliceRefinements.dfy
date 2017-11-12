include "RE.dfy"



//============================================================
//					*** Help ***
//============================================================

predicate Theorem_4_1Help1 (S: Statement,T: Statement)
reads *
requires Valid(S)
requires Valid(T)
{
	(forall P: Predicate, s: State :: wp(S,P).0(s) == wp(T,P).0(s))
}

lemma Theorem_4_1Help1Lemma(S: Statement,T: Statement)
requires Valid(S)
requires Valid(T)
ensures Theorem_4_1Help1(S,T) <==> (forall P: Predicate, s: State :: wp(S,P).0(s) == wp(T,P).0(s))


predicate Theorem_4_1Help2 (S: Statement,T: Statement)
reads *
requires Valid(S)
requires Valid(T)
{
	(forall P: Predicate, s:State :: (wp(S,P).0(s) ==> wp(T,P).0(s)) && (EquivalentPredicates(wp(S,ConstantPredicate(true)),wp(T,ConstantPredicate(true)))))
}

lemma Theorem_4_1Help2Lemma(S: Statement,T: Statement)
requires Valid(S)
requires Valid(T)
ensures Theorem_4_1Help2(S,T) <==> (forall P: Predicate, s:State :: (wp(S,P).0(s) ==> wp(T,P).0(s)) && (EquivalentPredicates(wp(S,ConstantPredicate(true)),wp(T,ConstantPredicate(true)))))

predicate Theorem_5_1Help(S: Statement, SV: Statement, V: set<Variable>)
reads *
requires Valid(S)
requires Valid(SV)
{
	(forall s: State :: ((wp(S,ConstantPredicate(true)).0(s) ==> wp(SV,ConstantPredicate(true)).0(s)))) && (forall s: State, v: Variable :: v in V && v in s ==> (wp(S,PointwisePredicate(s,v)).0(s) ==> wp(SV,PointwisePredicate(s,v)).0(s)))
}

lemma Theorem_5_1HelpLemma(S: Statement, SV: Statement, V: set<Variable>)
requires Valid(S)
requires Valid(SV)
ensures Theorem_5_1Help(S,SV,V) <==> (forall s: State :: ((wp(S,ConstantPredicate(true)).0(s) ==> wp(SV,ConstantPredicate(true)).0(s)))) && (forall s: State, v: Variable :: v in V && v in s ==> (wp(S,PointwisePredicate(s,v)).0(s) ==> wp(SV,PointwisePredicate(s,v)).0(s)))

predicate Corollary_5_2Help(S: Statement, SV: Statement, V: set<Variable>)
reads *
requires Valid(S)
requires Valid(SV)
{
	TerminationRefinement(S,SV) && SetPointwiseRefinement(S,SV,def(S)+def(SV)-V)
}

lemma Corollary_5_2HelpLemma(S: Statement, SV: Statement, V: set<Variable>)
requires Valid(S)
requires Valid(SV)
ensures Corollary_5_2Help(S,SV,V) <==> (((forall s: State :: ((wp(S,ConstantPredicate(true)).0(s) ==> wp(SV,ConstantPredicate(true)).0(s)))) && (forall s: State, v: Variable :: v in (def(S)+def(SV)-V) && v in s ==> (wp(S,PointwisePredicate(s,v)).0(s) ==> wp(SV,PointwisePredicate(s,v)).0(s)))))

predicate Corollary_5_4Help1(S: Statement, SV: Statement, V: set<Variable>)
reads *
requires Valid(S)
requires Valid(SV)
{
	TerminationRefinement(S,SV) && SetPointwiseRefinement(S,SV,V+def(S)+def(SV))
}

lemma Corollary_5_4Help1Lemma(S: Statement, SV: Statement, V: set<Variable>)
requires Valid(S)
requires Valid(SV)
ensures Corollary_5_4Help1(S,SV,V) <==> (forall s: State :: ((wp(S,ConstantPredicate(true)).0(s) ==> wp(SV,ConstantPredicate(true)).0(s)))) && (forall s: State ,v: Variable :: v in (V+def(S)+def(SV)) && v in s  ==> (wp(S,PointwisePredicate(s,v)).0(s) ==> wp(SV,PointwisePredicate(s,v)).0(s)))

lemma Corollary_5_2HelpToCorollary_5_4Help1Lemma(S: Statement, SV: Statement, V: set<Variable>)
requires Valid(S)
requires Valid(SV)
// one can freely add here (to the set of all defined variables) the remaining (hence non-defined) elements of V
ensures Corollary_5_2Help(S,SV,{}) ==  Corollary_5_4Help1(S,SV,V)
{
	var T := TerminationRefinement(S,SV);
	var nonDefV := SetPointwiseRefinement(S,SV,V-(def(S)+def(SV)));
	var allDefs := SetPointwiseRefinement(S,SV,def(S)+def(SV));
	
	calc {
	Corollary_5_2Help(S,SV,{});
	==
	T && SetPointwiseRefinement(S,SV,def(S)+def(SV)-{});
	==
	T && allDefs;
	== {	assert T == (T && nonDefV) by { 
				forall P | vars(P) !! def(S)+def(SV) ensures T ==> (forall s:State :: (wp(S,P)).0(s) ==> (wp(SV,P)).0(s)) { calc {
					T;
				==
					TerminationRefinement(S,SV);
				==> { Corollary_5_5(S,SV,P); }
					(forall s:State :: (wp(S,P)).0(s) ==> (wp(SV,P)).0(s));
				} }
				assert T ==> SetPointwiseRefinement(S,SV,V-(def(S)+def(SV)));
				assert T ==> nonDefV;
			}
		}
	T && nonDefV && allDefs;
	== { assert nonDefV && allDefs <==> SetPointwiseRefinement(S,SV,V+def(S)+def(SV));
			assert T && SetPointwiseRefinement(S,SV,V+def(S)+def(SV)) <==> Corollary_5_4Help1(S,SV,V); }
	Corollary_5_4Help1(S,SV,V);
	}
}

lemma Corollary_5_4Help1ToHelp2Lemma(S: Statement, SV: Statement, V: set<Variable>)
requires Valid(S)
requires Valid(SV)
ensures Corollary_5_4Help1(S,SV,V) <==> Corollary_5_4Help2(S,SV,V)
{
	calc {
		Corollary_5_4Help1(S,SV,V);
		== {Corollary_5_4Help1Lemma(S,SV,V);}
		(forall s: State :: ((wp(S,ConstantPredicate(true)).0(s) ==> wp(SV,ConstantPredicate(true)).0(s)))) && (forall s: State ,v: Variable :: v in (V+def(S)+def(SV)) && v in s  ==> (wp(S,PointwisePredicate(s,v)).0(s) ==> wp(SV,PointwisePredicate(s,v)).0(s)));
		== {}
		(forall s: State :: ((wp(S,ConstantPredicate(true)).0(s) ==> wp(SV,ConstantPredicate(true)).0(s)))) && (forall s: State ,v: Variable :: (v in (V) || v in (def(S)+def(SV)-V)) && v in s  ==> (wp(S,PointwisePredicate(s,v)).0(s) ==> wp(SV,PointwisePredicate(s,v)).0(s)));
		== {Corollary_5_4Help1ToHelp2LemmaHelpLemma(S,SV,V);}
		Corollary_5_4Help1ToHelp2LemmaHelp(S,SV,V);
		== {Corollary_5_4Help1ToHelp2LemmaHelpToHelp2(S,SV,V);}
		Corollary_5_4Help2(S,SV,V);
	}

}

// The following predicates and Lemmas are for proving Corollary_5_4Help1ToHelp2LemmaHelpToHelp2
predicate Corollary_5_4Help1ToHelp2LemmaHelp(S: Statement, SV: Statement, V: set<Variable>)
reads *
requires Valid(S)
requires Valid(SV)
{
	(forall s: State :: ((wp(S,ConstantPredicate(true)).0(s) ==> wp(SV,ConstantPredicate(true)).0(s)))) && (forall s: State ,v: Variable :: (v in (V) || v in (def(S)+def(SV)-V)) && v in s  ==> (wp(S,PointwisePredicate(s,v)).0(s) ==> wp(SV,PointwisePredicate(s,v)).0(s)))
}

predicate SideA(S: Statement, SV: Statement, V: set<Variable>)
reads *
requires Valid(S)
requires Valid(SV)
{
	(forall s: State :: ((wp(S,ConstantPredicate(true)).0(s) ==> wp(SV,ConstantPredicate(true)).0(s))))
}

predicate SideB1(S: Statement, SV: Statement, V: set<Variable>)
reads *
requires Valid(S)
requires Valid(SV)
{
	(forall s: State ,v: Variable :: (v in (V) || v in (def(S)+def(SV)-V)) && v in s  ==> (wp(S,PointwisePredicate(s,v)).0(s) ==> wp(SV,PointwisePredicate(s,v)).0(s)))
}

predicate SideB2(S: Statement, SV: Statement, V: set<Variable>)
reads *
requires Valid(S)
requires Valid(SV)
{
	(forall s: State ,v: Variable :: v in (V) && v in s ==> (wp(S,PointwisePredicate(s,v)).0(s) ==> wp(SV,PointwisePredicate(s,v)).0(s))) && (forall s: State ,v: Variable :: v in ((def(S)+def(SV))-V) && v in s  ==> (wp(S,PointwisePredicate(s,v)).0(s) ==> wp(SV,PointwisePredicate(s,v)).0(s)))
}

lemma Corollary_5_4Help1ToHelp2LemmaHelpLemma(S: Statement, SV: Statement, V: set<Variable>)
requires Valid(S)
requires Valid(SV)
ensures Corollary_5_4Help1ToHelp2LemmaHelp(S,SV,V) <==> (forall s: State :: ((wp(S,ConstantPredicate(true)).0(s) ==> wp(SV,ConstantPredicate(true)).0(s)))) && (forall s: State ,v: Variable :: (v in (V) || v in (def(S)+def(SV)-V)) && v in s  ==> (wp(S,PointwisePredicate(s,v)).0(s) ==> wp(SV,PointwisePredicate(s,v)).0(s)))

lemma SideALemma(S: Statement, SV: Statement, V: set<Variable>)
requires Valid(S)
requires Valid(SV)
ensures SideA(S,SV,V) <==> (forall s: State :: ((wp(S,ConstantPredicate(true)).0(s) ==> wp(SV,ConstantPredicate(true)).0(s))))

lemma SideB1Lemma(S: Statement, SV: Statement, V: set<Variable>)
requires Valid(S)
requires Valid(SV)
ensures SideB1(S,SV,V) <==> (forall s: State ,v: Variable :: (v in (V) || v in (def(S)+def(SV)-V)) && v in s  ==> (wp(S,PointwisePredicate(s,v)).0(s) ==> wp(SV,PointwisePredicate(s,v)).0(s)))

lemma SideB2Lemma(S: Statement, SV: Statement, V: set<Variable>)
requires Valid(S)
requires Valid(SV)
ensures SideB2(S,SV,V) <==> (forall s: State ,v: Variable :: v in (V) && v in s ==> (wp(S,PointwisePredicate(s,v)).0(s) ==> wp(SV,PointwisePredicate(s,v)).0(s))) && (forall s: State ,v: Variable :: v in ((def(S)+def(SV))-V) && v in s  ==> (wp(S,PointwisePredicate(s,v)).0(s) ==> wp(SV,PointwisePredicate(s,v)).0(s)))

lemma SideB1SideB2Lemma(S: Statement, SV: Statement, V: set<Variable>)
requires Valid(S)
requires Valid(SV)
ensures SideB1(S,SV,V) <==> SideB2(S,SV,V)
{
	calc {
		SideB1(S,SV,V);
		=={}
		(forall s: State ,v: Variable :: (v in V || v in ((def(S)+def(SV))-V)) && v in s  ==> (wp(S,PointwisePredicate(s,v)).0(s) ==> wp(SV,PointwisePredicate(s,v)).0(s)));
		=={SideB2Lemma(S,SV,V);}
		/*(forall s: State ,v: Variable :: v in V && v in s ==> (wp(S,PointwisePredicate(s,v)).0(s) ==> wp(SV,PointwisePredicate(s,v)).0(s))) && (forall s: State ,v: Variable :: v in ((def(S)+def(SV))-V)  ==> (wp(S,PointwisePredicate(s,v)).0(s) ==> wp(SV,PointwisePredicate(s,v)).0(s)));
		=={}*/
		SideB2(S,SV,V);
	}
}

lemma Corollary_5_4Help1ToHelp2LemmaHelpToHelp2(S: Statement, SV: Statement, V: set<Variable>)
requires Valid(S)
requires Valid(SV)
ensures Corollary_5_4Help1ToHelp2LemmaHelp(S,SV,V) <==> Corollary_5_4Help2(S,SV,V)
{
	calc {
		Corollary_5_4Help1ToHelp2LemmaHelp(S,SV,V);
		== {} 
		SideA(S,SV,V) && SideB1(S,SV,V);
		== {SideB1SideB2Lemma(S,SV,V);}
		SideA(S,SV,V) && SideB2(S,SV,V);
		== {}
		Corollary_5_4Help2(S,SV,V);
	}
}

predicate Corollary_5_4Help2(S: Statement, SV: Statement, V: set<Variable>)
reads *
requires Valid(S)
requires Valid(SV)
{
	(forall s: State :: ((wp(S,ConstantPredicate(true)).0(s) ==> wp(SV,ConstantPredicate(true)).0(s)))) && (forall s: State ,v: Variable :: v in (V) && v in s ==> (wp(S,PointwisePredicate(s,v)).0(s) ==> wp(SV,PointwisePredicate(s,v)).0(s))) && (forall s: State ,v: Variable :: v in ((def(S)+def(SV))-V) && v in s ==> (wp(S,PointwisePredicate(s,v)).0(s) ==> wp(SV,PointwisePredicate(s,v)).0(s)))
}

lemma Corollary_5_4Help2Lemma(S: Statement, SV: Statement, V: set<Variable>)
requires Valid(S)
requires Valid(SV)
ensures Corollary_5_4Help2(S,SV,V) <==> (forall s: State :: ((wp(S,ConstantPredicate(true)).0(s) ==> wp(SV,ConstantPredicate(true)).0(s)))) && (forall s: State ,v: Variable :: v in (V) && v in s ==> (wp(S,PointwisePredicate(s,v)).0(s) ==> wp(SV,PointwisePredicate(s,v)).0(s))) && (forall s: State ,v: Variable :: v in ((def(S)+def(SV))-V) && v in s ==> (wp(S,PointwisePredicate(s,v)).0(s) ==> wp(SV,PointwisePredicate(s,v)).0(s)))

lemma Corollary_5_4Help2ToHelp3ANDHelp4Lemma(S: Statement, SV: Statement, V: set<Variable>,CoV: set<Variable>)
requires Valid(S)
requires Valid(SV)
requires CoV == (def(S) + def(SV)) - V
ensures Corollary_5_4Help2(S,SV,V) <==> Corollary_5_4Help3(S,SV,V,CoV) && Corollary_5_4Help4(S,SV,V,CoV)
{
	calc {
		Corollary_5_4Help2(S,SV,V);
		=={Corollary_5_4Help2Lemma(S,SV,V);}
		(forall s: State :: ((wp(S,ConstantPredicate(true)).0(s) ==> wp(SV,ConstantPredicate(true)).0(s)))) && (forall s: State ,v: Variable :: v in (V) && v in s ==> (wp(S,PointwisePredicate(s,v)).0(s) ==> wp(SV,PointwisePredicate(s,v)).0(s))) && (forall s: State ,v: Variable :: v in ((def(S)+def(SV))-V) && v in s  ==> (wp(S,PointwisePredicate(s,v)).0(s) ==> wp(SV,PointwisePredicate(s,v)).0(s)));
		== {}
		(forall s: State :: ((wp(S,ConstantPredicate(true)).0(s) ==> wp(SV,ConstantPredicate(true)).0(s)))) && (forall s: State :: ((wp(S,ConstantPredicate(true)).0(s) ==> wp(SV,ConstantPredicate(true)).0(s)))) && (forall s: State ,v: Variable :: v in (V) && v in s ==> (wp(S,PointwisePredicate(s,v)).0(s) ==> wp(SV,PointwisePredicate(s,v)).0(s))) && (forall s: State ,v: Variable :: v in ((def(S)+def(SV))-V) && v in s  ==> (wp(S,PointwisePredicate(s,v)).0(s) ==> wp(SV,PointwisePredicate(s,v)).0(s)));
		== {Corollary_5_4Help3Lemma(S,SV,V,CoV);}
		Corollary_5_4Help3(S,SV,V,CoV) && (forall s: State :: ((wp(S,ConstantPredicate(true)).0(s) ==> wp(SV,ConstantPredicate(true)).0(s)))) && (forall s: State ,v: Variable :: v in ((def(S)+def(SV))-V) && v in s  ==> (wp(S,PointwisePredicate(s,v)).0(s) ==> wp(SV,PointwisePredicate(s,v)).0(s)));
		== {assert CoV == (def(S) + def(SV)) - V;}
		Corollary_5_4Help3(S,SV,V,CoV) && (forall s: State :: ((wp(S,ConstantPredicate(true)).0(s) ==> wp(SV,ConstantPredicate(true)).0(s)))) && (forall s: State ,v: Variable :: v in (CoV) && v in s ==> (wp(S,PointwisePredicate(s,v)).0(s) ==> wp(SV,PointwisePredicate(s,v)).0(s)));
		//					  (forall s: State :: ((wp(S,ConstantPredicate(true)).0(s) ==> wp(SV,ConstantPredicate(true)).0(s)))) && (forall s: State ,v: Variable :: v in (CoV) && v in s ==> (wp(S,PointwisePredicate(s,v)).0(s) ==> wp(SV,PointwisePredicate(s,v)).0(s)))
		== {Corollary_5_4Help4Lemma(S,SV,V,CoV);}
		Corollary_5_4Help3(S,SV,V,CoV) && Corollary_5_4Help4(S,SV,V,CoV);
	}
}

predicate Corollary_5_4Help3(S: Statement, SV: Statement, V: set<Variable>,CoV: set<Variable>)
reads *
requires Valid(S)
requires Valid(SV)
requires CoV == (def(S) + def(SV)) - V
{
	(forall s: State :: ((wp(S,ConstantPredicate(true)).0(s) ==> wp(SV,ConstantPredicate(true)).0(s)))) && (forall s: State ,v: Variable :: v in (V) && v in s ==> (wp(S,PointwisePredicate(s,v)).0(s) ==> wp(SV,PointwisePredicate(s,v)).0(s)))
}

predicate Corollary_5_4Help4(S: Statement, SV: Statement, V: set<Variable>,CoV: set<Variable>)
reads *
requires Valid(S)
requires Valid(SV)
requires CoV == (def(S) + def(SV)) - V
{
	(forall s: State :: ((wp(S,ConstantPredicate(true)).0(s) ==> wp(SV,ConstantPredicate(true)).0(s)))) && (forall s: State ,v: Variable :: v in (CoV) && v in s ==> (wp(S,PointwisePredicate(s,v)).0(s) ==> wp(SV,PointwisePredicate(s,v)).0(s)))
}

lemma Corollary_5_4Help3Lemma(S: Statement, SV: Statement, V: set<Variable>,CoV: set<Variable>)
requires Valid(S)
requires Valid(SV)
requires CoV == (def(S) + def(SV)) - V
ensures Corollary_5_4Help3(S,SV,V,CoV) <==> (forall s: State :: ((wp(S,ConstantPredicate(true)).0(s) ==> wp(SV,ConstantPredicate(true)).0(s)))) && (forall s: State ,v: Variable :: v in (V) && v in s ==> (wp(S,PointwisePredicate(s,v)).0(s) ==> wp(SV,PointwisePredicate(s,v)).0(s)))

lemma Corollary_5_4Help4Lemma(S: Statement, SV: Statement, V: set<Variable>,CoV: set<Variable>)
requires Valid(S)
requires Valid(SV)
requires CoV == (def(S) + def(SV)) - V
ensures Corollary_5_4Help4(S,SV,V,CoV) <==> (forall s: State :: ((wp(S,ConstantPredicate(true)).0(s) ==> wp(SV,ConstantPredicate(true)).0(s)))) && (forall s: State ,v: Variable :: v in (CoV) && v in s ==> (wp(S,PointwisePredicate(s,v)).0(s) ==> wp(SV,PointwisePredicate(s,v)).0(s)))

lemma Corollary_5_4Help4ToCoSliceRefinementLemma(S: Statement, SV: Statement, V: set<Variable>,CoV: set<Variable>)
requires Valid(S)
requires Valid(SV)
requires CoV == (def(S)+def(SV))-V
ensures CoSliceRefinement(S,SV,V) <==> Corollary_5_4Help4(S,SV,V,CoV)
{
	calc {
		Corollary_5_4Help4(S,SV,V,CoV);
		== {Corollary_5_4Help4Lemma(S,SV,V,CoV);}
		(forall s: State :: ((wp(S,ConstantPredicate(true)).0(s) ==> wp(SV,ConstantPredicate(true)).0(s)))) && (forall s: State ,v: Variable :: v in (CoV) && v in s ==> (wp(S,PointwisePredicate(s,v)).0(s) ==> wp(SV,PointwisePredicate(s,v)).0(s)));
		== {assert CoV == (def(S)+def(SV)-V);}
		(forall s: State :: ((wp(S,ConstantPredicate(true)).0(s) ==> wp(SV,ConstantPredicate(true)).0(s)))) && (forall s: State ,v: Variable :: v in (def(S)+def(SV)-V) && v in s ==> (wp(S,PointwisePredicate(s,v)).0(s) ==> wp(SV,PointwisePredicate(s,v)).0(s)));
		== {Corollary_5_2HelpLemma(S,SV,V);}
		Corollary_5_2Help(S,SV,V);
		== {Corollary_5_2(S,SV,V);}
		CoSliceRefinement(S,SV,V);
	}
}

lemma Corollary_5_4Help3ToSliceRefinementLemma(S: Statement, SV: Statement, V: set<Variable>,CoV: set<Variable>)
requires Valid(S)
requires Valid(SV)
requires CoV == (def(S)+def(SV))-V
ensures SliceRefinement(S,SV,V) <==> Corollary_5_4Help3(S,SV,V,CoV)
{
	calc {
		Corollary_5_4Help3(S,SV,V,CoV);
		=={Corollary_5_4Help3Lemma(S,SV,V,CoV);}
		(forall s: State :: ((wp(S,ConstantPredicate(true)).0(s) ==> wp(SV,ConstantPredicate(true)).0(s)))) && (forall s: State ,v: Variable :: v in (V) && v in s ==> (wp(S,PointwisePredicate(s,v)).0(s) ==> wp(SV,PointwisePredicate(s,v)).0(s)));
		== {}
		(forall s: State :: ((wp(S,ConstantPredicate(true)).0(s) ==> wp(SV,ConstantPredicate(true)).0(s)))) && (forall s: State ,v: Variable :: v in (V) && v in s ==> (wp(S,PointwisePredicate(s,v)).0(s) ==> wp(SV,PointwisePredicate(s,v)).0(s)));
	//	(forall s: State :: ((wp(S,ConstantPredicate(true)).0(s) ==> wp(SV,ConstantPredicate(true)).0(s)))) && (forall s: State, v: Variable :: v in V && v in s ==> (wp(S,PointwisePredicate(s,v)).0(s) ==> wp(SV,PointwisePredicate(s,v)).0(s)))	
		== {Theorem_5_1HelpLemma(S,SV,V);}
		Theorem_5_1Help(S,SV,V);
		=={Theorem_5_1(S,SV,V);}
		SliceRefinement(S,SV,V);
	}
}

function P2_x(P:Predicate,S:Statement, V: set<Variable>) : State->Predicate
reads *
requires Valid(S)
{
	(p: State) => (((s0:State)=>(forall v: Variable :: v in V ==> v in s0 && v in p && s0[v] == p[v])),P.1)
}

function P3_x(s:State,P:Predicate,S:Statement, V: set<Variable>) : Predicate
reads *
requires Valid(S)
{
	(((s1: State) reads * requires P.0.requires(s1)=> exists p: State ::  P.0.requires(p) && P.0(p) &&Valid(S) && P2_x(P,S,V).requires(p) && wp.requires(S,P2_x(P,S,V)(p)) && (wp(S,(P2_x(P,S,V))(p)).0(s1))),P.1)
}

lemma P3P4(s1:State,P:Predicate,S:Statement,SV:Statement, V: set<Variable>)
requires Valid(S)
requires Valid(SV)
requires (forall s: State, v: Variable :: v in V && v in s ==> (wp(S,PointwisePredicate(s,v)).0(s) ==> wp(SV,PointwisePredicate(s,v)).0(s)))
ensures (forall s: State, v: Variable :: v in V && v in s ==> (P3_x(s1,P,S,V).0(s) ==> P3_x(s1,P,SV,V).0(s)))
/*{
	forall s: State, v: Variable | v in V && v in s {
		calc
		 {
			P3_x(s1,P,S,V).0(s);
			==>{}
			(((s1: State) reads * requires P.0.requires(s1)=> exists p: State ::  P.0.requires(p) && P.0(p) && Valid(S) && P2_x(P,S,V).requires(p) && wp.requires(S,P2_x(P,S,V)(p)) && (wp(S,(P2_x(P,S,V))(p)).0(s1))),P.1).0(s);
			==>{assert (wp(S,PointwisePredicate(s,v)).0(s) ==> wp(SV,PointwisePredicate(s,v)).0(s));}
			(((s1: State) reads * requires P.0.requires(s1)=> exists p: State ::  P.0.requires(p) && P.0(p) && Valid(SV) &&P2_x(P,SV,V).requires(p) && wp.requires(SV,P2_x(P,SV,V)(p)) && (wp(SV,(P2_x(P,SV,V))(p)).0(s1))),P.1).0(s);
			== {}
			P3_x(s1,P,SV,V).0(s);
		 }
	 }
}*/

// All the following lemma's and predicates till Corollary_5_6 are used in order to prove in Dafny that Corollary_5_6 is correct 
predicate Corollary_5_6Help1Single (S: Statement, T: Statement, V: set<Variable>)
reads * 
requires Valid(S)
requires Valid(T)
{
	SliceRefinement(S,T,V)	&& EquivalentPredicates(wp(S,ConstantPredicate(true)),wp(T,ConstantPredicate(true)))
}

predicate Corollary_5_6Help1 (S: Statement, T: Statement, V: set<Variable>)
reads * 
requires Valid(S)
requires Valid(T)
{
	(forall P: Predicate, s: State :: vars(P) <= V ==> wp(S, P).0(s) == wp(T, P).0(s))
}

lemma Corollary_5_6Help1Lemma(S: Statement, T: Statement, V: set<Variable>)
requires Valid(S)
requires Valid(T)
ensures Corollary_5_6Help1(S,T,V) == (forall P: Predicate, s: State :: vars(P) <= V ==> wp(S, P).0(s) == wp(T, P).0(s))  


lemma EquivalentCorollary_5_6Help1SingleLemma(S: Statement, T: Statement, V: set<Variable>)
requires Valid(S)
requires Valid(T)
ensures Corollary_5_6Help1Single(S,T,V) <==> Corollary_5_6Help1(S,T,V) 
{
	calc {
	Corollary_5_6Help1Single(S,T,V);
	=={}
	SliceRefinement(S,T,V)	&& EquivalentPredicates(wp(S,ConstantPredicate(true)),wp(T,ConstantPredicate(true)));
	=={SliceRefinementLemma(S,T,V);}
	((forall P: Predicate, s: State :: vars(P) <= V ==> wp(S, P).0(s) ==> wp(T, P).0(s)) && EquivalentPredicates(wp(S,ConstantPredicate(true)),wp(T,ConstantPredicate(true))));
	=={}
	forall P: Predicate, s: State :: vars(P) <= V ==> ((wp(S, P).0(s) ==> wp(T, P).0(s)) && (EquivalentPredicates(wp(S,ConstantPredicate(true)),wp(T,ConstantPredicate(true)))));
	=={Theorem_4_2inVLemma(S, T,V);}
	(forall P: Predicate, s: State :: vars(P) <= V ==> wp(S, P).0(s) == wp(T, P).0(s));
	== {Corollary_5_6Help1Lemma(S,T,V);}
	Corollary_5_6Help1(S,T,V);
	}
}

predicate Corollary_5_6Help2Single (S: Statement, T: Statement, V: set<Variable>)
reads * 
requires Valid(S)
requires Valid(T)
{
	CoSliceRefinement(S,T,V) && EquivalentPredicates(wp(S,ConstantPredicate(true)),wp(T,ConstantPredicate(true)))
}

predicate Corollary_5_6Help2 (S: Statement, T: Statement, V: set<Variable>)
reads * 
requires Valid(S)
requires Valid(T)
{
	(forall P: Predicate, s: State :: vars(P) !! V ==> wp(S, P).0(s) == wp(T, P).0(s)) 
}

lemma Corollary_5_6Help2Lemma(S: Statement, T: Statement, V: set<Variable>)
requires Valid(S)
requires Valid(T)
ensures Corollary_5_6Help2(S,T,V) == (forall P: Predicate, s: State :: vars(P) !! V ==> wp(S, P).0(s) == wp(T, P).0(s))

lemma EquivalentCorollary_5_6Help2SingleLemma(S: Statement, T: Statement, V: set<Variable>)
requires Valid(S)
requires Valid(T)
ensures Corollary_5_6Help2Single(S,T,V) == Corollary_5_6Help2(S,T,V)
{
	calc {
	Corollary_5_6Help2Single(S,T,V);
	=={}
	CoSliceRefinement(S,T,V)	&& EquivalentPredicates(wp(S,ConstantPredicate(true)),wp(T,ConstantPredicate(true)));
	=={CoSliceRefinementLemma(S,T,V);}
	((forall P: Predicate, s: State :: vars(P) !! V ==> wp(S, P).0(s) ==> wp(T, P).0(s)) && EquivalentPredicates(wp(S,ConstantPredicate(true)),wp(T,ConstantPredicate(true))));
	=={}
	forall P: Predicate, s: State :: vars(P) !! V ==> ((wp(S, P).0(s) ==> wp(T, P).0(s)) && (EquivalentPredicates(wp(S,ConstantPredicate(true)),wp(T,ConstantPredicate(true)))));
	=={Theorem_4_2StrangerVLemma(S, T, V);}
	(forall P: Predicate, s: State :: vars(P) !! V ==> wp(S, P).0(s) == wp(T, P).0(s));
	== {Corollary_5_6Help2Lemma(S,T,V);}
	Corollary_5_6Help2(S,T,V);
	}
}


//============================================================
//					*** THEOREMS ***
//============================================================
lemma Equation_5_1(P: Predicate,V: set<Variable>)
ensures EquivalentPredicates(P,(((s1: State) reads * requires P.0.requires(s1) => exists p: State :: P.0.requires(p) && P.0(p) && forall v: Variable :: v in V ==> v in s1 && v in p && p[v] == s1[v]), P.1))

lemma Equation_5_2(S: Statement, Sco: Statement, V: set<Variable>)
requires Valid(S)
requires Valid(Sco)
ensures (forall s: State, v: Variable :: v in V && v in s ==> (wp(S,PointwisePredicate(s,v)).0(s) ==> wp(Sco,PointwisePredicate(s,v)).0(s)))

lemma AbsorptionOfTermination3_14(P: Predicate,S: Statement)
	requires Valid(S)
	ensures EquivalentPredicates(AND(wp(S,P),wp(S,ConstantPredicate(true))) , wp(S,P));
{
	forall s:State {
		calc {
			AND(wp(S,P),wp(S,ConstantPredicate(true))).0(s);
			== {FinitelyConjunctive(S,P,ConstantPredicate(true));}
			wp(S,AND(P,ConstantPredicate(true))).0(s);
			== {IdentityOfAND(S,P);}
			wp(S,P).0(s);
		}	
	}
}

lemma Theorem_4_1(S: Statement, T: Statement) 
requires Valid(S)
requires Valid(T)
ensures (EquivalentStatments(S,T)) <==> ((Refinement(S,T)) && EquivalentPredicates(wp(S,ConstantPredicate(true)),wp(T,ConstantPredicate(true))))
{
	 calc {
		EquivalentStatments(S,T);
		== {EquivalentStatmentsLemma(S,T);}
		(forall P: Predicate ::EquivalentPredicates(wp(S,P), wp(T,P)));
		== {/*def. of program equivalence*/}
		(forall P: Predicate, s: State :: (wp(S,P).0(s) == wp(T,P).0(s)));
		== {Theorem_4_1Help1Lemma(S,T);}
		Theorem_4_1Help1(S,T);
		== {Lemma_4_2(S,T);}
		Theorem_4_1Help2(S,T);
		== {Theorem_4_1Help2Lemma(S,T);}
		(forall P: Predicate, s: State :: (wp(S,P).0(s) ==> wp(T,P).0(s))) && (EquivalentPredicates(wp(S,ConstantPredicate(true)),wp(T,ConstantPredicate(true))));
		== {/*pred. calc. (3.7): the range is non-empty}*/}
		(forall P: Predicate, s: State :: (wp(S,P).0(s) ==> wp(T,P).0(s))) && (EquivalentPredicates(wp(S,ConstantPredicate(true)),wp(T,ConstantPredicate(true))));
		== {RefinementLemma(S,T);}
		(Refinement(S,T)) && (EquivalentPredicates(wp(S,ConstantPredicate(true)),wp(T,ConstantPredicate(true))));
	}
}

lemma Lemma_4_2(S: Statement, T: Statement)
requires Valid(S)
requires Valid(T)
ensures  Theorem_4_1Help1(S,T) <==> Theorem_4_1Help2(S,T)
{
	assert	Theorem_4_1Help1(S,T) <==> (forall P: Predicate, s: State :: wp(S,P).0(s) == wp(T,P).0(s)) by {Theorem_4_1Help1Lemma(S,T);}
	assert	Theorem_4_1Help2(S,T) <==> (forall P: Predicate, s:State :: (wp(S,P).0(s) ==> wp(T,P).0(s)) && (EquivalentPredicates(wp(S,ConstantPredicate(true)),wp(T,ConstantPredicate(true))))) by {Theorem_4_1Help2Lemma(S,T);}
	assert  (forall P: Predicate, s: State :: wp(S,P).0(s) == wp(T,P).0(s)) ==> ((forall P: Predicate, s:State :: (wp(S,P).0(s) ==> wp(T,P).0(s)) && (EquivalentPredicates(wp(S,ConstantPredicate(true)),wp(T,ConstantPredicate(true)))))) by {Lemma_4_2_Left(S,T);}
	assert  (forall P: Predicate, s: State :: wp(S,P).0(s) == wp(T,P).0(s)) <== ((forall P: Predicate, s:State :: (wp(S,P).0(s) ==> wp(T,P).0(s)) && (EquivalentPredicates(wp(S,ConstantPredicate(true)),wp(T,ConstantPredicate(true)))))) by 
	{
		if (((forall P: Predicate, s:State :: (wp(S,P).0(s) ==> wp(T,P).0(s)) && (EquivalentPredicates(wp(S,ConstantPredicate(true)),wp(T,ConstantPredicate(true)))))))
		{
			calc {
			((forall P: Predicate, s:State :: (wp(S,P).0(s) ==> wp(T,P).0(s)) && (EquivalentPredicates(wp(S,ConstantPredicate(true)),wp(T,ConstantPredicate(true))))));
			==> {Lemma_4_2_Right(S,T);}
			(forall P: Predicate, s: State :: wp(S,P).0(s) == wp(T,P).0(s));
			}
		}
	}
	assert Theorem_4_1Help1(S,T) <==> Theorem_4_1Help2(S,T);
}

lemma Lemma_4_2_Left(S: Statement, T: Statement)
requires Valid(S)
requires Valid(T)
ensures  (forall P: Predicate, s: State :: wp(S,P).0(s) == wp(T,P).0(s)) ==> (forall P: Predicate, s:State :: (wp(S,P).0(s) ==> wp(T,P).0(s)) && (EquivalentPredicates(wp(S,ConstantPredicate(true)),wp(T,ConstantPredicate(true)))))
{
	calc 
	{
		(forall P: Predicate, s: State :: wp(S,P).0(s) == wp(T,P).0(s));
		==> {}
		((forall P: Predicate, s:State :: (wp(S,P).0(s) ==> wp(T,P).0(s)) && (EquivalentPredicates(wp(S,ConstantPredicate(true)),wp(T,ConstantPredicate(true))))));
	}
}

lemma Lemma_4_2_Right(S: Statement, T: Statement)
requires Valid(S)
requires Valid(T)
requires forall P: Predicate, s:State :: (wp(S,P).0(s) ==> wp(T,P).0(s)) 
requires EquivalentPredicates(wp(S,ConstantPredicate(true)),wp(T,ConstantPredicate(true)))
ensures  (forall P: Predicate, s: State :: wp(S,P).0(s) == wp(T,P).0(s))
{
	forall s: State, P : Predicate
	{
		calc {
		wp(S,P).0(s);
		== {WP_Definition(S,P);}
		AND(wlp(S,P),wp(S,ConstantPredicate(true))).0(s);
		== {}
		AND(NOT(wp(S,NOT(P))),wp(S,ConstantPredicate(true))).0(s);
		<== {assert (wp(S,P).0(s) ==> wp(T,P).0(s));}
		AND(NOT(wp(T,NOT(P))),wp(S,ConstantPredicate(true))).0(s);
		== {}
		AND(wlp(T,P),wp(S,ConstantPredicate(true))).0(s);
		== {assert EquivalentPredicates(wp(S,ConstantPredicate(true)),wp(T,ConstantPredicate(true)));}
		AND(wlp(T,P),wp(T,ConstantPredicate(true))).0(s);
		== {WP_Definition(T,P);}
		wp(T,P).0(s);
		}
	}
}

lemma Theorem_4_2inVLemma(S: Statement, T: Statement, V: set<Variable>)
requires Valid(S)
requires Valid(T)
ensures (forall P: Predicate, s:State :: vars(P) <= V ==> ((wp(S,P).0(s) ==> wp(T,P).0(s)) && (EquivalentPredicates(wp(S,ConstantPredicate(true)),wp(T,ConstantPredicate(true)))))) <==> (forall P: Predicate, s: State :: wp(S,P).0(s) == wp(T,P).0(s))

lemma Theorem_4_2StrangerVLemma(S: Statement, T: Statement, V: set<Variable>)
requires Valid(S)
requires Valid(T)
ensures (forall P: Predicate, s:State :: vars(P) !! V ==> ((wp(S,P).0(s) ==> wp(T,P).0(s)) && (EquivalentPredicates(wp(S,ConstantPredicate(true)),wp(T,ConstantPredicate(true)))))) <==> (forall P: Predicate, s: State :: wp(S,P).0(s) == wp(T,P).0(s))


lemma Theorem_5_1 (S: Statement, SV: Statement, V: set<Variable>)
requires Valid(S)
requires Valid(SV)
ensures SliceRefinement(S,SV,V) <==> Theorem_5_1Help(S,SV,V)
{
	calc
	{
	SliceRefinement(S,SV,V);
	== {Theorem_5_1Left(S,SV,V); Theorem_5_1Right(S,SV,V);}
	Theorem_5_1Help(S,SV,V);
	}
}

/*TODO: Complete 1-3 error*/
lemma {:verify false} Theorem_5_1Left (S: Statement, SV: Statement, V: set<Variable>)
requires Valid(S)
requires Valid(SV)
ensures SliceRefinement(S,SV,V) ==> Theorem_5_1Help(S,SV,V)
{
	//glob.true = ; and glob.(x = val )  V for all x 2 V of type T ,and value val 2 T .x .
	forall P:Predicate,s: State, v: Variable | v in V && v in s && (vars(P) <= V){
		calc {
		SliceRefinement(S,SV,V);
		==> {SliceRefinementLemma(S,SV,V);}
		((wp(S,P).0(s) ==> wp(SV,P).0(s)));
		// need to define types of Predicate (ConstantPredicate(true) && PointwisePredicate(s,v)) in the group of predicate P
		== {Theorem_5_1HelpLemma(S,SV,V);assert vars(PointwisePredicate(s,v)) <= V;assert vars(ConstantPredicate(true)) <= V by {assert vars(ConstantPredicate(true)) == {};}}
		/*((wp(S,ConstantPredicate(true)).0(s) ==> wp(SV,ConstantPredicate(true)).0(s))) && (wp(S,PointwisePredicate(s,v)).0(s) ==> wp(SV,PointwisePredicate(s,v)).0(s));
		== {Theorem_5_1HelpLemma(S,SV,V);}*/
		Theorem_5_1Help(S,SV,V);

		// vars(ConstantPredicate(true)) == {}
		// vars(PointwisePredicate(s,v)) <= V
		//forall P: Predicate,s: State :: (vars(P) <= V) ==> ((wp(S1,P).0(s) ==> wp(S2,P).0(s)))
		//(forall s: State :: ((wp(S,ConstantPredicate(true)).0(s) ==> wp(SV,ConstantPredicate(true)).0(s)))) && (forall s: State, v: Variable :: v in V && v in s ==> (wp(S,PointwisePredicate(s,v)).0(s) ==> wp(SV,PointwisePredicate(s,v)).0(s)))
		}
	}
}

/*TODO : Complete 2 err*/
/*break into V is empty and V isnot empty */
/*add EMPTY type to V in order to use match+case */
lemma Theorem_5_1Right (S: Statement, SV: Statement, V: set<Variable>)
requires Valid(S)
requires Valid(SV)
ensures SliceRefinement(S,SV,V) <== Theorem_5_1Help(S,SV,V)
{
	/*match V {
		case EMPTY => true
		case set<Variable> => { 
		*/
	forall P: Predicate ,s: State |(vars(P) <= V) ensures wp(S,P).0(s) ==> wp(SV,P).0(s);
	{			
		var P1 := (((s1: State) reads * requires P.0.requires(s1) => exists p: State :: P.0.requires(p) && P.0(p) && forall v: Variable :: v in V ==> v in s1 && v in p && p[v] == s1[v]), P.1);
		var P2 := (p: State) => (((s0:State)=>(forall v: Variable :: v in V ==> v in s0 && v in p && s0[v] == p[v])),P.1);
		var P3 := (((s1: State) reads * requires P.0.requires(s1)=> exists p: State :: P.0.requires(p) && P.0(p) && wp.requires(S,P2(p)) && (wp(S,P2(p)).0(s1))),P.1);
		var P4 := (((s2: State) reads * requires P.0.requires(s2)=> exists p1: State :: P.0.requires(p1) && P.0(p1) && wp.requires(SV,P2(p1)) && (wp(SV,P2(p1)).0(s2))),P.1);
		calc{
		wp(S,P).0(s);
		==> {Equation_5_1(P,V);assert EquivalentPredicates(P,P1);Leibniz2(wp,P,P1,S);}
		wp(S,P1).0(s);
		==> {}
		wp(S,(((s1: State) reads * requires P.0.requires(s1) => exists p: State :: P.0.requires(p) && P.0(p) && forall v: Variable :: v in V ==> v in s1 && v in p && p[v] == s1[v]), P.1)).0(s);
		==> {assert forall s1: State, p: State :: (forall v: Variable :: v in V ==> v in s1 && v in p && p[v] == s1[v]) == (P2(p).0(s1));
			var P4 := (((s1: State) reads * requires P.0.requires(s1) => exists p: State :: P.0.requires(p) && P.0(p) && forall v: Variable :: v in V ==> v in s1 && v in p && p[v] == s1[v]), P.1); 
			var P5 := (((s1: State) reads * requires P.0.requires(s1) => exists p: State :: P.0.requires(p) && P.0(p) && P2(p).0(s1)), P.1);
			assert EquivalentPredicates(P4,P5);
			Leibniz2(wp, P4,P5, S);}
		wp(S,(((s1: State) reads * requires P.0.requires(s1) => exists p: State :: P.0.requires(p) && P.0(p) && P2(p).0(s1)), P.1)).0(s);
		==> { assume EquivalentPredicates(wp(S,(((s1: State) reads * requires P.0.requires(s1) => exists p: State :: P.0.requires(p) && P.0(p) && P2(p).0(s1)), P.1)),P3) /*by { RE1(S,{P/*2(p)*/});}*/;} 
		//(((s1: State) reads * requires P.0.requires(s1) => exists p: State :: P.0.requires(p) && P.0(p) && wp.requires(S,P2(p)) && (wp(S,P2(p)).0(s1))), P.1).0(s);
		//=={}                                                                                              
		P3_x(s,P,S,V).0(s);
		==> {assume P3_x(s,P,S,V).0(s) ==> P3_x(s,P,SV,V).0(s);}
		/*==> {/*assume EquivalentPredicates(wp(S,(((s1: State) reads * requires P.0.requires(s1) => exists p: State :: P.0.requires(p) && P.0(p) && P2(p).0(s1)), P.1)),P3);*/}
		((s1: State) reads * requires P.0.requires(s1)=>exists p: State :: P.0.requires(p) && P.0(p) && wp.requires(S,P2(p)) && wp(S,((s0:State)=>(forall v: Variable :: v in V ==> v in s0 && v in p && s0[v] == p[v]),P.1)).0(s1),P.1).0(s);
		//==> {Equation_5_2(S,SV,V);P3P4(s,P,S,SV,V);/*assert exists p: State::(((wp(S,P2(p)).0(s))) ==> (wp(SV,P2(p)).0(s))) by {Equation_5_2(S,SV,V);}/*leibniz3 - forall ==>*/*/}*/
		P3_x(s,P,SV,V).0(s);
		==> {assume EquivalentPredicates(wp(SV,(((s1: State) reads * requires P.0.requires(s1) => exists p: State :: P.0.requires(p) && P.0(p) && P2(p).0(s1)), P.1)),P4) /*by { RE1(S,{P/*2(p)*/});}*/;} 
		wp(SV,(((s1: State) reads * requires P.0.requires(s1) => exists p: State :: P.0.requires(p) && P.0(p) && P2(p).0(s1)), P.1)).0(s);
		==> {assert forall s1: State, p: State :: (forall v: Variable :: v in V ==> v in s1 && v in p && p[v] == s1[v]) == (P2(p).0(s1));
			var P6 := (((s1: State) reads * requires P.0.requires(s1) => exists p: State :: P.0.requires(p) && P.0(p) && forall v: Variable :: v in V ==> v in s1 && v in p && p[v] == s1[v]), P.1); 
			var P7 := (((s1: State) reads * requires P.0.requires(s1) => exists p: State :: P.0.requires(p) && P.0(p) && P2(p).0(s1)), P.1);
			assert EquivalentPredicates(P6,P7);
			Leibniz2(wp, P6,P7, SV);}
		wp(SV,(((s1: State) reads * requires P.0.requires(s1) => exists p: State :: P.0.requires(p) && P.0(p) && forall v: Variable :: v in V ==> v in s1 && v in p && p[v] == s1[v]), P.1)).0(s);
		==> {}
		wp(SV,P1).0(s);
		==> {Equation_5_1(P,V);assert EquivalentPredicates(P,P1);Leibniz2(wp,P,P1,SV);}
		wp(SV,P).0(s);
		}
		assert wp(S,P).0(s) ==> wp(SV,P).0(s);
	}	/*}
	}*/
}


lemma Corollary_5_2 (S: Statement, SV: Statement, V: set<Variable>)
requires Valid(S)
requires Valid(SV)
ensures (CoSliceRefinement(S,SV,V)) <==> Corollary_5_2Help(S,SV,V)
{
	calc {
	CoSliceRefinement(S,SV,V);
	== {Corollary_5_3(S,SV,V,(def(S) + def(SV)) - V);}
	SliceRefinement(S,SV,(def(S) + def(SV)) - V);
	== {Theorem_5_1(S,SV,(def(S) + def(SV)) - V);Theorem_5_1HelpLemma(S,SV,(def(S) + def(SV)) - V);}
	((forall s:State :: ((wp(S,ConstantPredicate(true)).0(s) ==> wp(SV,ConstantPredicate(true)).0(s)))) && (forall s: State, v: Variable :: v in (def(S)+def(SV)-V) && v in s ==> (wp(S,PointwisePredicate(s,v)).0(s) ==> wp(SV,PointwisePredicate(s,v)).0(s))));
	== {Corollary_5_2HelpLemma(S,SV,V);}
	Corollary_5_2Help(S,SV,V);
	}
}

lemma Corollary_5_3 (S: Statement, SV: Statement, V: set<Variable>, CoV: set<Variable>)
requires Valid(S)
requires Valid(SV)
requires CoV == (def(S) + def(SV)) - V
ensures CoSliceRefinement(S,SV,V) == SliceRefinement(S,SV,CoV)
{
	calc
	{
	CoSliceRefinement(S,SV,V);
	== {Corollary_5_3Left(S,SV,V,CoV); Corollary_5_3Right(S,SV,V,CoV);}
	SliceRefinement(S,SV,CoV);
	}
}

lemma Corollary_5_3Left (S: Statement, SV: Statement, V: set<Variable>, CoV: set<Variable>)
requires Valid(S)
requires Valid(SV)
requires CoV == (def(S) + def(SV)) - V
ensures CoSliceRefinement(S,SV,V) ==> SliceRefinement(S,SV,CoV)
{
	calc{
		CoSliceRefinement(S,SV,V);
		==>  {}
		SliceRefinement(S,SV,CoV);
		}
}

/*TODO: Complete */
lemma {:verify false} Corollary_5_3Right (S: Statement, SV: Statement, V: set<Variable>, CoV: set<Variable>)
requires Valid(S)
requires Valid(SV)
requires CoV == (def(S) + def(SV)) - V
ensures CoSliceRefinement(S,SV,V) <== SliceRefinement(S,SV,CoV)
{
	forall s: State, P: Predicate{
		var CoV1 := vars(P) * CoV;
		var ND := vars(P) - CoV;
		var n1 := |CoV1|;
		var n2 := |vars(P)|;

		//var NDP := (s0: State) => (forall v:Variable:: v in ND ==> PointwisePredicate(s0,v).0(s0));

		var P1 := ((s0:State) reads * =>(exists p: State ::  P.0.requires(p) && P.0(p) && (forall v: Variable :: v in CoV1 ==> v in s0 && v in p && s0[v] == p[v]) && (forall v: Variable :: v in ND ==> v in s0 && v in p && s0[v] == p[v])),P.1);
		var P2 := ((s0:State) reads * =>(exists p: State ::  P.0.requires(p) && P.0(p) && wp.requires(S,(p => (forall v: Variable :: v in CoV1 ==> v in s0 && v in p && s0[v] == p[v]),P.1)) && wp(S,(p => (forall v: Variable :: v in CoV1 ==> v in s0 && v in p && s0[v] == p[v]),P.1)).0(s0) && wp(S,(p => (forall v: Variable :: v in ND ==> v in s0 && v in p && s0[v] == p[v]),P.1)).0(s0)),P.1);
		var P3 := ((s0:State) reads * =>(exists p: State ::  P.0.requires(p) && P.0(p) && wp.requires(S,(p => (forall v: Variable :: v in CoV1 ==> v in s0 && v in p && s0[v] == p[v]),P.1)) && wp(S,(p => (forall v: Variable :: v in CoV1 ==> v in s0 && v in p && s0[v] == p[v]),P.1)).0(s0) && AND((p => (forall v: Variable :: v in ND ==> v in s0 && v in p && s0[v] == p[v]),P.1),wp(S,ConstantPredicate(true))).0(s0)),P.1);
		var P4 := ((s0:State) reads * =>(exists p: State ::  P.0.requires(p) && P.0(p) && wp.requires(SV,(p => (forall v: Variable :: v in CoV1 ==> v in s0 && v in p && s0[v] == p[v]),P.1)) && wp(SV,(p => (forall v: Variable :: v in CoV1 ==> v in s0 && v in p && s0[v] == p[v]),P.1)).0(s0) && AND((p => (forall v: Variable :: v in ND ==> v in s0 && v in p && s0[v] == p[v]),P.1),wp(S,ConstantPredicate(true))).0(s0)),P.1);
		var P5 := ((s0:State) reads * =>(exists p: State ::  P.0.requires(p) && P.0(p) && wp.requires(SV,(p => (forall v: Variable :: v in CoV1 ==> v in s0 && v in p && s0[v] == p[v]),P.1)) && wp(SV,(p => (forall v: Variable :: v in CoV1 ==> v in s0 && v in p && s0[v] == p[v]),P.1)).0(s0) && AND((p => (forall v: Variable :: v in ND ==> v in s0 && v in p && s0[v] == p[v]),P.1),wp(SV,ConstantPredicate(true))).0(s0)),P.1);
		var P6 := ((s0:State) reads * =>(exists p: State ::  P.0.requires(p) && P.0(p) && wp.requires(SV,(p => (forall v: Variable :: v in CoV1 ==> v in s0 && v in p && s0[v] == p[v]),P.1)) && wp(SV,(p => (forall v: Variable :: v in CoV1 ==> v in s0 && v in p && s0[v] == p[v]),P.1)).0(s0) && wp(SV,(p => (forall v: Variable :: v in ND ==> v in s0 && v in p && s0[v] == p[v]),P.1)).0(s0)),P.1);
		
		if (!((vars(P) !! V) && (vars(P) - CoV != {})))
		{}
		else{
			calc {
				wp(S,P).0(s);
				== {assume EquivalentPredicates(P,P1);Leibniz2(wp,P,P1,S);}
				wp(S,P1).0(s);
				==>{assume EquivalentPredicates(wp(S,P1),P2);}
				P2.0(s);
				=={var PP := ((s0:State) reads * =>(exists p: State :: (forall v: Variable :: v in ND ==> v in s0 && v in p && s0[v] == p[v])),ND); assert vars(wp(S,PP)) <= vars(PP) - ddef(S) + input(S) by {RE2(S,PP);}assert vars(PP) !! def(S); RE3(S,PP);assert EquivalentPredicates(AND(PP,wp(S,ConstantPredicate(true))),wp(S,PP));assert EquivalentPredicates(P2,P3);}
				P3.0(s);
				=={assert CoV1 <= CoV;}
				P4.0(s);
				=={assert CoV1 <= CoV;}
				P5.0(s);
				== {var PP := wp(SV,((s0:State) reads * =>(exists p: State :: (forall v: Variable :: v in ND ==> v in s0 && v in p && s0[v] == p[v])),P.1)); assert vars(wp(SV,P2)) <= vars(P2) - ddef(SV) + input(SV) by {RE2(SV,P2);}assert ND !! def(SV); RE3(S,PP);assert EquivalentPredicates(P2,P3);}
				P6.0(s);
				== {assume EquivalentPredicates(wp(SV,P1),P6);}
				wp(SV,P1).0(s);
				== {assume EquivalentPredicates(P,P1);Leibniz2(wp,P,P1,SV);}
				wp(SV,P).0(s);
			}
		}
	}
}


lemma Corollary_5_4 (S: Statement, T: Statement, V: set<Variable>)
requires Valid(S)
requires Valid(T)
ensures Refinement(S,T) <==> SliceRefinement(S,T,V) && CoSliceRefinement(S,T,V)
{
		calc {
		Refinement(S,T);
		== {RefinementLemma(S,T);}
		(forall P: Predicate, s: State ::(wp(S,P).0(s) ==> wp(T,P).0(s)));
		== {/*def. of refinement; glob.P  ; holds for all P*/}
		(forall P: Predicate, s: State :: (vars(P) !! {}) ==> (wp(S,P).0(s) ==> wp(T,P).0(s)));
		== {CoSliceRefinementLemma(S,T,{});}
		CoSliceRefinement(S,T,{});
		== {Corollary_5_2(S, T, {});} 
		Corollary_5_2Help(S,T,{});															// all defined variables (...minus the empty set)
		== {Corollary_5_2HelpToCorollary_5_4Help1Lemma(S,T,V);}
		Corollary_5_4Help1(S,T,V);															// union of V and the defined variables
		== {Corollary_5_4Help1ToHelp2Lemma(S,T,V);}
		Corollary_5_4Help2(S,T,V);															// V separately from the non-V defined variables
		== {Corollary_5_4Help2ToHelp3ANDHelp4Lemma(S,T,V,(def(S)+def(T))-V);}
		Corollary_5_4Help3(S,T,V,(def(S)+def(T))-V) && Corollary_5_4Help4(S,T,V,(def(S)+def(T))-V);
		== {Corollary_5_4Help3ToSliceRefinementLemma(S,T,V,(def(S)+def(T))-V);Corollary_5_4Help4ToCoSliceRefinementLemma(S,T,V,(def(S)+def(T))-V);}
		SliceRefinement(S,T,V) && CoSliceRefinement(S,T,V);
		}
}

lemma Corollary_5_5(S: Statement, T: Statement, P:Predicate)
requires Valid(S)
requires Valid(T)
requires vars(P) !! (def(S) + def(T))
ensures TerminationRefinement(S,T) ==> (forall s:State :: (wp(S,P)).0(s) ==> (wp(T,P)).0(s))
{
	if ((forall s:State :: (wp(S,ConstantPredicate(true))).0(s) ==> (wp(T,ConstantPredicate(true))).0(s)))
	{
		forall s:State {
			calc {
				wp(S,P).0(s);
				== {RE3(S,P);}
				AND(P,wp(S,ConstantPredicate(true))).0(s);
				== {}
				P.0(s) && wp(S,ConstantPredicate(true)).0(s);
				==> {assert forall s1:State :: IMPLIES(wp(S,ConstantPredicate(true)),wp(T,ConstantPredicate(true))).0(s1);}
				P.0(s) && wp(T,ConstantPredicate(true)).0(s);
				== {}
				AND(P,wp(T,ConstantPredicate(true))).0(s);
				== {RE3(T,P);}
				wp(T,P).0(s);
				}
			}
	}
}


lemma Corollary_5_6 (S: Statement, T: Statement, V: set<Variable>)
requires Valid(S)
requires Valid(T)
ensures EquivalentStatments(S,T) <==> Corollary_5_6Help1(S,T,V) && Corollary_5_6Help2(S,T,V)
{
		calc{
		EquivalentStatments(S,T);
		== {Theorem_4_1(S,T);}
		Refinement(S,T) && EquivalentPredicates(wp(S,ConstantPredicate(true)),wp(T,ConstantPredicate(true)));
		== {Corollary_5_4(S,T,V);}
		SliceRefinement(S,T,V) && CoSliceRefinement(S,T,V) && EquivalentPredicates(wp(S,ConstantPredicate(true)),wp(T,ConstantPredicate(true)));
		== {}
		SliceRefinement(S,T,V) && CoSliceRefinement(S,T,V) && EquivalentPredicates(wp(S,ConstantPredicate(true)),wp(T,ConstantPredicate(true))) 
		&& EquivalentPredicates(wp(S,ConstantPredicate(true)),wp(T,ConstantPredicate(true)));
		== {} 
		SliceRefinement(S,T,V) && EquivalentPredicates(wp(S,ConstantPredicate(true)),wp(T,ConstantPredicate(true))) 
		&& CoSliceRefinement(S,T,V) && EquivalentPredicates(wp(S,ConstantPredicate(true)),wp(T,ConstantPredicate(true)));
		== {}
		Corollary_5_6Help1Single(S,T,V) && Corollary_5_6Help2Single(S,T,V);
		== {EquivalentCorollary_5_6Help1SingleLemma(S,T,V);EquivalentCorollary_5_6Help2SingleLemma(S,T,V);}
		Corollary_5_6Help1(S,T,V) && Corollary_5_6Help2(S,T,V);
		}
}


lemma ProgramEquivalence5_7 ( S1: Statement, S2: Statement)
	requires def(S1) !! def(S2)
	requires input(S1) !! def(S2)
	requires def(S1) !! input(S2)
	requires Valid(S1)
	requires Valid(S2)
    ensures EquivalentStatments(SeqComp(S1,S2),SeqComp(S2,S1))
{
	forall P: Predicate, s: State | vars(P) <= def(S1) {
		calc {
			wp(SeqComp(S1,S2), P).0(s);
			== {/*wp of ‘ ; ’*/}
			wp(S1,(wp(S2,P))).0(s);
			== {RE3(S2,P);Leibniz2(wp, wp(S2,P), AND(P, wp(S2,ConstantPredicate(true))), S1);}
			wp(S1, AND(P, wp(S2,ConstantPredicate(true)))).0(s);
			== {ConjWp(S1, P, wp(S2,ConstantPredicate(true)));}
			AND(wp(S1,P), wp(S1,(wp(S2,ConstantPredicate(true))))).0(s);
			== { var P1 := wp(S2,ConstantPredicate(true)); assert vars(P1) !! def(S1) by { assert vars(P1) <= input(S2) by { RE2(S2,ConstantPredicate(true)); assert vars(P1) <= vars(ConstantPredicate(true)) - ddef(S2) + input(S2); assert vars(ConstantPredicate(true)) - ddef(S2) + input(S2) <= input(S2) by { assert vars(ConstantPredicate(true)) == {}; }} assert def(S1) !! input(S2);} RE3(S1,P1); }
			AND(wp(S1,P),AND(wp(S2,ConstantPredicate(true)), wp(S1,ConstantPredicate(true)))).0(s);
			== {}
			AND(AND(wp(S1,P),wp(S1,ConstantPredicate(true))), wp(S2,ConstantPredicate(true))).0(s);
			== {AbsorptionOfTermination3_14(P,S1);}
			AND(wp(S1,P), wp(S2,ConstantPredicate(true))).0(s);
			== {var P1 := wp(S1,P); assert vars(P1) !! def(S2) by { assert vars(P1) <= vars(P) - ddef(S1) + input(S1) by { RE2(S1,P); } assert def(S2) !! (input(S1) + vars(P));} RE3(S2,P1); }
			(wp(S2,(wp(S1,P)))).0(s);
			== {/*wp of ‘ ; ’*/}
			wp(SeqComp(S2,S1), P).0(s);
		} 
	}
	forall P: Predicate, s: State | vars(P) !! def(S1) {
		calc {
			wp(SeqComp(S2,S1), P).0(s);
			==	{/*wp of ‘ ; ’*/}
			wp(S2,(wp(S1,P))).0(s);
			== {RE3(S1,P);Leibniz2(wp,wp(S1,P),AND(P,wp(S1,ConstantPredicate(true))),S2);}
			wp(S2,AND(P , wp(S1,ConstantPredicate(true)))).0(s);
			== {ConjWp(S2, P, wp(S1,ConstantPredicate(true)));}
			AND(wp(S2,P), wp(S2,(wp(S1,ConstantPredicate(true))))).0(s);
			== {var P1 := wp(S1,ConstantPredicate(true)); assert vars(P1) !! def(S2) by { assert vars(P1) <= input(S1) by { RE2(S1,ConstantPredicate(true)); } assert def(S2) !! input(S1) ;} RE3(S2,P1); }
			AND(wp(S2,P), AND(wp(S2,ConstantPredicate(true)), wp(S1,ConstantPredicate(true)))).0(s);
			== {}
			AND(AND(wp(S2,P), wp(S2,ConstantPredicate(true))), wp(S1,ConstantPredicate(true))).0(s);
			== {AbsorptionOfTermination3_14(P,S2);}
			AND(wp(S2,P), wp(S1,ConstantPredicate(true))).0(s);
			== {var P1 := wp(S2,P); assert vars(P1) !! def(S1) by { assert vars(P1) <= vars(P) - ddef(S2) + input(S2) by { RE2(S2,P); } assert def(S1) !! (input(S2) + vars(P));} RE3(S1,P1); }
			wp(S1,(wp(S2,P))).0(s);
			== {/*wp of ‘ ; ’*/}
			wp(SeqComp(S1,S2), P).0(s);
		}
	}
	assert EquivalentStatments(SeqComp(S1,S2),SeqComp(S2,S1)) by {Corollary_5_6 (SeqComp(S1,S2), SeqComp(S2,S1), def(S1));}
}

