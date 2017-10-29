include "Util.dfy"
include "Definitions.dfy"

class Fresh {
	/*
	 * map of original variable to a fresh variable.
	 * for example: vr <--> ivr or vr <--> fvr
	 */
	var m : map<Variable, set<Variable>>;
	ghost var range : set<Variable>;	// fresh variables (range of map)
	ghost var rotten : set<Variable>;	// non-fresh variables

	constructor ()
	modifies this
	ensures Valid()
	ensures |m| == 0 && range == {} && rotten == {}
	{
		m := map[];
		range := {};
		rotten := {};
	}

	predicate Valid() 
	reads this
	{
		(|m| == 0 && range == {} && rotten == {}) || (
		   (forall v :: v in m ==> v !in range)
		&& (forall v :: v in range ==> v !in m)
		&& (forall v :: v in rotten <==> v !in range)
		&& (forall v :: v in range ==> v !in rotten)
		&& (forall v :: v in m ==> m[v] <= range))
	}

	/*
	 * in: V - subset of variables to which fresh names are required (V<=SV)
	 * in: SV - set of all variables. Fresh variables should not exist in SV
	 * out: fV - set of fresh variables, one per variable in V (fV !! SV)
	 * side-effect: m is updated accordingly
	 */
	method {:verify true} CreateFresh(V: seq<Variable>, SV: seq<Variable>) returns (fV: seq<Variable>)
	modifies this
	requires Valid()
	requires setOf(V) <= setOf(SV)
	requires forall v :: v in V ==> v !in range
	ensures Valid()
	ensures setOf(fV) <= range
	ensures setOf(fV) !! rotten
	ensures setOf(fV) !! setOf(V)
	ensures forall v :: v in fV ==> v !in SV
	ensures forall v :: v in SV ==> v !in fV
	ensures setOf(fV) !! setOf(SV)
	ensures |fV| == |V|
	{
		var r := V;
		var fV' : seq<Variable> := [];
		while (r != [])
		invariant forall v :: v in r ==> v in V
		invariant forall v :: v in m ==> v in V
		invariant forall v :: v in fV' ==> v !in m
		decreases r
		{
			var name := freshName(r[0], SV, 0, {}, SV);
			if (r[0] in m) {
				m := m[r[0] := m[r[0]]+{name}]; // update 
			} else {
				m := m[r[0] := {name}]; // new map entry
			}
			assert name !in m;
			fV' := fV' + [name];
			assert name in fV';
			r := r[1..];
		}
		
		range := range + setOf(fV');
		rotten := rotten + setOf(SV);
		fV := fV';
	}
	
	function method ComposeName(v: Variable, i : nat) : (res: Variable)
	ensures res == v + intToString(i)
	{
		v + intToString(i)
	}

	lemma failedAttemptsBuildupLemma(v : Variable, 
						 i : nat, 
						 failedAttempts : set<Variable>)
	ensures ComposeName(v, i) !in failedAttempts

	method {:verify true} freshName(v : Variable, 
					 SV: seq<Variable>, 
					 i : nat, 
					 failedAttempts : set<Variable>, 
					 ghost SVorig : seq<Variable> ) 
	returns (fv: Variable)
	decreases |SV|
	requires v in SV
	requires SV <= SVorig
	requires setOf(SV) !! failedAttempts
	requires setOf(SV)+failedAttempts == setOf(SVorig)
	requires forall j :: i > j >= 0 ==> ComposeName(v, j) in failedAttempts
	requires ComposeName(v, i) !in failedAttempts
	ensures fv !in SVorig
	ensures fv != v
	{
		fv := ComposeName(v, i);
		assert fv !in failedAttempts;
		if (fv in SV) {
			var i', SV', failedAttempts' := i+1, seqSubtraction(SV,[fv]), failedAttempts+{fv};
			assert SV' < SV by {
				assert fv !in SV' && fv in SV;
				assume SV' <= SV;
			}
			assert ComposeName(v, i') !in failedAttempts' by
			{ failedAttemptsBuildupLemma(v, i', failedAttempts');}
			fv := freshName(v, SV', i', failedAttempts', SVorig);
			assert fv !in SVorig;
		}
		else
		{
			assert fv !in SVorig;
		}
	}
}
/* end of class Fresh */
