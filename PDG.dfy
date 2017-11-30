include "Definitions.dfy"
include "Util.dfy"
include "CFG.dfy"

// PDG Definitions:
datatype Tag = Control | Data(vars: set<Variable>)
datatype PDGNode = Node(l:Label) | Entry
type PDGEdge = (PDGNode, PDGNode, Tag)

method ComputePDG(S: Statement, cfg: CFG) returns (N: set<PDGNode>, E: set<PDGEdge>)
{
	var cfgToPdgNodeMap : map<CFGNode, PDGNode> := map[];
	N := {};
	var cfgNodes := cfg.0;
	while (|cfgNodes| > 0) {
		var cfgNode : CFGNode;
		cfgNode	:| cfgNode in cfgNodes;
		cfgNodes := cfgNodes - {cfgNode};
		match cfgNode {
			case Entry =>
				var pdgNode := PDGNode.Entry;
				N := N + {pdgNode};
				cfgToPdgNodeMap := cfgToPdgNodeMap[cfgNode := pdgNode];
			case Node(l) => 
				var pdgNode := PDGNode.Node(l);
				N := N + {pdgNode};
				cfgToPdgNodeMap := cfgToPdgNodeMap[cfgNode := pdgNode];
			case Exit =>
		}
	}
	E := {};
	cfgNodes := set node | node in cfgToPdgNodeMap;
	while (|cfgNodes| > 0) 
	invariant forall n :: n in cfgNodes ==> n in cfgToPdgNodeMap
	{
		var dest : CFGNode;
		dest :| dest in cfgNodes;
		cfgNodes := cfgNodes - {dest};
		match dest {
			case Entry =>
			case Node(destLabel) => 
				var sourceNodes := set node | node in cfgToPdgNodeMap;
				assert forall n :: n in sourceNodes ==> n in cfgToPdgNodeMap;
				var theSource := PDGNode.Entry;
				var theSourceLabel := [];
				while (|sourceNodes| > 0) 
				invariant forall n :: n in sourceNodes ==> n in cfgToPdgNodeMap
				{
					var source : CFGNode;
					source :| source in sourceNodes;
					sourceNodes := sourceNodes - {source};
					match source {
						case Entry =>
						case Node(sourceLabel) => if (theSourceLabel < sourceLabel < destLabel) {
								theSourceLabel := sourceLabel;
								theSource := cfgToPdgNodeMap[source];
							}
						case Exit =>
					}
				}
				E := E + {(theSource, cfgToPdgNodeMap[dest], Control)};
			case Exit =>
		}
	}
		
}

