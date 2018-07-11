include "Definitions.dfy"
include "Util.dfy"
include "CFG.dfy"

// PDG Definitions:

//datatype Tag = Control | Data(vars: set<Variable>)
datatype Tag = Control | Data(v: Variable) // changed to singleton variable
datatype PDGNode = Node(l:Label) | Entry
type PDGEdge = (PDGNode, PDGNode, Tag)
type PDG = (set<PDGNode>, set<PDGEdge>, map<CFGNode, PDGNode>)

//method ComputePDG(S: Statement, cfg: CFG) returns (N: set<PDGNode>, E: set<PDGEdge>)


method ComputePDG(S: Statement, cfg: CFG) returns (pdg: PDG)
{
	var nodes, cfgToPdgNodeMap := ComputePDGNodes(S, cfg);
	var edges := ComputePDGEdges(S, cfg, cfgToPdgNodeMap);

	var pdg := (nodes, edges, cfgToPdgNodeMap);
}

function PDGEdges(S: Statement, cfg: CFG, cfgToPdgNodeMap: map<CFGNode, PDGNode>): set<PDGEdge>
{
	//set edge: PDGEdge | edge.0
}


method ComputePDGNodes(S: Statement, cfg: CFG) returns (N: set<PDGNode>, cfgToPdgNodeMap: map<CFGNode, PDGNode>)
{
	cfgToPdgNodeMap := map[];
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
}

method ComputePDGEdges(S: Statement, cfg: CFG, cfgToPdgNodeMap: map<CFGNode, PDGNode>) returns (E: set<PDGEdge>)
{
	E := {};
	var cfgNodes := set node | node in cfgToPdgNodeMap;
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