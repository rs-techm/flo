> module Graph where

> import qualified Data.Map as Map
> import qualified Data.Set as Set


Graph

FGL caused lot of grief due to the necessity of specifying a node by a
(node(::Int), lab) pair in which the node number has to be
unique. Node number is naturally available for NFA graph but not for
DFA and leads surprsingly to complications. Although, the algorithm
was made to work, it seems it could be simplfied using a graph
representation that simply accepts unique node labels whatever their
type maybe (also such a graph representation seems possible using just
sets and maps).


'Adjacency list' representation with the list of nodes represented by a map,
and the list for each node represented by a set.

The idea is to represent a graph as a map whose key values are node
names (labels) and whose data values are sets, whose elements are
pairs of edge names and destination node values (distinct edge names
can allow multiple edges between same two nodes as is required for
automata).

> type Graph n e = Map.Map n (Set.Set (e,n))

> empty :: Graph n e
> empty = Map.empty

If graph already has a node with the same name as one being inserted
the previous one (presumably with its associated data value) is
deleted. Note that as a result, currently, outgoing edges from the
node will get deleted but incoming edges, if any, will be preserved.

> insNode node graph = Map.insert node Set.empty graph

To prevent above problem, insNode' variant inserts node only if its
not in graph.

> insNode' node graph = if isNode node graph then graph else insNode node graph

> insNodes' nodes graph = foldr insNode' graph nodes

> insNodeSet' nodes graph = Set.fold insNode' graph nodes


When node name is not found in the graph, graph is returned
unchanged. Otherwise outgoing as well as incoming edges to the node
are deleted. Later get deleted by deleting the corresponding set, but
the former have to be hunted down, requiring the Map.map and Set.fold.

> delNode node graph = if Map.member node graph
>                      then Map.map (Set.fold (\(e,n) s-> if n==node then s else Set.insert (e,n) s) Set.empty)
>                             (Map.delete node graph)
>                      else graph


Merely return the corresponding set.

> outEdgeSet node graph = graph Map.! node

> outEdges node graph = Set.toList (outEdgeSet node graph)

> outNodeSet node graph = Set.map snd (outEdgeSet node graph)

> outNodes node graph = map snd (outEdges node graph)

> outLabSet node graph = Set.map fst (outEdgeSet node graph)

> outLabs node graph = Set.toList (outLabSet node graph)

> {-inEdgeSet node graph = Set.fold (\(sn,dn,el) set->if node==dn then Set.insert (sn,dn,el) set else set)
>                        Set.empty (edgeSet graph)-}

*** TODO <2013-04-12 Fri>

Graph type and out* functions return (edge,node) while inEdgeSet returns
(node,edge). Convert all to (node,edge)?

> inEdgeSet node graph = Set.fold (\(sn,dn,el) set->if node==dn then Set.insert (sn,el) set else set)
>                        Set.empty (edgeSet graph)

> inEdges node graph = Set.toList (inEdgeSet node graph)

> inLabSet node graph = Set.map snd (inEdgeSet node graph)

> inLabs node graph = Set.toList (inLabSet node graph)

> isEdge (sn,dn,el) graph = Set.fold (\(el',dn') is_edge->if el'==el && dn'==dn then True else is_edge) False
>                           (outEdgeSet sn graph)

> inNodeSet node graph = Set.fold (\(sn,dn,el) set->if node==dn then Set.insert sn set else set) Set.empty (edgeSet graph)

> inNodes node graph = Set.toList (inNodeSet node graph)

> isNode node graph = Map.member node graph

> selfEdge node graph = Set.member node (outNodeSet node graph)

> nodes graph = Set.toList (nodeSet graph)

> nodeSet graph = (Map.foldWithKey (\k x l-> Set.insert k (Set.union l (Set.map snd x))) Set.empty graph)

> --nodeSet graph = Map.keysSet graph


> edgeSet graph = Map.foldWithKey (\s x set->Set.union (Set.map (\(l,d)->(s,d,l)) x) set) Set.empty graph

> edges graph = Map.foldWithKey (\s x list->(map (\(l,d)->(s,d,l)) (Set.toList x))++list) [] graph

**** TODO Rewrite edges using edgeSet? Uniformly rewrite others as well using their set counterparts?

**** TODO
     Should insEdge also check if destination node is in graph. If not, should
     a separate graph consistency function be written to ensure each node is
     inserted via insNode? If former is assumed, allNodes need not be so
     complex.

**** TODO
     Rename allNodes to nodeList or better, nodes (latter also consistent with Data.Map).

**** TODO
     Write mapEdges and use it to write edges. Rewrite nodes using mapNodes.

**** TODO <2013-04-12 Fri>
     insEdge sn dn e?

> insEdge e sn dn graph = if Map.member sn graph
>                         then Map.adjust (Set.insert (e,dn)) sn graph
>                         else error ((show sn)++"insEdge: Node not found.")

> delEdge e sn dn graph = if Map.member sn graph
>                         then Map.adjust (Set.delete (e,dn)) sn graph
>                         else error ((show sn)++"insEdge: Node not found.")

**** TODO Rewrite insEdge like insEdge'.


Insert edge variant that creates nodes if they don't exist. Required to create
a graph from list of edges and may be useful on its own.

> insEdge' (sn,dn,el) graph = Map.adjust (Set.insert (el,dn)) sn (insNode' dn (insNode' sn graph))

> insEdges le = foldr insEdge' empty le

**** DONE delEdge? <2012-09-25 Tue>

Union and variants have same semantics as the corresponding Map functions.

**** TODO Unions may not be too useful. Proper merge_graph required (perhaps unionWith with a suitable function).

*** Depth First Search <2015-04-10 Fri>

Based on [[https://en.wikipedia.org/wiki/Depth-first_search#Pseudocode][wikipedia. Set as well as list used to store nodes, as former is used
to search for nodes and latter to preserve order (and is the output).

> dfs1 node ((set,list),graph) = if (Set.member node set) then ((set,list),graph) else dfs0 graph node (set,list)

> dfs0 graph node (set,list) = Set.fold dfs1 ((Set.insert node set,(node:list)),graph) (outNodeSet node graph)

> dfs graph node = snd (dfs0 graph node (Set.empty,[]))

Currently merge_graph valid only for graphs with disjoint nodes

> merge_graphs g1 g2 = Map.unionWith Set.union g1 g2

> union g1 g2 = Map.union g1 g2

> unionWith fn g1 g2 = Map.unionWith fn g1 g2

> unionWithKey kfn g1 g2 = Map.unionWithKey kfn g1 g2

> unions graphs = Map.unions graphs

> unionsWith fn graphs = Map.unionsWith fn graphs


> mapNodes fn graph = Map.foldWithKey (\n s m->Map.insert (fn n) (Set.map (\(e,n')->(e,(fn n'))) s) m) Map.empty graph


> delquotes s = filter ((/=) '"') s

Assigns an integers from i0 to (i0 + nodes in graph) to the nodes in
the graph. Returns a map with nodes as keys and the assigned ints as data values.

> numNodes i0 graph = Map.fromList (zipWith (\n i->(n,i)) (nodes graph) [i0..])


*** Transitive closure.

> --trans_clos' g node = Set.fold (\(src,dest,lab) g'->if is_edge' (src,node) && is_edge' (node,dest) then g (edges g))

> --trans_clos g = trans_clos' (nodes g)


*** Convert given graph to Graphviz format.

> graphviz_header = "digraph gv {\n        margin = \"0\"\n        page = \"8.5,11.0\"\n        size = \"11.0,8.5\"\n        rotate = \"90\"\n        ratio = \"fill\"\n"

> graphviz_footer = "\n}\n"

> graphviz_nodes nodemap graph = concatMap (\(n, i)->"        "++(show i)++" [label = \""++(delquotes (show n))++"\"]\n")
>                                (Map.toList nodemap)

> graphviz_edges nodemap graph = concatMap (\(s,d,l)->"        "++(show (nodemap Map.! s))++" -> "++
>                                           (delquotes (show (nodemap Map.! d)))++
>                                           " [label = \""++(delquotes (show l))++"\"]\n") (edges graph)

> graphviz graph = graphviz_header++(graphviz_nodes (numNodes 1 graph) graph)++(graphviz_edges (numNodes 1 graph) graph)++
>                  graphviz_footer

**** TODO show "\\" outputs "\\\\" so putStr(shows"\\") outputs "\\" but "\" is required. <2012-08-15 Wed>


**** TODO Add fold/map over edges/nodes.
