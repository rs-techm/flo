Copyright 2015 Tech Mahindra

This file is part of Flo.

Flo is free software: you can redistribute it and/or modify it under
the terms of the GNU General Public License as published by the Free
Software Foundation, either version 3 of the License, or (at your
option) any later version.

Flo is distributed in the hope that it will be useful, but WITHOUT ANY
WARRANTY; without even the implied warranty of MERCHANTABILITY or
FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
for more details.

You should have received a copy of the GNU General Public License
along with Flo.  If not, see <http://www.gnu.org/licenses/>.


* Sim

> module Sim where
> import Misc
> import Flo
> import qualified Lib as Lib
> import qualified Graph as Graph
> import qualified Data.Map as Map
> import qualified Data.Set as Set
> import Control.Exception
        
- If any input is z, output is z
- If any input is x, and no input is z, output is x (to enable hunting x source)
  - Although gate_or2 (x,1) should be 1, it is assigned x

> z = 2
        
> x = 3
        
> gate_invert = Map.fromList [(z,z),(x,x),(0,1),(1,0)]
        
The 12 common entries for 2 input gates.

> common_gate_2 = [((z,z),z),((z,x),z),((x,z),z),((x,x),x),((x,0),x),((x,1),x),((0,x),x),((1,x),x),((z,0),z),((z,1),z),((0,z),z),((1,z),z)]

> gate_and2 = Map.fromList (common_gate_2++[((0,0),0),((0,1),0),((1,0),0),((1,1),1)])

> gate_or2 = Map.fromList (common_gate_2++[((0,0),0),((0,1),1),((1,0),1),((1,1),1)])
        
> gate_nand2 = Map.fromList (common_gate_2++[((0,0),1),((0,1),1),((1,0),1),((1,1),0)])

> gate_nor2 = Map.fromList (common_gate_2++[((0,0),1),((0,1),0),((1,0),0),((1,1),0)])

> gate_xor2 = Map.fromList (common_gate_2++[((0,0),0),((0,1),1),((1,0),1),((1,1),0)])

> gate_xnor2 = Map.fromList (common_gate_2++[((0,0),1),((0,1),0),((1,0),0),((1,1),1)])

> demux2 = Map.fromList ((map (\((a,b),p)->((a,b),(p,p))) common_gate_2)++[((0,0),(0,0)),((0,1),(0,0)),((1,0),(1,0)),((1,1),(0,1))])

> andor2 = Map.fromList ((map (\((a,b),p)->((a,b),(p,p))) common_gate_2)++[((0,0),(0,0)),((0,1),(0,1)),((1,0),(0,1)),((1,1),(1,1))])

The 56 common entries for 3 input gates are generated programatically.

> common_gate_3_0 (a,b,c) list = if (a==z)||(b==z)||(c==z) then (((a,b,c),z):list) else if (a==x)||(b==x)||(c==x) then (((a,b,c),x):list) else list
         
> common_gate_3 = foldr common_gate_3_0 [] (concat(concat(map3 (,,) [0,1,x,z] [0,1,x,z] [0,1,x,z])))
        
> mux2 = Map.fromList (common_gate_3++[((0,0,0),0),((0,0,1),0),((0,1,0),0),((0,1,1),1),((1,0,0),1),((1,0,1),0),((1,1,0),1),((1,1,1),1)])

** Block Evaluation <2015-04-16 Thu>

> --eval_block block imap omap = 

> --eval_block map block = foldr (eval_block0 map) Map.empty (inst_blocks_ block)


*** Topological sort of instances in block <2015-04-19 Sun>

Not too elegant but (seems to) get the job done. Given a block, rearrange its
list of instantiated blocks into topological order. To do so, the instantiated
modules are mapped to nodes in a directed acyclic graph (dag) with edges
representing wire connections. Start with for each instantiated
block, distinguishing its input and output wires. Use it to construct dag and
use topo_sort from graph library to sort.

**** part_io

Partition the wire list for each instantiated module into input and output,
returning, for each instantiated block, (block_name,inputs,outputs).

> part_io0 inst_block part_list = let in_ports_size = length (in_ports_ (block_ inst_block))
>                                 in assert (length (wires_ inst_block) == (in_ports_size +  length (out_ports_ (block_ inst_block))))
>                                        (((name_ (block_ inst_block)),(take in_ports_size (wires_ inst_block)),(drop in_ports_size (wires_ inst_block))):part_list)
        
> part_io block = (foldr part_io0 [] (inst_blocks_ block))++[((name_ block)++".i",[],(in_ports_ block)),((name_ block)++".o",(out_ports_ block),[])]

**** plist__imap

From above partition list use block name and inputs to construct map
(inputs_map) from each input wire (key) to destination block (data).

> plist__imap0 (block,inputs,outputs) map = foldr (\input map'->Map.insertWith Set.union input (Set.singleton block) map') map inputs

> plist__imap part_list = foldr plist__imap0 Map.empty part_list

**** block__dag

From above partition list use block name and outputs with above inputs map to
construct dag. For each outgoing wire from a block, figure out its incoming
block using input_map, and using above two blocks and connecting wire,
construct and edge of dag. In addition parent block name suffixed with ".i" and
".o" are used as source and destination nodes for parent block input and output
wires respectively.

> block__dag1 inputs_map block wire dag = Set.fold (\block' dag'->assert (block /= block') Graph.insEdge' block block' wire dag') dag (lookup' wire inputs_map)
        
> block__dag0 inputs_map (block,inputs,outputs) dag = foldr (block__dag1 inputs_map block) dag outputs

> block__dag block = let part_list = part_io block
>                    in foldr (block__dag0 (plist__imap part_list)) Graph.empty part_list

**** block_topo_sort
        
As topo_sort returns a list of names (strings) block_name_map is constructed
which given name, returns instantiated block, enabling construction of
instantiated block list in the topological order.

Simple but slightly hackish solution below to simply delete the input and
output nodes (as opposed to find and delete not only above two nodes but also
(somewhat painstakingly) their connecting edges before generating the dag.

> block_topo_sort block = let block_name_map = foldr (\inst_block map->Map.insert (name_ (block_ inst_block)) inst_block map) Map.empty (inst_blocks_ block)
>                             topo_order = Graph.topo_sort (Graph.delNode ((name_ block)++".o") (Graph.delNode ((name_ block)++".i") (block__dag block)))
>                         in block {inst_blocks_ = (foldr (\iblk iblks -> (lookup' iblk block_name_map):iblks) [] topo_order)}

> test_topo_sort = make_block "test_topo_sort" ["i0","i1","i2","i3"] ["o"]
>                  (reverse [inst_block Lib.gate_or2 ["i2","t1","t2"], inst_block Lib.gate_xor2 ["i3","t2","o"], inst_block Lib.gate_and2 ["i0","i1","t1"]])

*** Generate sim structures <2015-04-23 Thu>

> gen_sim block input_map = foldr 

> data Block_wire_map = Block_wire_map_ {block_bwm_::Block, wire_map_::Map.Map String Int,
>                                        inst_blocks_map_::Map.Map String Block_wire_map}

> data RT a = Nil | Cons a (RT a)

> --data Net a = Net_ {block_wire_ :: (Inst_block,[Char]), net_forest_ :: [Net a]}

> type Net = Tree (Inst_block,[Char])

> type Nets_tree = Tree (Inst_block,[Net])

> nil_block = Block_ [] [] [] []

> nil_inst_block = Inst_block_ nil_block []

**** Find nets <2015-04-28 Tue>

The input to find_nets is the root block and using trav_blocks traversal the
output (also output for each block in the hierarchy) is net_lists_trees, a list
of pairs (net_lists,net_trees).
 - net_lists for a block is a list of /nets/, one net for each port (input or
   output) of the block. A net (of type Net) corresponds to a 'physical' wire
   over the entire block hierarchy, with the net (wire) name in a block
   specified in the correponding node in the Net tree.
 - net_trees for a block is a tree used as a 'hanger' for the nets. If the net
   has a root in a particular block (net is not an input ot output port) then
   it is stored in the net_tree node corresponding to the block. Since many
   such nets can exist in a block, a net_tree node stores a list of nets.

find_nets_pblock and find_nets_block are the trav_blocks functions.
find_nets_pblock is simple providing list of 'leaf node' nets for net_list and
nil for nets_tree. Both net and nets_tree have an inst_block field which is
updated while processing the parent block (it was experimented to modify
trav_blocks to provide inst_block but it wasn't 'satisfying' (because function
structure didn't seem 'natural' (one symptom would be requiring to instantiate
root block (slightly ugly))) so while updating in parent block seems complex,
it actually seems 'natural').

Key complexity is in find_nets_block. Essentially, for given block, wires are partitioned into port (input
and output) and others. Former are used in net_lists (processed by fn_net_list
(fn for find_nets)) and latter in net_trees (processed by fn_net_tree). Input
is [(net_lists,net_trees)] one pair for each instantiated block in block.

A key task (common to both fn_net_list and fn_net_tree) is to create the nets
in the block. For each net, one needs to identify all instantiated nodes it is
connected to. To do so efficiently, fn_wire_map creates a map from wire name to
set of nets (each net corresponding to the net supplied for an instantiated
block where the wire name was used in the instantiated block). fn_net_forest is
used to do so for a list of wires (which is port wires for fn_net_list and
others (so have root net node here) for fn_net_tree).

> find_nets_lblock block = error "find_blocks_net: LBlock encountered."

> fn_pblock_net_list block = map (\port->Tree_ {node_=(nil_inst_block,port), forest_=[]}) ((in_ports_ block)++(out_ports_ block))

> find_nets_pblock block = (fn_pblock_net_list block, Tree_ (nil_inst_block, []) [])

Wire map also inserts the inst_block value, as its covenient to do so (since
inst_block is available anyway).

> fn_wire_map0 (inst_block,net_list) map = foldr (\(net,wire) map'->Map.insertWith Set.union wire (Set.singleton (net {node_=(inst_block,(snd (node_ net)))})) map')
>                                          map (zipWith (,) net_list (wires_ inst_block))

> fn_wire_map block net_lists = foldr fn_wire_map0 Map.empty (zipWith (,) (inst_blocks_ block) net_lists)

> fn_net_forest0 block net_lists wire = Tree_ (nil_inst_block,wire) (Set.foldr (:) [] (Misc.lookup' wire (fn_wire_map block net_lists)))

> fn_net_forest block net_lists wire_list = map (fn_net_forest0 block net_lists) wire_list

> fn_net_list block net_lists = fn_net_forest block net_lists (io_ports block)

Update of inst_block for net_lists taken care of in wire_map, for net_tree have
done it in fn_net_tree.

> fn_net_tree block net_lists_trees = Tree_ {node_=(nil_inst_block,(fn_net_forest block (map fst net_lists_trees) (non_io_wires block))),
>                                            forest_=((zipWith (\inst_block (net_list,net_tree)->net_tree{node_=(inst_block,(snd (node_ net_tree)))})
>                                                     (inst_blocks_ block) net_lists_trees))}

> find_nets_block block net_lists_trees = (fn_net_list block (map fst net_lists_trees), fn_net_tree block net_lists_trees)

> find_nets block = trav_blocks find_nets_block find_nets_pblock block
