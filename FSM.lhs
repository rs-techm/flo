Copyright (c) 2015 Tech Mahindra

This file is part of Flo.

Flo is free software: you can redistribute it and/or modify it under
the terms of the GNU General Public License version 3, as published by
the Free Software Foundation.

Flo is distributed in the hope that it will be useful, but WITHOUT ANY
WARRANTY; without even the implied warranty of MERCHANTABILITY or
FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
for more details.

You should have received a copy of the GNU General Public License
along with Flo.  If not, see <http://www.gnu.org/licenses/>.


* FSM

> module FSM where

> import Data.List
> import qualified Graph as G
> import qualified Data.Set as S
> import qualified Data.Map as M

> import Flo
> import Lib
> import Comb
> --import Test
> --import Misc

** FSM (OHE)

> fsm_ff_state insize = make_block ("fsm_ff_state_"++(show insize))
>                       (["clk","reset"]++(wire_vec "i" 0 insize)) (["o"])
>                       [inst_block (fst (xbintree_arb gate_or2 insize)) ((wire_vec "i" 0 insize)++["t"]),
>                        inst_block dfr ["clk","reset","t","o"]]

Below init state implementation seems fine assuming reset is synchronous
(deasserted just after a rising clock edge). Else may not work correctly.

> fsm_init_ff_state' insize = make_block ("fsm_init_ff_state_"++(show insize))
>                             (["clk","reset"]++(wire_vec "i" 0 insize)) (["o"])
>                             [if insize==0 then inst_block zero ["t"]
>                              else inst_block (fst (xbintree_arb gate_or2 insize)) ((wire_vec "i" 0 insize)++["t"]),
>                              inst_block dfs ["clk","reset","t","o"]]

> xbintree_arb' block inputs = if inputs==0 then zero else (fst (xbintree_arb block inputs))

> omaps' map' lo sn dn = foldr (\o map''->M.insertWith S.union o (S.singleton (sn++"_"++dn)) map'') map' lo

> omaps graph = (foldr (\(sn,dn,(li,(lo0,lo1))) (map'0,map'1)->((omaps' map'0 lo0 sn dn),(omaps' map'1 lo1 sn dn)))
>                (M.empty,M.empty) (G.edges graph))

> cfag__fsm_ff'' map1 output = [inst_block (xbintree_arb' gate_or2 (S.size (M.findWithDefault S.empty output map1)))
>                               ((S.toList (M.findWithDefault S.empty output map1))++[output])]

Above modified to allow incoming edges into initial state

Each graph edge label is a pair of pair of lists of lists... First pair is the
signals to be anded together (signals in first item in pair are inverted), and
the second pair is the outputs (those in first item in pair are to be zero and
those in the second, one).

> cfag__fsm_ff name ini graph inputs outputs = 
>   make_block name (["clk","reset"]++inputs) outputs
>    ((map (\node->inst_block ((if node==ini then fsm_init_ff_state' else fsm_ff_state) (S.size (G.inEdgeSet node graph)))
>            (["clk","reset"]++((map (\n->n++"_"++node) (G.inNodes node graph))++[node++"_o"]))) (G.nodes graph))++
>    (map (\(sn,dn,((li_,li),lo))->inst_block (fst (xbintree_arb gate_and2 ((length li_)+(length li)+1)))
>          ([sn++"_o"]++(map (\s->s++"_") li_)++li++[sn++"_"++dn])) (G.edges graph))++
>    (concatMap (cfag__fsm_ff'' (snd (omaps graph))) outputs)++
>    (map (\i->inst_block gate_invert [i,(i++"_")]) (nub (concatMap (\(sn,dn,((li_,li),lo))->li_) (G.edges graph)))))

> test = G.insEdges [("s0","s1",(["i0","i1_"],(["o0"],[]))),("s1","s2",(["i1","i2"],(["o0"],["o1"]))),
>                    ("s2","s1",(["i1","i2_"],(["o0"],[]))),("s2","s2",(["i1"],([],["o0","o1"])))]


*** FSM OHE with enable <2013-10-10 Thu>

    Variations of fsm_ff_state, fsm_init_ff_state', cfag__fsm_ff'',
    cfag__fsm_ff with enable.

> fsm_en_ff_state insize = make_block ("fsm_en_ff_state_"++(show insize))
>                          (["clk","reset","en"]++(wire_vec "i" 0 insize)) (["o"])
>                          [inst_block (fst (xbintree_arb gate_or2 insize)) ((wire_vec "i" 0 insize)++["t"]),
>                           inst_block dfrl ["clk","reset","en","t","o"]]

> fsm_en_init_ff_state' insize = make_block ("fsm_en_init_ff_state_"++(show insize))
>                                (["clk","reset","en"]++(wire_vec "i" 0 insize)) (["o"])
>                                [if insize==0 then inst_block zero ["t"]
>                                 else inst_block (fst (xbintree_arb gate_or2 insize)) ((wire_vec "i" 0 insize)++["t"]),
>                                 inst_block dfsl ["clk","reset","en","t","o"]]

> cfag__fsm_en_ff name ini graph inputs outputs = 
>   make_block name (["clk","reset","en"]++inputs) outputs
>    ((map (\node->inst_block ((if node==ini then fsm_en_init_ff_state' else fsm_en_ff_state) (S.size (G.inEdgeSet node graph)))
>            (["clk","reset","en"]++((map (\n->n++"_"++node) (G.inNodes node graph))++[node++"_o"]))) (G.nodes graph))++
>    (map (\(sn,dn,((li_,li),lo))->inst_block (fst (xbintree_arb gate_and2 ((length li_)+(length li)+1)))
>          ([sn++"_o"]++(map (\s->s++"_") li_)++li++[sn++"_"++dn])) (G.edges graph))++
>    (concatMap (cfag__fsm_ff'' (snd (omaps graph))) outputs)++
>    (map (\i->inst_block gate_invert [i,(i++"_")]) (nub (concatMap (\(sn,dn,((li_,li),lo))->li_) (G.edges graph)))))

