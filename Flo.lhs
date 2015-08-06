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


> module Flo where

> import Prelude
> import Data.Char
> import Numeric
> import Data.List
> import qualified Data.Set as Set
> import qualified Data.Map as Map

> import Misc

> out_ver = putStr . fl__ver

Seems there is a subtle point in how Block and Inst_block are defined below
(which happens to be 'mutually recursive'). It may initially seem that a single
definition as a 'rose' tree (each node defined as data plus a forest (list) of
trees). But above would be relatively simplistic compared to how
function/procedure definitions are typically structured in a programming
language: each definitions may 'refer' other definitions, and since multiple
such references can occur to a single definition, the structure is somewhat
more complex than a simple tree, and the definitions below seem to be a more
natural fit. <2015-04-28 Tue>

> data Block = Block_ {name_ :: String, in_ports_ :: [String], out_ports_ :: [String], inst_blocks_ :: [Inst_block]}
> --             deriving (Eq, Show)
>            | Pblock_ {name_ :: String, in_ports_ :: [String], out_ports_ :: [String], text_ :: String}
>            | Lblock_ {name_ :: String, in_ports_ :: [String], out_ports_ :: [String]}
>              deriving (Eq, Show)

Below stuff to make Block (and Inst_block) instance of Ord class.

> block_ord list = foldr (\new old->if old/=EQ then old else new) EQ list

> instance Ord Block where
>     compare block0 block1 = case (block0,block1) of
>                             ((Lblock_ a0 b0 c0),(Lblock_ a1 b1 c1)) -> block_ord [(compare a0 a1),(compare b0 b1),(compare c0 c1)]
>                             ((Lblock_ a0 b0 c0),(Pblock_ a1 b1 c1 d1)) -> LT
>                             ((Lblock_ a0 b0 c0),(Block_ a1 b1 c1 d1)) -> LT
>                             ((Pblock_ a0 b0 c0 d0),(Lblock_ a1 b1 c1)) -> GT
>                             ((Pblock_ a0 b0 c0 d0),(Pblock_ a1 b1 c1 d1)) -> block_ord [(compare a0 a1),(compare b0 b1),(compare c0 c1),(compare d0 d1)]
>                             ((Pblock_ a0 b0 c0 d0),(Block_ a1 b1 c1 d1)) -> LT
>                             ((Block_ a0 b0 c0 d0),(Lblock_ a1 b1 c1)) -> GT
>                             ((Block_ a0 b0 c0 d0),(Pblock_ a1 b1 c1 d1)) -> GT
>                             ((Block_ a0 b0 c0 d0),(Block_ a1 b1 c1 d1)) -> block_ord [(compare a0 a1),(compare b0 b1),(compare c0 c1),(compare d0 d1)]
        
> data Inst_block = Inst_block_ {block_ :: Block, wires_ :: [String]}
>                   deriving (Eq, Show)

> instance Ord Inst_block where
>     compare (Inst_block_ b0 w0) (Inst_block_ b1 w1) = if (compare b0 b1)/=EQ then (compare b0 b1) else (compare w0 w1)
        
> io_ports block = (in_ports_ block)++(out_ports_ block)

> all_wires block = filter (\w->isAlpha(head w)||('_'==(head w))) (concatMap wires_(inst_blocks_ block))

> non_io_wires block = Set.toList (Set.difference (Set.fromList (all_wires block)) (Set.fromList (io_ports block)))

> trav_blocks fn fnp fnl block = case block of
>                                Block_ a b c d -> fn block (map ((trav_blocks fn fnp fnl) . block_) (inst_blocks_ block))
>                                Pblock_ a b c d -> fnp block
>                                Lblock_ a b c -> fnl block

> trav_blocks' fn fnp inst_block = case (block_ inst_block) of
>                                  Block_ a b c d -> fn inst_block (map ((trav_blocks' fn fnp)) (inst_blocks_ (block_ inst_block)))
>                                  Pblock_ a b c d -> fnp inst_block


> v_inst_mod (inst_block, i) = "  "++(name_ (block_ inst_block))++" "++(name_ (block_ inst_block))++"_"++(show i)++"("++
>                              ((concat (intersperse ", " (wires_ inst_block))))++");\n"

> dec_wires blk = intercalate ", "  
>                 ((if (in_ports_ blk)==[] then [] else ["input wire "++(((intercalate ", ") . in_ports_) blk)])++
>                  (if (out_ports_ blk)==[] then [] else ["output wire "++(((intercalate ", ") . out_ports_) blk)]))

> block__mod block = let all_wires = filter (\w->isAlpha(head w)||('_'==(head w))) (concatMap wires_ (inst_blocks_ block))
>                        wires = (\\) (nub all_wires) (io_ports block)
>                    in "\nmodule "++(name_ block)++" ("++(dec_wires block)++");\n"++
>                           (if (wires == []) then "" else ("  wire "++(concat (intersperse "," wires))++";\n"))++
>                           (concatMap v_inst_mod (zip (inst_blocks_ block) [0..]))++"endmodule\n"

> pblock__mod block = "\nmodule "++(name_ block)++" ("++(dec_wires block)++");\n"++(text_ block)++"endmodule\n"

> blocks_used block = nub (trav_blocks (\block blocks->block:(concat blocks)) (\block->[]) (\block->[]) block)

> pblocks_used block = nub (trav_blocks (\block blocks->(concat blocks)) (\block->[block]) (\block->[]) block)

> fl__ver block = (concatMap pblock__mod (pblocks_used block))++(concatMap block__mod (blocks_used block))


> ports_vec ports vec_ports size = concatMap (\port-> if (elem port vec_ports)
>                                                     then map (\i->port++""++(show i)) [0..(size-1)]
>                                                     else [port]) ports 

> ports_vec_i ports vec_ports i =  map (\port-> if (elem port vec_ports) then (port++""++(show i)) else port) ports


*** Combinators

> ser a b = make_block ((name_ a)++"S"++(name_ b)) (in_ports_ a) (out_ports_ b)
>           [inst_block a ((in_ports_ a)++(out_ports_ a)), inst_block b ((out_ports_ a)++(out_ports_ b))]

**** DONE ser' is useful (synch_ram) but not general as (in_ports_ b) and (in_ports_ a) size may differ, what to do?
     [changed ser' def to something (hopefully) more useful.]

> par a b = make_block ((name_ a)++"P"++(name_ b)) ((in_ports_ a)++(in_ports_ b)) ((out_ports_ a)++(out_ports_ b))
>           [inst_block a ((in_ports_ a)++(out_ports_ a)), inst_block b ((in_ports_ b)++(out_ports_ b))]

> addp l = map (\w->if w=="clk" || w=="reset" then w else "P"++w) l -- map ((++) "P") l


> par' a b = make_block ((name_ a)++"P"++(name_ b)) (nub ((in_ports_ a)++(addp (in_ports_ b))))
>            (nub ((out_ports_ a)++(addp (out_ports_ b))))
>            [inst_block a ((in_ports_ a)++(out_ports_ a)), inst_block b (addp ((in_ports_ b)++(out_ports_ b)))]


reni (rename inputs) essentially (by creating a new block in which b is
instantiated) replaces the list of input port names of b by the list l (which
should be of same size).

> reni l b = make_block ("reni_"++(name_ b)) l (out_ports_ b) [inst_block b (l++(out_ports_ b))]

*** Primitives

> make_inst_block1 size wires = if wires==[] then (take size (repeat [])) else wires

> make_inst_block block wires = Inst_block_ {block_=block, wires_=(make_inst_block1 (length (io_ports block)) wires)}

> inst_block = make_inst_block

> make_inst_block_v block wires_or_prefixes size = map (make_inst_block block)
>                                                  (map (\i->(map (\wp->wp++(if (last wp)=='_' then (show i) else ""))
>                                                             wires_or_prefixes)) [0..(size-1)])

> make_pblock name in_ports out_ports text = Pblock_ {name_=name,in_ports_=in_ports,out_ports_=out_ports,text_=text}

> make_lblock name in_ports out_ports = Lblock_ {name_=name,in_ports_=in_ports,out_ports_=out_ports}

> make_block name in_ports out_ports inst_blocks = Block_ {name_=name,in_ports_=in_ports,out_ports_=out_ports,
>                                                          inst_blocks_=inst_blocks}

id_block:

> pblk_id = make_pblock "id" ["i"] ["o"] "  assign o = i;\n"
