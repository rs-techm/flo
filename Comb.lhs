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


> module Comb where

> import Data.List
> import Data.Char

> import Flo
> import Misc


*** Permute

Creates a module with size inputs and outputs that reorders the inputs
according to the specified function fn which should be bijective (?)

> permute name fn size = make_block ("permute_"++name++"_"++(show size)) (wire_vec "i" 0 size) (wire_vec "o" 0 size)
>                        (map (\i->inst_block pblk_id [("i"++(show i)),("o"++(show (fn size i)))]) [0..(size-1)])

> --combinators

> replace_elem list elem elem' = map (\e->if e == elem then elem' else e) list
> replace_elems list elems elems' = foldr (\(e,e') r->replace_elem r e e') list (zipWith (,) elems elems')
>
    
> _chain' pre blk blk0 adj vports i b = make_block (pre++(name_ blk)++"_"++(show (i+1)))
>                                        (ports_vec (in_ports_ blk0) vports (i+1)) (ports_vec (out_ports_ blk0) vports (i+1))
>                                        [inst_block blk (ports_vec_i (io_ports blk) vports i),
>                                         inst_block b (ports_vec (replace_elems (io_ports blk0)
>                                                                  (intersect (out_ports_ blk0) adj)
>                                                                  (intersect (in_ports_ blk) adj)) vports i)]

> chain' blk blk0 com_in adj size = foldr (_chain' "" blk blk0 adj (((io_ports blk)\\com_in)\\adj)) blk0
>                                   (reverse [1..(size-1)])


> chain0' blk com_in size = chain' blk blk com_in [] size

*** chain variants with prefix <2013-06-29 Sat>

    Solution to the nameclash problem: chain' and chain0' variants with prefix
    argument. Also had to modify _chain' to add the prefix (pre) argument, and
    chain' and chain0' to pass "" as the pre argument.

> chain'' pre blk blk0 com_in adj size = foldr (_chain' pre blk blk0 adj (((io_ports blk)\\com_in)\\adj)) blk0
>                                         (reverse [1..(size-1)])

> chain0'' pre blk com_in size = chain'' pre blk blk com_in [] size


Assumed that only difference between ports of blk0 and other blocks is
that blk0 has no "cin" type ports. And so it is hoped that replacing
blk by blk0 in (((io_ports blk)\\com_in)\\adj) should be fine.

Okay, chain finally seems to have the right (probably just cleaner)
abstraction. The code could be cleaner if ports are generated using
the ports of b instead of starting from scratch as done now. The
improvement requires being able to increment by one the vector ports
in input ports list. Writing a function for it seems a bit painful,
but there may be a more generally useful abstraction lurking in there
(and likely more compact chain:)).

Abstraction seems to break for addsubv: how to connect common signal
addsub to "cin" input of blk0?

Latest (hopefully (almost) final) idea is to use a "hylomorphism" as
the origin for all linear (array like) structures. We start with the
most general, where the hylo unfold produces a list of pairs, each a
pair composed of a block and a tuple composed of com_in, left and
right ports for the block. Per block ports seems similar to above idea
so hopefully we're on the right track...

So, how to right the e (lets call it chn (for now)) for the hylo? Lets try:

Attributes:
1. Array structure base name
2. Instance appended name (else default instance number (starting from 0))
3. Bidir adjacent (else unidir)
4, Explicit block list (else ?)
5. Adj list (else none)
6. z parameter


> wire_vec prefix start size = map (\i-> prefix ++ (show i)) [start..(start+size-1)]

> wires prefix start size = map (\i-> prefix ++ (show i)) [start..(start+size-1)]

> wires0 prefix size = wires prefix 0 size

_wires2 functionality seems useful, so separated it out from wires. <2013-07-01 Mon>

> _wires2 prefix start0 size0 start1 size1 = map2 (\i j-> prefix++(show i)++"_"++(show j)) [start0..(start0+size0-1)]
>                                                  [start1..(start1+size1-1)]

> _wires2_0 prefix size0 size1 = _wires2 prefix 0 size0 0 size1


> wires2 prefix start0 size0 start1 size1 = concat (_wires2 prefix start0 size0 start1 size1)

> wires2_1 prefix start0 size0 size1 = wires2 prefix start0 size0 0 size1

> wires2_0 prefix size0 size1 = wires2 prefix 0 size0 0 size1

> wires2' prefix start0 size0 start1 size1 = concat (transpose (map2 (\i j-> prefix++(show i)++"_"++(show j)) [start0..(start0+size0-1)]
>                                                   [start1..(start1+size1-1)]))

> wires2'_1 prefix start0 size0 size1 = wires2' prefix start0 size0 0 size1

> wires2'_0 prefix size0 size1 = wires2' prefix 0 size0 0 size1

Following needed due to chain' portname problem when size=1.

> wires' prefix start size = if size==1 then [prefix] else wires prefix start size

> wires0' prefix size = if size==1 then [prefix] else wires0 prefix size

> ---block!=nil, arity>1, levels>=0 (level 0 returns pblk_id)
> tree_complete block arity levels = foldr (tree_complete_1 block ((name_ block)++"_"++(show arity)) arity
>                                             (length (out_ports_ block))) pblk_id (reverse [1..levels])

> tree_complete_1 node_blk name_prefix arity width level tree_blk =
>   make_block (name_prefix++"_"++(show level)) (wire_vec "i" 0 (width*(arity^(level)))) (wire_vec "o" 0 width)
>                ((inst_block node_blk ((wire_vec "_t" 0 (arity*width))++(wire_vec "o" 0 width))):
>                 (map (\i->inst_block tree_blk ((wire_vec "i" (i*width*(arity^(level-1))) (width*(arity^(level-1))))++
>                                                (wire_vec "_t" (i*width) width))) [0..(arity-1)]))

> jwidth block arity = (length (in_ports_ block)) - ((length (out_ports_ block))*arity)

Seems to work out quite well: since level is 0 for pblk_id, the j
inputs to it disappear as the number of j inputs is jwidth*(level-1)

Seems xtree* performs functionality of tree*, so delete latter? Also
chain performs functionality of vec? Or better to define vec in terms
of chain? And tree in terms of xtree?

Why use pblk_id in tree and xtree? Simplifies code (else if statement
would be required). Also gives a (hopefully) useful output for level=0
which may be useful in some situations. More importantly, the
[x]bintree_arb function, in order to construct a [x]tree with
arbitrary inputs, uses pblk_id as a [x]tree with one input. While
[x]trees with arbitrary input could be constructed without a [x]tree
of one input, the ability to do so is convenient as it simplifies
code. Again, it also enables [x]bintree_arb to return something
(hopefully) useful when asked to return a [x]tree with one input.


> xtree_complete block arity levels = foldr (xtree_complete_1 block ((name_ block)++"_"++(show arity)) arity
>                                             (length (out_ports_ block)) (jwidth block arity)) pblk_id (reverse [1..levels])

> xtree_complete_1 node_blk name_prefix arity width jwidth level tree_blk =
>   make_block (name_prefix++"_"++(show level)) ((wire_vec "i" 0 (width*(arity^level)))++
>                                                (wire_vec "j" 0 (jwidth*level))) (wire_vec "o" 0 width)
>                ((inst_block node_blk ((wire_vec "_t" 0 (arity*width))++(wire_vec "j" (jwidth*(level-1)) jwidth)++(wire_vec "o" 0 width))):
>                 (map (\i->inst_block tree_blk ((wire_vec "i" (i*width*(arity^(level-1))) (width*(arity^(level-1))))++
>                                                (wire_vec "j" 0 (jwidth*(level-1)))++
>                                                (wire_vec "_t" (i*width) width))) [0..(arity-1)]))

> compose_bintree node_blk width (ltree_blk,l_level) (rtree_blk,r_level) =
>     (make_block "" (wire_vec "i" 0 (width*((2^l_level)+(2^r_level)))) (wire_vec "o" 0 width)
>                  [inst_block node_blk ((wire_vec "_t" 0 (2*width))++(wire_vec "o" 0 (width))),
>                   inst_block ltree_blk ((wire_vec "i" 0 (width*(2^l_level)))++(wire_vec "_t" 0 (width))),
>                   inst_block rtree_blk ((wire_vec "i" (width*(2^l_level)) (2^r_level))++(wire_vec "_t" width (width)))],
>      (max l_level r_level)+1)

> bintree_arb block inputs = foldl1 (compose_bintree block (length (out_ports_ block)))
>                            (unfold (0 ==) (\x->(tree_complete block 2 (log2_floor x), (log2_floor x)))
>                                            (\x-> x - (2^(log2_floor x))) inputs)


It is assumed that the left subtree is larger than the right one.

> compose_xbintree' node_blk width jwidth (ltree_blk,l_level) (rtree_blk,r_level) =
>   (make_block ((name_ node_blk)++"__"++(show l_level)++"_"++(show r_level))
>    ((wire_vec "i" 0 (width*((2^l_level)+(2^r_level))))++(wire_vec "j" 0 (jwidth*((max l_level r_level)+1))))
>    (wire_vec "o" 0 width)
>    [inst_block node_blk ((wire_vec "_t" 0 (2*width))++(wire_vec "j" (jwidth*l_level) jwidth)++
>                                                       (wire_vec "o" 0 (width))),
>     inst_block ltree_blk ((wire_vec "i" 0 (width*(2^l_level)))++(wire_vec "j" 0
>                                                                  (jwidth*l_level))++(wire_vec "_t" 0 (width))),
>     inst_block rtree_blk ((wire_vec "i" (width*(2^l_level)) (2^r_level))++(wire_vec "j"  (jwidth*(l_level-r_level))
>                                                                            (jwidth*r_level))++
>                           (wire_vec "_t" width (width)))],
>       (l_level+1))

> compose_xbintree node_blk width jwidth (ltree_blk,l_level) (rtree_blk,r_level) =
>   let l_in_ports= length (in_ports_ ltree_blk) - jwidth*l_level
>       r_in_ports= length (in_ports_ rtree_blk) - jwidth*r_level
>   in (make_block ((name_ node_blk)++"__"++(show width)++"_"++(show (div l_in_ports width))++"_"++
>                   (show (div r_in_ports width)))
>       ((wire_vec "i" 0 (l_in_ports+r_in_ports))++(wire_vec "j" 0 (jwidth*((max l_level r_level)+1))))
>       (wire_vec "o" 0 width)
>       [inst_block node_blk ((wire_vec "_t" 0 (2*width))++(wire_vec "j" (jwidth*l_level) jwidth)++
>                             (wire_vec "o" 0 width)),
>        inst_block ltree_blk ((wire_vec "i" 0 (width*l_in_ports))++(wire_vec "j" 0
>                                                                    (jwidth*l_level))++(wire_vec "_t" 0 width)),
>        inst_block rtree_blk ((wire_vec "i" (width*l_in_ports) r_in_ports)++
>                              (wire_vec "j"  (jwidth*(l_level-r_level)) (jwidth*r_level))++(wire_vec "_t" width (width)))],
>       (l_level+1))

> xbintree_arb block inputs = foldl1 (compose_xbintree block (length (out_ports_ block)) (jwidth block 2))
>                             (unfold (0 ==) (\x->(xtree_complete block 2 (log2_floor x), (log2_floor x)))
>                              (\x-> x - (2^(log2_floor x))) inputs)


** Parallel Prefix


Determine common ports.

> common_ports block = take ((length (in_ports_ block)) - (2*(length (out_ports_ block)))) (in_ports_ block)

> par_prefix block n = foldr (_par_prefix block (name_ block) (common_ports block) (length (out_ports_ block)))
>                      (chain0' pblk_id [] (length (out_ports_ block))) (reverse [1..n])

> _par_prefix block name_prefix common width i prev_blk =
>   let w p i = map2 (\i j->p++(show i)++"_"++(show j)) [0..((2^i)-1)] [0..(width-1)]
>   in make_block ((name_prefix)++"_par_prefix_"++(show i)++"_"++(show width)++"_"++(show (length common)))
>        (common++(concat(w "i" i))) (concat(w "o" i))
>        [inst_block prev_blk (common++(concat(w "i" (i-1)))++(concat(w "o" (i-1)))),
>         inst_block prev_blk (common++(drop ((2^(i-1))*width) (concat(w "i" i)))++(concat(w "t" (i-1)))),
>         inst_block (chain0' block common (2^(i-1)))
>         (common++(concat (transpose(w "t" (i-1))))++
>          (concat (transpose (replicate (2^(i-1)) (wires0 ("o"++(show ((2^(i-1))-1))++"_") width))))
>          {-++(drop ((2^(i-1))*width) (w "o" (i-1)))-}++(concat(transpose(drop (2^(i-1)) (w "o" i)))))]



norev ports assumed specified in front in lists of input as well as output ports.

> revio norev blk = (((intersect (in_ports_ blk) norev)++((out_ports_ blk)\\norev)),
>                    ((intersect (out_ports_ blk) norev)++((in_ports_ blk)\\norev)))

> blkname_prefix blk = dropWhile isDigit (reverse (name_ blk))

> revio_rec1 norev orgblk blk iblks = if blkname_prefix blk==blkname_prefix orgblk
>                                     then make_block ((name_ blk)++"_r") (fst (revio norev blk)) (snd (revio norev blk))
>                                            (map (\iblk->inst_block iblk ((fst (revio norev blk))++
>                                                                          (snd (revio norev blk)))) iblks)
>                                     else blk -- make_block ((name_ blk)++"_r") (in_ports_ blk) (out_ports_ blk) iblks

> revio_rec norev blk = trav_blocks (revio_rec1 norev blk) id id blk

Current status: Implementation of demux motivated revio_rec which was
intended to reverse not just trees but chains as well (and perhaps
others (like fft?)). But the way wires are connected in xtree and
chain are different. How to resolve? Related issue: add support to
xtree for common wires to left and right subtrees (and node)?
