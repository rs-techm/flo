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


> module Mstack where

> import Data.List

> import Flo
> import Lib
> import Comb
> import Test
> import Misc

> comp_range_l' size thresh = if (size==0)
>                             then one 
>                             else make_block ("comp_range_l_"++(show size)++(show thresh))
>                                    (wire_vec "i" 0 size) ["o"]
>                                    [inst_block (comp_range_l (size-1) (div thresh 2))
>                                     ((wire_vec "i" 0 (size-1))++["t"]),
>                                     inst_block (if (mod thresh 2)==0 then gate_or2 else gate_and2) 
>                                     [("i"++(show size)),"t","o"]]

> comp_range_ge size thresh = chain "ge" [] ["i0","o"] one
>                             (map (\b->if (head b)=='0' then (b,gate_or2) else (b,gate_and2))
>                              ((init . tails) (show_num_base_size 2 size thresh)))

> comp_range_l size thresh = make_block ((name_ (comp_range_ge size thresh))++"_inv")
>                            (in_ports_ (comp_range_ge size thresh)) (out_ports_ (comp_range_ge size thresh))
>                            [inst_block (comp_range_ge size thresh)
>                             (replace_elem (io_ports (comp_range_ge size thresh)) "o" "t"),
>                             inst_block gate_invert ["t","o"]]

> maj2 = make_block "maj2" ["i0","i1","i2"] ["o"]
>        [inst_block gate_and2 ["i0","i1","t01"], inst_block gate_and2 ["i1","i2","t12"],
>         inst_block gate_and2 ["i2","i0","t20"], inst_block gate_or2 ["t01","t12","t"],
>         inst_block gate_or2 ["t","t20","o"]]


> gate_1i gate = make_block ((name_ gate)++"_i1") ["i0","i1"] ["o"]
>                [inst_block gate ["i0","t","o"], inst_block gate_invert ["i1","t"]]


> comp_range_le size thresh = chain "le" [] ["i0","o"] one
>                             (map (\b->if (head b)=='1' then (b,(gate_1i gate_or2)) else (b,(gate_1i gate_and2)))
>                              ((init . tails) (show_num_base_size 2 size thresh)))

> comp_range_g size thresh = make_block ((name_ (comp_range_le size thresh))++"_inv")
>                            (in_ports_ (comp_range_le size thresh)) (out_ports_ (comp_range_le size thresh))
>                            [inst_block (comp_range_le size thresh)
>                             (replace_elem (io_ports (comp_range_le size thresh)) "o" "t"),
>                             inst_block gate_invert ["t","o"]]

> comp_range_leg size tle tg = make_block ("leg_"++(show_num_base_size 2 size tle)++"_"++(show_num_base_size 2 size tg))
>                              (in_ports_ (comp_range_le size tle)) (out_ports_ (comp_range_le size tle))
>                              [inst_block (comp_range_le size tle)
>                               (replace_elem (io_ports (comp_range_le size tle)) "o" "t1"),
>                               inst_block (comp_range_g size tg)
>                               (replace_elem (io_ports (comp_range_le size tg)) "o" "t2"),
>                               inst_block gate_and2 ["t1","t2","o"]]

> comp_range_gel size tl tge = make_block ("gel_"++(show_num_base_size 2 size tge)++"_"++(show_num_base_size 2 size tl))
>                              (in_ports_ (comp_range_ge size tge)) (out_ports_ (comp_range_ge size tl))
>                              [inst_block (comp_range_ge size tge)
>                               (replace_elem (io_ports (comp_range_ge size tge)) "o" "t1"),
>                               inst_block (comp_range_l size tl)
>                               (replace_elem (io_ports (comp_range_ge size tl)) "o" "t2"),
>                               inst_block gate_and2 ["t1","t2","o"]]

> stacki size bits m id = make_block ("stacki_"++(show m)++"_"++(show id))
>                         (["clk","reset","push","pop","oflow"]++(wire_vec "cur" 0 m)++(wire_vec "new" 0 m)++
>                          (wire_vec "i" 0 bits))
>                         (["pushi","popi"]++(wire_vec "o" 0 bits))
>                         [inst_block gate_invert ["oflow","oflow_"],
>                          inst_block (comp_range_l m id) ((wire_vec "cur" 0 m)++["tl"]),
>                          inst_block (comp_range_ge m id) ((wire_vec "new" 0 m)++["tge"]),
>                          inst_block maj2 ["tl","tge","oflow","_pushi"], inst_block gate_and2 ["_pushi","push","pushi"],
>                         -- inst_block (comp_range_l m id) ((wire_vec "new" 0 m)++["tl_"]),
>                         -- inst_block (comp_range_ge m id) ((wire_vec "cur" 0 m)++["tge_"]),
>                         -- inst_block maj2 ["tl_","tge_","oflow_","_popi"],
>                          inst_block gate_invert ["_pushi","_popi"],
>                          inst_block gate_and2 [ "_popi","pop","popi"],
>                          inst_block (stack size bits) (["clk","reset","pushi","popi"]++(wire_vec "i" 0 bits)++
>                                                        (wire_vec "o" 0 bits))]


** Mstack

   *Inputs* /clk/, /reset/, /push/, /pop/, /k[m]/, /i[bits]/

   *Outputs* /o[bits]/

   *Parameters* /m/, /size/, /bits/

   Mstack can store upto $2^m\times size$ data items, each having
   /bits/ number of bits. Mstack can perform either upto /2^m/ push
   operations or upto /2^m/ pop operations in a single clock cycle.

*** Structure and Operation


    [figure]

    /2^m/ instantiations of the stack block (each supplied with
    parameters /size/ and /bits/) are used.

    Number of words pushed or popped can vary from 1 to 2^m and is
    specified by input /k/. Since /m/-bit /k/ varies from 0 to 2^m-1,
    /k+1/ words are pushed or popped.

    Whenever an operation is to be performed (push or pop is asserted)
    the /m/-bit adder/subtracter output, /new/, is stored in the
    offset counter register, whose output is /cur/.

    To cin of adder/subtracter 0 is applied while adding, and 1 while
    subtracting, so that /k+1/ is added or subtracted, thus pushing or
    popping /k+1/ words.

    If offset counter contains /cur/, input /k/ plus 1 is /l/, then
    during a push operation, the input on wires /i_0/ to
    /i_{bits\times l-1}/ is stored in the /l/ stacks from /(cur+1) \bmod
    m/ to  /(cur+l) \bmod m/ and during a pop operation, words from
    stacks /(cur-l+1) \bmod m/ to /cur \bmod m/ are readout to outputs
    /cur_0/ to /cur_{bits\times l-1}/.

    At times, the interval of participating stacks can
    /wraparound/. The wraparound is detected in a simple manner as
    /cout/ of the adder/subtracter. While it is reasonable to expect
    above signal to detect wraparound during addition, it is
    interesting that the /cout/ does so during subtraction as well
    (no need to compute an (arithmetic) overflow signal). 

    A push operation involves stacks from /(cur+1) \bmod m/ to /new
    \bmod m/ while a pop operation involves stacks from /(new+1) \bmod
    m/ to /cur \bmod m/. Since a stack is (potentially) involved
    either in a push or a pop, for each stack /\_popi/ is the complement
    of /\_pushi/.

    For a push operation, rotation of input wire /j/ to /(j+k+1)\bmod
    m/ = /(cur+1)\bmod m/ is required, but rotation by /cur/ is
    specified. In order to avoid specifying rotation by /cur+1/ which
    would require an additional incrementer, the inputs to the rotnet
    are shifted by one.

    Similarly, for a pop operation, rotation of stack output on wire
    /j/ to /(j-(k+1))\bmod m/ is required, but rotation by /cur/ is
    specified[20]. In order to avoid specifying rotation by /cur+1/ which
    would require an additional incrementer, the inputs to the rotnet
    are shifted by one.

[20] Actually /new/ should be used, but the value of /new/ is required
in the next clock cycle by which time /new/ has become /cur/. Thus
/cur/ is used.

    To determine for each stack if it is within the bounds of /cur/
    and /new/ the previously developed circuit is used. The logic
    could be made more efficient if the binary tree form is used,
    which could supply required input to each stack.

    Each of the /m/ stacks uses a counter inside. This seems redundant
    (as it seems values of all counters are atmost off by one of each
    other at any time) and it may be possible to replace the /m/
    counters by one or two.



> mstack m size bits = make_block ("mstack__"++(show m)) (["clk","reset","push","pop"]++(wire_vec "k" 0 m)++
>                                                         (wire_vec "i" 0 ((2^m)*bits)))
>                      ((wire_vec "new_" 0 m)++(wire_vec "cur_" 0 m)++(wire_vec "pushi" 0 (2^m))++(wire_vec "popi" 0 (2^m))
>                       ++(wire_vec "o" 0 ((2^m)*bits)))
>                      ([inst_block gate_or2 ["push","pop","en"],
>                        inst_block (addsubdffen''v m) (["clk","reset","en","pop"]++
>                                                      (wire_vec "k" 0 m)++(wire_vec "new_" 0 m)++
>                                                      (wire_vec "cur_" 0 m)++["oflow"])]++
>                       (map (\i-> inst_block (stacki size bits m i)
>                             (["clk","reset","push","pop","oflow"]++(wire_vec "cur_" 0 m)++(wire_vec "new_" 0 m)++
>                              (wire_vec "ti" (bits*i) bits)++["pushi"++(show i)]++["popi"++(show i)]++
>                              (wire_vec "to" (bits*i) bits))) [0..((2^m)-1)])++
>                       [inst_block (chain' (rotnet m) (rotnet m) (wire_vec "u" 0 m) [] bits)
>                        ((rotatel (fromIntegral (bits*((2^m)-1))) (wire_vec "i" 0 (bits*(2^m))))++(wire_vec "cur_" 0 m)++
>                         (wire_vec "ti" 0 (bits*(2^m))))]++
>                       [inst_block (chain' dff dff ["clk","reset"] [] m) (["clk","reset"]++(wire_vec "cur_" 0 m)++
>                                                                          (wire_vec "cur_reg_" 0 m))]++
>                       [inst_block (chain' (rotnet m) (rotnet m) (wire_vec "u" 0 m) [] bits)
>                        ((rotatel (fromIntegral (bits*((2^m)-1))) (reverse (wire_vec "to" 0 (bits*(2^m)))))++
>                         (wire_vec "cur_" 0 m)++(reverse (wire_vec "o" 0 (bits*(2^m)))))])

> --test_mstack::Int->Int->Int->[Char]
> test_mstack m size bits = tb_gen2 (tv_reorder ((in_ports_ (mstack m size bits))\\["clk","reset"])
>                                    (tvc (tvc (tvc (["push"],[0,1,1,1,1,1,1,1,0,0,0,0,0,0,0]) 
>                                               (["pop"],[0,0,0,0,0,0,0,0,1,1,1,1,1,1,1]))
>                                          ((reverse (wire_vec "k" 0 m)),[0,0,0,0,0,0,0,0, 3,2,0,0,0,0,0]))
>                                           --take 15 (repeat (2^(fromIntegral 1)-0))))
>                                     (((unfold (== -1) (\i->"i"++(show i)) (\i->i-1) ((2^m)*bits-1))),
>                                      [0,0o0001,0o0002,0o0003,0o0004,0o0005,0o0006,0o0007,0o0001,0o0002,0o0003,0o0004,
>                                       0o0005,0o0006,0o0007])))
>                           (mstack m size bits) tb_seq
>                           ([("din",(wire_vec "i" 0 ((2^m)*bits))),
>                             ("dout",(wire_vec "o" 0 ((2^m)*bits)))]++
>                            (concatMap (\i->[("din"++(show i),wire_vec "i"(bits*i) bits),
>                                             ("dout"++(show i),wire_vec "o" (bits*i) bits)]) [0..((2^m)-1)])++
>                            [("cur",(wire_vec "cur_" 0 m)),("new",(wire_vec "new_" 0 m))])

> -- main = let dut = mstack 2 16 3
> --        in (putStr ((fl__ver dut)++(test_mstack 2 16 3)))
