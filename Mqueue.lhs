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


> module Mqueue where

> import Data.List

> import Flo
> import Lib
> import FSM
> import Comb
> import Test
> import Misc

*** Demuxl
    Demux lower is not really a demux but related. Just as an n output demux
    outputs the input on output wire i (i being the control input), a demuxl
    outputs the input on /all/ output wires i and lower.

**** Truth table for demuxl2

     The demuxl analogue of demux2 is demuxl2:

     | i | j |   | o0 | o1 |
     |---+---+---+----+----|
     | 0 | 0 |   |  0 |  0 |
     | 0 | 1 |   |  0 |  0 |
     | 1 | 0 |   |  1 |  0 |
     | 1 | 1 |   |  1 |  1 |

> demuxl2 = make_pblock "demuxl2" ["i", "j"] ["o0","o1"] "  assign o0 = i;\n  assign o1 = i & j;\n"

demuxl2n, as implemented below is somewhat of a hack compared to "proper" way of
doing it which would involve reversing inputs of structure produced by
xbintree_arb but latter seems to assume all block outputs are connections to
parents (only inputs can be "horizontal" connections) which is a shortcoming
which prevents connection reversal using rec_revio (which also may have bugs).

> demuxl2n levels = foldr demuxl2n_1 pblk_id (reverse [1..levels])

> demuxl2n_1 level tree_blk =
>   make_block ((name_ demuxl2)++"n_"++(show level)) (["i"]++(wires0 "j" level)) (wires0 "o" (2^level))
>                ((inst_block demuxl2 (["i"]++["j"++(show (level-1))]++(wires0 "_t" 2))):
>                 (map (\i->inst_block tree_blk ((wires0 "_t" 1)++
>                                                (wires0 "j" (level-1))++
>                                                (wires "o" (i*(2^(level-1))) (2^(level-1))))) [0,1]))



*** Mqueue

    + No need for twos complement of shift amount for second rotnet, just
      reversing its data inputs as well as outputs does (it seems) the trick.

    + Rename andor to bcast or expand(er) or ...?

    mqueue0 m words bits constructs a "multiqueue" (FIFO) which can, each clock
    cycle, read or read (both can occur in the same clock cycle) upto $2^m$
    words each of size /bits/ bits.

*** DONE modify rotnet data wires using dat -<2012-05-15 Tue>

Hack to avoid mux2_2 name clash.

> _mux2 = make_pblock "_mux2" ["i0", "i1", "j"] ["o"] "  assign o = (j==0)?i0:i1;\n"

> __mux2 = make_pblock "__mux2" ["i0", "i1", "j"] ["o"] "  assign o = (j==0)?i0:i1;\n"

> mqueue0 m words bits =
>   let dat p = (concat . transpose) (map ((flip wires0) (2^m)) (wires0 p bits))
>   in make_block ("mqueue_"++(show m)++"_"++(show words)++"_"++(show bits)) 
>        (["clk","reset","rd","wr"]++(wires0 "iwords" m)++(wires0 "owords" m)++(dat "din")) (["empty","full"]++(dat "dout"))
>        [inst_block {-wr offset-} (chain' adddffen adddffen'0 ["clk","reset","en"] ["cin","cout"] m)
>         (["clk","reset","wren"]++(wires0 "iwords" m)++(wires0 "wroff" m)++["wrcout"]),
>         inst_block gate_and2 ["wr","full_","wren"] {-change to deal with full (done)-},
>         inst_block {-din rotate-} (chain' (rotnet m) (rotnet m) (wires0 "u" m) [] bits)
>         ((dat "din")++(wires0 "wroff" m)++(dat "tdin")),
>         inst_block {-wr expander-} (lte m) (["wren"]++(reverse (wires0 "iwords" m))++(wires0 "twr" (2^m))),
>         inst_block {-wr rotate-} (rotnet m) ((wires0 "twr" (2^m))++(wires0 "wroff" m)++(wires0 "uwr" (2^m))),
>         inst_block {-rd offset-} (chain' adddffen adddffen'0 ["clk","reset","en"] ["cin","cout"] m)
>         (["clk","reset","rden"]++(wires0 "owords" m)++(wires0 "rdoff" m)++["rdcout"]),
>         inst_block gate_and2 ["rd","empty_","rden"] {-change to deal with empty (done)-},
>         inst_block {-dout rotate-} (chain' (rotnet m) (rotnet m) (wires0 "u" m) [] bits)
>         ((reverse (dat "tdout"))++(wires0 "trdoff" m)++(reverse (dat "dout"))),
>         inst_block {-rd expander-} (lte m) (["rden"]++(reverse (wires0 "owords" m))++(wires0 "trd" (2^m))),
>         inst_block {-rd rotate-} (rotnet m) ((wires0 "trd" (2^m))++(wires0 "rdoff" m)++(wires0 "urd" (2^m))),
>         inst_block (chain' dff dff ["clk","reset"] [] m) (["clk", "reset"]++(wires0 "rdoff" m)++(wires0 "trdoff" m)),
>         inst_block {-queues-} (chain' (queue words bits) (queue words bits) ["clk","reset"] [] (2^m))
>         (["clk","reset"]++(wires0 "uwr" (2^m))++(wires0 "urd" (2^m))++(concatMap((flip wires0) (2^m)) (wires0 "tdin" bits))
>          ++(wires0 "full" (2^m))++(wires0 "empty" (2^m))++(concatMap ((flip wires0) (2^m)) (wires0 "tdout" bits))),
>         inst_block (fst (xbintree_arb gate_and2 (2^m))) ((wires0 "empty" (2^m))++["empty"]),
>         inst_block (fst (xbintree_arb gate_or2 (2^m))) ((wires0 "full" (2^m))++["full"]),
>         inst_block gate_invert ["empty","empty_"], inst_block gate_invert ["full","full_"]]

> test_mqueue0 m size bits = tb_gen2 (tv_reorder ((in_ports_ (mqueue0 m size bits))\\["clk","reset"])
>                                    (foldr1 tvc [(["wr"],[0,1,1,1,1,0,0,0,0,0,0,0,0,0,0]),
>                                                 (["rd"],[0,0,0,0,0,0,1,1,1,1,1,1,1,1,0]),
>                                                 ((reverse (wires0 "iwords" m)),[0,0,1,1,0,0,0,0,0,0,0,0,0,0,0]),
>                                                 ((reverse (wires0 "owords" m)),[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]),
>                                                 ((reverse.concat.transpose)(map ((flip wires0) (2^m)) (wires0 "din" bits)),
>                                                   [0,0xabcdef01,0x0123456789abcdef,0x123456789abcdef0,0x23456789,0,0,0,0,0,0,0,0,0,0])]))
>                           (mqueue0 m size bits) tb_seq
>                           [("i0",map (\i->i++"0") (wires "din" 0 32)),("i1",map (\i->i++"1") (wires "din" 0 32)),
>                            ("o0",map (\i->i++"0") (wires "dout" 0 32)),("o1",map (\i->i++"1") (wires "dout" 0 32))]

**** DONE chain' variant (maybe chain1 like foldr1) that does not take argument for "lsb" logic block or the "neighboring signals" argument <2012-05-11 Fri>

**** Updates to modified queues below <2013-07-06 Sat>

     So further thinking and experimentation has led to the following
     modification for queue block: use wad_reg for wr addr but rad for rd
     adder. This enables fwft behaviour while retaining previous (somewhat
     elegant) empty/full logic. Also above can be converted as in mqueue2
     below into non-fwft mode. Also, need for trdoff is eliminated.

**** Modified mqueue

     Modification to generate empty and full based on owords and iwords inputs
     (and internal emptyx and fullx signals) respectively. Manner of doing so
     is a bit funky, but seems neat and efficient. Out of the 2^n emptyx
     signals, 2^n-1 are summed with bit_sum_mer, which are added to owords,
     with adder cin being fed the remaining cin. Cout of above sum is the
     empty signal. Similarly full is computed from iwords and fullx. Note that
     iwords and owords numbers are one less than they mean. <2013-06-29 Sat>

     Using chain'' to avoid name clash on fa_2. <2013-06-29 Sat>

     Queue mem size seems to be (2^m)*words*bits. <2013-08-18 Sun> 

> mqueue1 m words bits =
>   let dat p = (concat . transpose) (map ((flip wires0) (2^m)) (wires0 p bits))
>   in make_block ("mqueue1_"++(show m)++"_"++(show words)++"_"++(show bits)) 
>        (["clk","reset","rd","wr"]++(wires0 "iwords" m)++(wires0 "owords" m)++(dat "din")) (["empty","full"]++(dat "dout"))
>        [inst_block {-wr offset-} (chain' adddffen adddffen'0 ["clk","reset","en"] ["cin","cout"] m)
>         (["clk","reset","wren"]++(wires0 "iwords" m)++(wires0 "wroff" m)++["wrcout"]),
>         inst_block gate_and2 ["wr","full_","wren"] {-change to deal with full (done)-},
>         inst_block {-din rotate-} (chain' (rotnet m) (rotnet m) (wires0 "u" m) [] bits)
>         ((dat "din")++(wires0 "wroff" m)++(dat "tdin")),
>         inst_block {-wr expander-} (lte m) (["wren"]++(reverse (wires0 "iwords" m))++(wires0 "twr" (2^m))),
>         inst_block {-wr rotate-} (rotnet m) ((wires0 "twr" (2^m))++(wires0 "wroff" m)++(wires0 "uwr" (2^m))),
>         inst_block {-rd offset-} (chain' adddffen adddffen'0 ["clk","reset","en"] ["cin","cout"] m)
>         (["clk","reset","rden"]++(wires0 "owords" m)++(wires0 "rdoff" m)++["rdcout"]),
>         inst_block gate_and2 ["rd","empty_","rden"] {-change to deal with empty (done)-},
>         inst_block {-dout rotate-} (chain' (rotnet m) (rotnet m) (wires0 "u" m) [] bits)
>         ((reverse (dat "tdout"))++(wires0 "rdoff" m)++(reverse (dat "dout"))),
>         inst_block {-rd expander-} (lte m) (["rden"]++(reverse (wires0 "owords" m))++(wires0 "trd" (2^m))),
>         inst_block {-rd rotate-} (rotnet m) ((wires0 "trd" (2^m))++(wires0 "rdoff" m)++(wires0 "urd" (2^m))),
>         --inst_block (chain' dff dff ["clk","reset"] [] m) (["clk", "reset"]++(wires0 "rdoff" m)++(wires0 "trdoff" m)),
>         inst_block {-queues-} (chain' (queue words bits) (queue words bits) ["clk","reset"] [] (2^m))
>         (["clk","reset"]++(wires0 "uwr" (2^m))++(wires0 "urd" (2^m))++(concatMap((flip wires0) (2^m)) (wires0 "tdin" bits))
>          ++(wires0 "full" (2^m))++(wires0 "empty" (2^m))++(concatMap ((flip wires0) (2^m)) (wires0 "tdout" bits))),
>         inst_block (bit_sum_mers' m) ((wires0 "empty" ((2^m)-1))++(wires0 "emptys" m)),
>         inst_block (chain'' "_" fa fa0 [] ["cin","cout"] m)
>         ((wires0 "owords" m)++(wires0 "emptys" m)++["empty"++(show ((2^m)-1))]++(wires0 "empty_owords" m)++["empty"]),
>         inst_block (bit_sum_mers' m) ((wires0 "full" ((2^m)-1))++(wires0 "fulls" m)),
>         inst_block (chain'' "_" fa fa0 [] ["cin","cout"] m)
>         ((wires0 "iwords" m)++(wires0 "fulls" m)++["full"++(show ((2^m)-1))]++(wires0 "full_iwords" m)++["full"]),
>         {-inst_block (fst (xbintree_arb gate_and2 (2^m))) ((wires0 "empty" (2^m))++["empty"]),
>         inst_block (fst (xbintree_arb gate_or2 (2^m))) ((wires0 "full" (2^m))++["full"]),-}
>         inst_block gate_invert ["empty","empty_"], inst_block gate_invert ["full","full_"]{-,
>         inst_block one ("_1"),inst_block one ("_0")-}]


**** Further modified mqueue1 (non-fwft)

     dlfa_zd requires a non-fwft interface for input queue. So rather than
     change dlfa_zd control logic, following is used.

     Non-fwft variant mqueue is made by simply registering dout, with rden used
     as load enable.

> mqueue2 m words bits =
>   let dat p = (concat . transpose) (map ((flip wires0) (2^m)) (wires0 p bits))
>   in make_block ("mqueue2_"++(show m)++"_"++(show words)++"_"++(show bits)) 
>        (["clk","reset","rd","wr"]++(wires0 "iwords" m)++(wires0 "owords" m)++(dat "din")) (["empty","full"]++(dat "dout"))
>        [inst_block (mqueue1 m words bits)
>         ((["clk","reset","rd","wr"]++(wires0 "iwords" m)++(wires0 "owords" m)++(dat "din"))++
>          (["empty","full"]++(dat "_dout"))),
>         inst_block gate_and2 ["empty_","rd","ren"], inst_block gate_invert ["empty","empty_"],
>         inst_block {-dout reg-} (chain'' "__" dfrl dfrl ["clk","reset","load"] [] ((2^m)*bits))
>         (["clk","reset","ren"]++(dat "_dout")++(dat "dout"))]
  

test_mqueue 1 1 3 4

> test_mqueue m tag_size words bits =
>   let rep n x = replicate n x
>   in tb_gen2 (tv_reorder ((in_ports_ (mqueue m tag_size words bits))\\["clk","reset"])
>                (foldr1 tvc [(["wr"],([0]++(rep 16 1)++[0]++(rep 16 0)++[0])),
>                             (["wr_done"],([0]++(rep 16 0)++[1]++(rep 16 0)++[0])),
>                             (["rd"],([0]++(rep 16 0)++[0]++(rep 8 1)++(rep 8 0)++[0])),
>                             ((reverse (wires0 "tag" tag_size)),([0]++(rep 4 0)++(rep 4 0)++(rep 4 1)++(rep 4 1)++[0]++(rep 16 0)++[0])),
>                             ((reverse (wires0 "iwords" m)),([0]++(rep 16 0)++[0]++(rep 16 0)++[0])),
>                             ((reverse (wires0 "owords" m)),([0]++(rep 16 0)++[0]++(rep 8 1)++(rep 8 0)++[0])),
>                             ((reverse.concat.transpose) (map (\w->wires0 (w++"_") (2^m)) (wires0 "din" bits)),
>                             ([0]++[0x0..0xf]++[0]++(rep 16 0)++[0]))]))
>                           (mqueue m tag_size words bits) tb_seq
>                           [("i0",map (\i->i++"_0") (wires "din" 0 4)),("i1",map (\i->i++"_1") (wires "din" 0 4)),
>                            ("o0",map (\i->i++"_0") (wires "dout" 0 4)),("o1",map (\i->i++"_1") (wires "dout" 0 4))]

> test_mqueue2 m tag_size words bits =
>   let rep n x = replicate n x
>   in tb_gen2 (tv_reorder ((in_ports_ (mqueue m tag_size words bits))\\["clk","reset"])
>                (foldr1 tvc [(["wr"],([0]++(rep 16 1)++[0]++(rep 16 0)++[0])),
>                             (["wr_done"],([0]++(rep 16 0)++[1]++(rep 16 0)++[0])),
>                             (["rd"],([0]++(rep 16 0)++[0]++(rep 8 1)++(rep 8 0)++[0])),
>                             ((reverse (wires0 "tag_" tag_size)),([0]++(rep 4 0)++(rep 4 1)++(rep 4 2)++(rep 4 3)++[0]++(rep 16 0)++[0])),
>                             ((reverse (wires0 "iwords" m)),([0]++(rep 16 0)++[0]++(rep 16 0)++[0])),
>                             ((reverse (wires0 "owords" m)),([0]++(rep 16 0)++[0]++(rep 8 1)++(rep 8 0)++[0])),
>                             ((reverse.concat.transpose) (map (\w->wires0 (w++"_") (2^m)) (wires0 "din" bits)),
>                             ([0]++[0x0..0xf]++[0]++(rep 16 0)++[0]))]))
>                           (mqueue m tag_size words bits) tb_seq
>                           [("i0",map (\i->i++"_0") (wires "din" 0 4)),("i1",map (\i->i++"_1") (wires "din" 0 4)),
>                            ("o0",map (\i->i++"_0") (wires "dout" 0 4)),("o1",map (\i->i++"_1") (wires "dout" 0 4))]


> test_mqueue3 m tag_size words bits =
>   let rep n x = replicate n x
>   in tb_gen2 (tv_reorder ((in_ports_ (mqueue m tag_size words bits))\\["clk","reset"])
>                (foldr1 tvc [(["wr"],([0]++(rep 16 1)++[0]++(rep 16 0)++[0])),
>                             (["wr_done"],([0]++(rep 16 0)++[1]++(rep 16 0)++[0])),
>                             (["rd"],([0]++(rep 16 0)++[0]++(rep 8 1)++(rep 8 1)++[0])),
>                             ((reverse (wires0 "tag_" tag_size)),([0]++(rep 4 0)++(rep 4 1)++(rep 4 2)++(rep 4 3)++[0]++(rep 16 0)++[0])),
>                             ((reverse (wires0 "iwords" m)),([0]++(rep 16 0)++[0]++(rep 16 0)++[0])),
>                             ((reverse (wires0 "owords" m)),([0]++(rep 16 0)++[0]++(rep 8 1)++(rep 8 0)++[0])),
>                             ((reverse.concat.transpose) (map (\w->wires0 (w++"_") (2^m)) (wires0 "din" bits)),
>                             ([0]++[0x0..0xf]++[0]++(rep 16 0)++[0]))]))
>                           (mqueue m tag_size words bits) tb_seq
>                           [("i0",map (\i->i++"_0") (wires "din" 0 4)),("i1",map (\i->i++"_1") (wires "din" 0 4)),
>                            ("o0",map (\i->i++"_0") (wires "dout" 0 4)),("o1",map (\i->i++"_1") (wires "dout" 0 4))]

*** Mqueue with pipe stage <2013-10-24 Thu>

    Pipe stage added to front of mqueue to reduce mqueue latency.


> mqueue1_pipe m words bits =
>   let dat p = (concat . transpose) (map ((flip wires0) (2^m)) (wires0 p bits))
>   in make_block ("mqueue1_pipe_"++(show m)++"_"++(show words)++"_"++(show bits))
>        (["clk","reset","rd","wr"]++(wires0 "iwords" m)++(wires0 "owords" m)++(dat "din")) (["empty","full"]++(dat "dout"))
>        [inst_block (pipe_stage ((fromIntegral m)+((fromIntegral (2^m))*bits)))
>         (["clk","reset","_1","wr","full1_"]++(wires0 "iwords" m)++(dat "din")++["irq0","ordy0","en0"]++
>          (wires0 "iwords0_" m)++(dat "din0_")),
>         inst_block (mqueue1 m words bits)
>         (["clk","reset","rd","ordy0"]++(wires0 "iwords0_" m)++(wires0 "owords" m)++(dat "din0_")++
>          ["empty","full1"]++(dat "dout")),
>         inst_block gate_invert ["full1","full1_"], inst_block gate_invert ["irq0","full"],inst_block one ["_1"]]
