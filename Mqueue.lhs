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

*** TODO
    - expander 0 when input 0
    - check expander rotnet control bits ordering

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

**** TODO Clean up lte so that inputs don't have to be reversed <2012-05-11 Fri>

**** TODO Replace inst_block by iblk? <2012-05-11 Fri>

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

***** TODO Rewrite mqueue2 in terms of mqueue1. <2013-07-06 Sat>

> {-mqueue2 m words bits =
>   let dat p = (concat . transpose) (map ((flip wires0) (2^m)) (wires0 p bits))
>   in make_block ("mqueue2_"++(show m)++"_"++(show words)++"_"++(show bits)) 
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
>         ((reverse (dat "tdout"))++(wires0 "rdoff" m)++(reverse (dat "udout"))),
>         inst_block {-dout reg-} (chain'' "_" dfrl dfrl ["clk","reset","load"] [] ((2^m)*bits))
>         (["clk","reset","rden"]++(dat "udout")++(dat "dout")),
>         inst_block {-rd expander-} (lte m) (["rden"]++(reverse (wires0 "owords" m))++(wires0 "trd" (2^m))),
>         inst_block {-rd rotate-} (rotnet m) ((wires0 "trd" (2^m))++(wires0 "rdoff" m)++(wires0 "urd" (2^m))),
>         --inst_block (chain' dff dff ["clk","reset"] [] m) (["clk", "reset"]++(wires0 "rdoff" m)++(wires0 "trdoff" m)),
>         inst_block {-queues-} (chain' (queue words bits) (queue words bits) ["clk","reset"] [] (2^m))
>         (["clk","reset"]++(wires0 "uwr" (2^m))++(wires0 "urd" (2^m))++(concatMap((flip wires0) (2^m)) (wires0 "tdin" bits))
>          ++(wires0 "full" (2^m))++(wires0 "empty" (2^m))++(concatMap ((flip wires0) (2^m)) (wires0 "tdout" bits))),
>         inst_block (bit_sum_mers m) ((wires0 "empty" ((2^m)-1))++(wires0 "emptys" m)),
>         inst_block (chain'' "_" fa fa0 [] ["cin","cout"] m)
>         ((wires0 "owords" m)++(wires0 "emptys" m)++["empty"++(show ((2^m)-1))]++(wires0 "empty_owords" m)++["empty"]),
>         inst_block (bit_sum_mers m) ((wires0 "full" ((2^m)-1))++(wires0 "fulls" m)),
>         inst_block (chain'' "_" fa fa0 [] ["cin","cout"] m)
>         ((wires0 "iwords" m)++(wires0 "fulls" m)++["full"++(show ((2^m)-1))]++(wires0 "full_iwords" m)++["full"]),
>         {-inst_block (fst (xbintree_arb gate_and2 (2^m))) ((wires0 "empty" (2^m))++["empty"]),
>         inst_block (fst (xbintree_arb gate_or2 (2^m))) ((wires0 "full" (2^m))++["full"]),-}
>         inst_block gate_invert ["empty","empty_"], inst_block gate_invert ["full","full_"]{-,
>         inst_block one ("_1"),inst_block one ("_0")-}]-}

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
  

**** TODO <2013-06-28 Fri>
     Rename "one" and "zero" (signals from one and zero blocks) to "_1" and "_0"?

*** Mqueue variant for PCIE input

**** TODO
     Rename mqueue below to something more appropriate. Also, create new mqueue
     based on above mqueue as it uses newer approach compared to older mqueue0? <2013-06-10 Mon>

**** TODO Create new 

> mq_addr add_size count_size =
>   make_block ("mq_addr_"++(show add_size)++"_"++(show count_size))
>   (["clk","reset","en"]++(wires0 "words" add_size))
>   ((wires0 "off" add_size)++(wires0 "a0_" count_size)++(wires0 "a1_" count_size))
>   [inst_block {-offset-} (chain' adddffen adddffen'0 ["clk","reset","en"] ["cin","cout"] add_size)
>    (["clk","reset","en"]++(wires0 "words" add_size)++(wires0 "off" add_size)++["cout_inc"]),
>    inst_block {-count-} (chain' incdfre' incdfre'0 ["clk","reset","en"] ["cin","cout"] count_size)
>    (["clk","reset","en","cout_inc","cout"]++(wires0 "a1_" count_size)++(wires0 "a0_" count_size))]

> __mqueue1_1 m tag_size words =
>   let words' = words-tag_size
>       _addr = map (\w->wires0 (w++"_") (2^tag_size)) ((wires0 "off" m)++(wires0 "a0_" words')++(wires0 "a1_" words'))
>   in make_block ("__mqueue1_1_"++(show m)++"_"++(show tag_size)++"_"++(show words))
>        (["clk","reset","en"]++(wires0 "tag" tag_size)++(wires0 "words" m))
>        ((wires0 "off" m)++(wires0 "a0_" words')++(wires0 "a1_" words'))
>        [inst_block (demux2n tag_size) (["en"]++(wires0 "tag" tag_size)++(wires0 "en" (2^tag_size))), 
>         inst_block (chain0' (mq_addr m words') (["clk","reset"]++(wires0 "words" m)) (2^tag_size))
>         (["clk","reset"]++(wires0 "en" (2^tag_size))++(wires0 "words" m)++(concat _addr)),
>         inst_block (chain0' (fst (xbintree_arb _mux2 (2^tag_size))) (wires0 "j" tag_size) (m+2*words'))
>         ((concat(transpose _addr))++(wires0 "tag"tag_size)++(wires0"off" m)++(wires0 "a0_" words')++(wires0 "a1_" words'))]

> _mqueue1 m tag_size words bits =
>   let words' = words-tag_size
>       dat p = (concat . transpose) (map (\w->wires0 (w++"_") (2^m)) (wires0 p bits))
>       _addr p = map (\w->wires0 (w++"_") (2^m)) (wires0 p words')
>   in make_block ("_mqueue1_"++(show m)++"_"++(show tag_size)++"_"++(show words)++"_"++(show bits)) 
>        (["clk","reset","rw"]++(wires0 "tag" tag_size)++(wires0 "words" m)++(dat "di"))
>        ((wires0 "rw" (2^m))++(concat (transpose (_addr "a")))++(dat "do"))
>        [inst_block {-di rotate-} (chain' (rotnet m) (rotnet m) (wires0 "u" m) [] bits)
>         ((dat "di")++(wires0 "off" m)++(dat "do")),
>         inst_block {-expander-} (lte m) (["rw"]++(reverse (wires0 "words" m))++(wires0 "trw" (2^m))),
>         inst_block {-rw rotate-} (rotnet m) ((wires0 "trw" (2^m))++(wires0 "off" m)++(wires0 "rw" (2^m))),
>         inst_block {-addr-} (__mqueue1_1 m tag_size words)
>         (["clk","reset","en"]++(wires0 "tag" tag_size)++(wires0 "words" m)++
>          (wires0 "off" m)++(wires0 "_a0_" words')++(wires0 "_a1_" words')),
>         inst_block {--} (gte m) ((reverse (wires0 "off" m))++(wires0 "j" (2^m))),
>         inst_block {-muxes-} (chain0' (chain0' mux2 ["j"] words') ((wires0' "i0" words')++(wires0' "i1" words')) (2^m))
>         ((wires0 "_a1_" words')++(wires0 "_a0_" words')++(wires0 "j" (2^m))++(concat (_addr "a"))),
>         inst_block pblk_id ["rw","en"] {-change to deal with full/empty-}]

> _mqueue2 m words bits =
>   let dat p = (concat . transpose) (map (\w->wires0 (w++"_") (2^m)) (wires0 p bits))
>       addr p =  (concat . transpose) (map (\w->wires0 (w++"_") (2^m)) (wires0 p words))
>   in make_block ("_mqueue2_"++(show m)++"_"++(show words)++"_"++(show bits)) 
>        (["clk","reset","rw"]++(wires0 "words" m)++(dat "di")) (["cout"]++(wires0 "rw" (2^m))++(addr "a")++(dat "do")++
>         (wires0 "_a1_" words)++(wires0 "_a0_" words)++(wires0 "off" m))
>        [inst_block {-di rotate-} (chain' (rotnet m) (rotnet m) (wires0 "u" m) [] bits)
>         ((reverse (dat "di"))++(wires0 "toff" m)++(reverse (dat "do"))),
>         inst_block {-expander-} (lte m) (["rw"]++(reverse (wires0 "words" m))++(wires0 "trw" (2^m))),
>         inst_block {-rw rotate-} (rotnet m) ((wires0 "trw" (2^m))++(wires0 "off" m)++(wires0 "rw" (2^m))),
>         inst_block {-offset-} (chain' adddffen adddffen'0 ["clk","reset","en"] ["cin","cout"] m)
>         (["clk","reset","en"]++(wires0 "words" m)++(wires0 "off" m)++["cout_inc"]),
>         inst_block (chain0' dff ["clk","reset"] m) (["clk", "reset"]++(wires0 "off" m)++(wires0 "toff" m)),
>         inst_block {-count-} (chain' incdfre' incdfre'0 ["clk","reset","en"] ["cin","cout"] words)
>         (["clk","reset","en","cout_inc","cout"]++(wires0 "_a1_" words)++(wires0 "_a0_" words)),
>         inst_block {--} (gte m) ((reverse (wires0 "off" m))++(wires0 "j" (2^m))),
>         inst_block {-muxes-} (chain0' (chain0' __mux2 ["j"] words) ((wires0 "i0" words)++(wires0 "i1" words)) (2^m))
>         ((wires0 "_a1_" words)++(wires0 "_a0_" words)++(wires0 "j" (2^m))++
>         (concat {-. transpose-}) (map (\w->wires0 (w++"_") (2^m)) (wires0 "a" words))),
>         inst_block pblk_id ["rw","en"] {-change to deal with full/empty-}]

2^m memory blocks, each of size $2^{words}*bits$.

> mqueue m tag_size words bits =
>   let dat p = (concat . transpose) (map (\w->wires0 (w++"_") (2^m)) (wires0 p bits))
>       dat' p = concatMap (\w->wires0 (w++"_") (2^m)) (wires0 p bits)
>       addr p =  (concat . transpose) (map (\w->wires0 (w++"_") (2^m)) (wires0 p words))
>       addr' p = concatMap (\w->wires0 (w++"_") (2^m)) (wires0 p words)
>       addr'' p =  (concat . transpose) (map (\w->wires0 (w++"_") (2^m)) (wires0 p (words-tag_size)))
>       --addr''' p = (concatMap (\w->wires0 (w++"_") (2^m)) (wires0 p (words-tag_size)))++
>       --            (concatMap (\x->(wires0 "tag" tag_size)) [0..((2^m)-1)])
>       --addr''' p = concat (map (\w->(wires0 (w++"_") (2^m))++(wires0 "tag_" tag_size)) (wires0 p (words-tag_size)))
>       addr''' p = (concatMap (\w->wires0 (w++"_") (2^m)) (wires0 p (words-tag_size)))++
>                   (concatMap (replicate (2^m)) (wires0 "tag_" tag_size))
>   in make_block ("mqueue_"++(show m)++"_"++(show tag_size)++"_"++(show words)++"_"++(show bits))
>        (["clk","reset","rd","wr","wr_done"]++(wires0"tag_" tag_size)++(wires0 "iwords" m)++(wires0 "owords" m)++
>        (dat "din")) (["r_w_"]++(dat "dout")++
>           ["rd_cout"]++(wires0 "_a1_" words)++(wires0 "_a0_" words)++(wires0 "off" m))
>        [inst_block {-ram-} (chain0' (ram_1r1w_synch (2^words) bits (True,0) []) ["clk","reset"] (2^m))
>         (["clk","reset"]++(wires0 "wr" (2^m))++(dat' "di")++(addr''' "wad")++(addr' "rad")++(dat' "do")),
>         inst_block {-in-} (_mqueue1 m tag_size words bits)
>         (["clk","reset","wr"]++(wires0 "tag_" tag_size)++(wires0 "iwords" m)++(dat "din")++(wires0 "wr" (2^m))++
>          (addr'' "wad")++(dat "di")),
>         inst_block {-out-} (_mqueue2 m words bits)
>         (["clk","reset","rd"]++(wires0"owords" m)++(dat"do")++["rd_cout"]++(wires0"rd" (2^m))++(addr "rad")++(dat "dout")++
>           (wires0 "_a1_" words)++(wires0 "_a0_" words)++(wires0 "off" m)),
>         inst_block gate_and2 ["rd","rd_cout","rd_done"],
>         inst_block jkfr ["clk","reset","wr_done","rd_done","r_w_"]]

mqueue with built in mqueue1 on input side.

> mqueue' m tag_size words bits =
>   let dat p = (concat . transpose) (map (\w->wires0 (w++"_") (2^m)) (wires0 p bits))
>       dat' p = concatMap (\w->wires0 (w++"_") (2^m)) (wires0 p bits)
>       addr p =  (concat . transpose) (map (\w->wires0 (w++"_") (2^m)) (wires0 p words))
>       addr' p = concatMap (\w->wires0 (w++"_") (2^m)) (wires0 p words)
>       addr'' p =  (concat . transpose) (map (\w->wires0 (w++"_") (2^m)) (wires0 p (words-tag_size)))
>       --addr''' p = (concatMap (\w->wires0 (w++"_") (2^m)) (wires0 p (words-tag_size)))++
>       --            (concatMap (\x->(wires0 "tag" tag_size)) [0..((2^m)-1)])
>       --addr''' p = concat (map (\w->(wires0 (w++"_") (2^m))++(wires0 "tag_" tag_size)) (wires0 p (words-tag_size)))
>       addr''' p = (concatMap (\w->wires0 (w++"_") (2^m)) (wires0 p (words-tag_size)))++
>                   (concatMap (replicate (2^m)) (wires0 "tag_" tag_size))
>   in make_block ("mqueue_"++(show m)++"_"++(show tag_size)++"_"++(show words)++"_"++(show bits))
>        (["clk","reset","rd","wr","wr_done"]++(wires0"tag_" tag_size)++(wires0 "iwords" m)++(wires0 "owords" m)++
>        (dat "din")) (["r_w_"]++(dat "dout")++
>           ["rd_cout"]++(wires0 "_a1_" words)++(wires0 "_a0_" words)++(wires0 "off" m))
>        [inst_block {-ram-} (chain0' (ram_1r1w_synch (2^words) bits (True,0) []) ["clk","reset"] (2^m))
>         (["clk","reset"]++(wires0 "wr" (2^m))++(dat' "di")++(addr''' "wad")++(addr' "rad")++(dat' "do")),
>         inst_block {-in-} (_mqueue1 m tag_size words bits)
>         (["clk","reset","wr"]++(wires0 "tag_" tag_size)++(wires0 "iwords" m)++(dat "din")++(wires0 "wr" (2^m))++
>          (addr'' "wad")++(dat "di")),
>         inst_block {-out-} (_mqueue2 m words bits)
>         (["clk","reset","rd"]++(wires0"owords" m)++(dat"do")++["rd_cout"]++(wires0"rd" (2^m))++(addr "rad")++(dat "dout")++
>           (wires0 "_a1_" words)++(wires0 "_a0_" words)++(wires0 "off" m)),
>         inst_block gate_and2 ["rd","rd_cout","rd_done"],
>         inst_block jkfr ["clk","reset","wr_done","rd_done","r_w_"]]

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


test_mqueue3 2 2 4 16
test_mqueue3 2 2 4 4
test_mqueue3 2 2 2 4

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
