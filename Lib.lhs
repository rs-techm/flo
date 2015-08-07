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


* Lib

> module Lib where

> import Data.List
> import Data.Bits
> import Numeric
> import qualified Data.Map as Map


> import Flo
> import Misc
> import Comb
> import Test

> --gates

> ---templates

> gate_2_template name op = make_pblock name ["i0","i1"] ["o"] ("  assign o = i0 "++op++" i1;\n")

> gate_2_inv_template name op = make_block name ["i0","i1"] ["o"]
>                               [(inst_block (gate_2_template (name++"inv") op) ["i0","i1","_t"]),
>                                (inst_block gate_invert ["_t","o"])]

> ---common basic gates

> zero = make_pblock "zero" [] ["o"] " assign o = 1'b0;\n"
> one = make_block "one" [] ["o"] [inst_block zero ["t"], inst_block gate_invert ["t","o"]]

> bid = make_pblock "id" ["i"] ["o"] " assign o = i;\n"

Required for comp_range.

> one' = make_block "one" ["i1"] ["o"] [inst_block zero ["t"], inst_block gate_invert ["t","o"]]

> gate_invert = make_pblock "invert" ["i"] ["o"] "  assign o = !i;\n"
> gate_and2 = gate_2_template "and2" "&"
> gate_or2 = gate_2_template "or2" "|"
> gate_nand2 = gate_2_inv_template "nand2" "&"
> gate_nor2 = gate_2_inv_template "nor2" "|"
> gate_xor2 = gate_2_template "xor2" "^"
> gate_xnor2 = gate_2_inv_template "xnor2" "^"

> gate_or2_inv = make_block "or2inv" ["i0","i1"] ["o"]
>                [inst_block gate_invert ["i0","i0_"], inst_block gate_or2 ["i0_","i1","o"]]


> mux2 = make_pblock "mux2" ["i0", "i1", "j"] ["o"] "  assign o = (j==0)?i0:i1;\n"

> demux2 = make_pblock "demux2" ["i", "j"] ["o0","o1"] "  assign o0 = (j==0)?i:1'b0;\n  assign o1 = (j==1)?i:1'b0;\n"

> mux_const const size = make_block ("mux_const_"++(show const)++"_"++(show size)) ((wire_vec "i" 0 size)++["j"])
>                        (wire_vec "o" 0 size)
>                        (map (\i->inst_block (if testBit const ((fromIntegral size)-i-1) then gate_or2_inv else gate_and2)
>                              ["j",("i"++(show i)),("o"++(show i))]) [0..((fromIntegral size)-1)])

demux2n, as implemented below is somewhat of a hack compared to "proper" way of
doing it which would involve reversing inputs of structure produced by
xbintree_arb but latter seems to assume all block outputs are connections to
parents (only inputs can be "horizontal" connections) which is a shortcoming
which prevents connection reversal using rec_revio (which also may have bugs).

> demux2n levels = foldr demux2n_1 pblk_id (reverse [1..levels])

> demux2n_1 level tree_blk =
>   make_block ((name_ demux2)++"n_"++(show level)) (["i"]++(wire_vec "j" 0 level)) (wire_vec "o" 0 (2^level))
>                ((inst_block demux2 (["i"]++["j"++(show (level-1))]++(wire_vec "_t" 0 2))):
>                 (map (\i->inst_block tree_blk ((wire_vec "_t" i 1)++
>                                                (wire_vec "j" 0 (level-1))++
>                                                (wire_vec "o" (i*(2^(level-1))) (2^(level-1))))) [0,1]))


> dffen_old = make_pblock "dffen_old" ["clk", "reset", "clk_en", "i"] ["o"]
>             ("reg ff_out;\n"++
>              "always@(posedge clk or posedge reset) if (reset) ff_out <= 1'b0; else if (clk_en) ff_out <= i;\n"++
>              "assign o = ff_out;\n")

> dff = make_pblock "dff" ["clk", "reset", "i"] ["o"]
>             ("reg ff_out;\n"++
>              "always@(posedge clk or posedge reset) if (reset) ff_out <= 1'b0; else ff_out <= i;\n"++
>              "assign o = ff_out;\n")


> dffen = make_block "dffen" ["clk", "reset", "en", "i"] ["o"] [inst_block dff ["clk", "reset", "mo","o"],
>                                                               inst_block mux2 ["o", "i", "en","mo"]]


** Flip flops

   Perhaps its better to have flip flops with synchronous reset (and set):

   + df: simplest, with only clk.

   + dfr: with reset

   + dfs: with set

   + dfrs: both reset and set

   + dfl: with load enable

   + dfrl,dfsl,dfrsl:

   dfrs and dfrsl would require priority determination (when both set
   and reset are 1) and also do not seem useful at present, so not
   implemented now.

> df = make_pblock "df" ["clk", "in"] ["out"] "reg df_out;\nalways@(posedge clk) df_out <= in;\nassign out = df_out;\n"

> dfr = make_block "dfr" ["clk","reset","in"] ["out"]
>       [inst_block gate_invert ["reset","reset_"], inst_block gate_and2 ["in","reset_","df_in"],
>        inst_block df ["clk","df_in","out"]]

> dfs = make_block "dfs" ["clk","set","in"] ["out"] [inst_block gate_invert ["in","dfr_in"],
>                                                    inst_block gate_invert ["dfr_out","out"],
>                                                    inst_block dfr ["clk", "set", "dfr_in","dfr_out"]]

> dfl = make_block "dfl" ["clk","load","in"] ["out"] [inst_block mux2 ["out","in","load","_in"],
>                                                     inst_block df ["clk","_in","out"]]

> dfrl = make_block "dfrl" ["clk","reset","load","in"] ["out"] [inst_block mux2 ["out","in","load","_in"],
>                                                               inst_block dfr ["clk","reset","_in","out"]]

> dfsl = make_block "dfsl" ["clk","set","load","in"] ["out"] [inst_block mux2 ["out","in","load","_in"],
>                                                             inst_block dfs ["clk","set","_in","out"]]

__jkfr is incorrect (instead of k, its complement should be input to mux) and
not really needed, but retained as used in stackef' which may (not sure) be
used somewhere.

> __jkfr = make_block "jkfr" ["clk","reset","j","k"] ["out"] [inst_block mux2 ["j","k","out","_in"],
>                                                           inst_block dfr ["clk","reset","_in","out"]]

> jkfr = make_block "jkfr" ["clk","reset","j","k"] ["out"] [inst_block gate_invert ["k","k_"],
>                                                           inst_block mux2 ["j","k_","out","_in"],
>                                                           inst_block dfr ["clk","reset","_in","out"]]

*** PISO (shift register with parallel input)

> dffenmux = make_block "dffenmux" ["clk","reset","en","sel","i0","i1"] ["o"]
>            [inst_block dffen ["clk","reset","en","t","o"],inst_block mux2 ["i0","i1","sel","t"]]

> dffenmux0 = make_block "dffenmux0" ["clk","reset","en","sel","i1"] ["o"]
>             [inst_block dffenmux ["clk","reset","en","sel","z","i1","o"],inst_block zero["z"]]

> sregpi size = chain' dffenmux dffenmux0 ["clk","reset","en","sel"] ["i0","o"] size

> sregpi' size = make_block ("sregpi_"++(show size)) (["clk","reset","load","shift"]++(wire_vec "i" 0 size)) ["o"]
>             [inst_block gate_or2 ["load","shift","en"],
>              inst_block (sregpi size) (["clk","reset","en","load"]++(wire_vec "i" 0 size)++["o"])]

> sreg size = chain' dffen (make_block "dffen_renamed" ["clk","reset","en","si"] ["o"]
>                           [inst_block dffen ["clk","reset","en","si","o"]]) ["clk","reset","en"] ["i","o"] size

> ring_count size = make_block ("ring_count_"++(show size)) ["clk","reset","shift"] ["dout"]
>                   [inst_block (sreg (size-1)) ["clk","reset","shift","dout","t"],
>                    inst_block dfsl ["clk","reset","shift","t","dout"]]

synchronous ram.

> hash pairlist = foldr (\x r->(+) (snd x) r) (0::Integer) pairlist

> ssram_init' words bits init = let addr = wire_vec "a" 0 (log2_ceil words)
>                                   din = wire_vec "i" 0 bits
>                                   dout = wire_vec "o" 0 bits
>                                   grp l = "{"++intercalate "," l++"}"
>                               in make_pblock ("ssram_init_"++(show words)++"_"++(show bits)++"_"++(show (hash init)))
>                                    (["clk","en","w"]++addr++din)
>                                    dout ("  defparam ssram_xst0.words="++(show words)++";"++
>                                          "  defparam ssram_xst0.addr="++(show (log2_ceil words))++";"++
>                                          "  defparam ssram_xst0.data="++(show bits)++"; integer i;\n"++
>                                          (if init == [] then [] else "  initial begin\n"++
>                                           "for (i=0;i<ssram_xst0.words;i=i+1) ssram_xst0.ram[i]=0;\n"++
>                                           (concatMap (\(a,d)->"    ssram_xst0.ram["++(show (log2_ceil words))++"'h"++
>                                                       (showHex a "")++"]="++(show bits)++"'h"++
>                                                       (showHex d "")++";\n") init)++"  end\n")++
>                                          "  ssram_xst ssram_xst0 (clk,en,w,"++(intercalate "," [grp addr,grp din,grp dout])
>                                          ++");\n")

> ssram' words bits = ssram_init words bits [] --([]::[(Int,Int)])

> xst_ssram_init words bits init =
>   let addr = wire_vec "a" 0 (log2_ceil words)
>       din = wire_vec "i" 0 (fromIntegral bits)
>       dout = wire_vec "o" 0 (fromIntegral bits)
>       grp l = if ((length l)==1) then (head l) else "{"++intercalate "," l++"}"
>   in make_pblock ("xst_ssram_"++(show words)++"_"++(show bits)++"_"++(show (hash init))) (["clk","en","w"]++addr++din) dout
>        ("  wire [0:"++(show ((log2_ceil words)-1))++"] va; reg [0:"++(show ((log2_ceil words)-1))++"] vra;"++
>         " wire [0:"++(show (bits-1))++"] vdi,vdo;\n"++
>         "  reg [0:"++(show (bits-1))++"] ram [0:"++(show (words-1))++"];\n"++ --"  integer i;\n"++
>         (ram_init' words bits (True,0){-hack-} init)++
>         "  always @(posedge clk) if (en) begin if (w) ram[va]<=vdi; vra<=va; end\n"++
>         "  assign va = "++(grp addr)++";\n  assign vdi = "++(grp din)++";\n  assign "++(grp dout)++" = ram [vra];\n")

> xst_ssram_rst_init words bits init rst_val =
>   let addr = wire_vec "a" 0 (log2_ceil words)
>       din = wire_vec "i" 0 (fromIntegral bits)
>       dout = wire_vec "o" 0 (fromIntegral bits)
>       grp l = if ((length l)==1) then (head l) else "{"++intercalate "," l++"}"
>   in make_pblock ("xst_ssram_"++(show words)++"_"++(show bits)++"_"++(show (hash init))) (["clk","rst","en","w"]++addr++
>        din) dout
>        ("  wire [0:"++(show ((log2_ceil words)-1))++"] va;"++
>         " wire [0:"++(show (bits-1))++"] vdi;\n"++
>         " reg [0:"++(show (bits-1))++"] vdo;\n"++
>         "  reg [0:"++(show (bits-1))++"] ram [0:"++(show (words-1))++"];\n"++ --"  integer i;\n"++
>         (ram_init' words bits (True,0){-hack-} init)++
>         "  assign va = "++(grp addr)++";\n  assign vdi = "++(grp din)++";\n  assign "++(grp dout)++" = vdo;\n"++
>         "  always @(posedge clk) if (en) begin if (w) ram[va]<=vdi; if (rst) vdo<="++(show bits)++"'h"++
>         (showHex rst_val "")++"; else vdo<=ram[va]; end\n")

> xst_ssram words bits = xst_ssram_init words bits [] --([]::[(Int,Int)])

> ssram_init = xst_ssram_init

> ssram_rst_init = xst_ssram_rst_init

> ssram = xst_ssram

ram_rd and ram_wr implement in verilog memory read and write ports, they are
separate functions to enable multiport memory construction without code repetition.

> ram_wr p bits addr_bits = "  always @("++(intercalate " or " (map ((++) p) ((wire_vec "din" 0 bits)++
>                                                                             (wire_vec "addr" 0 addr_bits)++["wr"])))++")\n"
>                           ++"    if ("++p++"wr) ram[{"++(intercalate ", " (wire_vec (p++"addr") 0 addr_bits))++"}]={"++
>                           (intercalate ", " (wire_vec (p++"din") 0 bits))++"};\n"

> ram_rd p bits addr_bits = "  assign {"++(intercalate ", " (wire_vec (p++"dout") 0 bits))++"}="++
>                           "ram[{"++(intercalate ", " (wire_vec (p++"addr") 0 addr_bits))++"}];\n"

> ram_init words bits (flag,initval) initpairs =
>   (if flag then "  integer i;\n" else "")++(if flag||(initpairs/=[]) then "  initial begin\n" else "")++
>   (if flag then "    for (i=0;i<"++(show words)++";i=i+1) ram[i]="++(show initval)++";\n" else "")++
>   (if initpairs/=[] then (concatMap (ram_init1 words bits) initpairs) else "")++
>   (if flag||(initpairs/=[]) then "  end\n" else "")

> ram_init1 words bits (addr,val) = "    ram["++(show (log2_ceil words))++"'h"++(showHex addr "")++"]="++(show bits)++
>                                   "'h"++(showHex val "")++";\n"


Following is a hack to overcome Xilinx XST's inability to initialize only a
subset of memory locations.

> ram_init' words bits (flag,initval) initpairs =
>   if initpairs /= []
>   then "  initial begin\n"++(concatMap (ram_init1' words bits initval (Map.fromList initpairs)) (reverse [0..(words-1)]))
>          ++"  end\n"
>   else ""

> ram_init1' words bits initval initmap addr =
>   ram_init1 words bits (addr,(if Map.member addr initmap then (initmap Map.! addr) else initval))

Basic (asynch, single port) ram. Ram initialization consists of two components,
If flag is true, then all locations are initialized to val else not
initialized. If initpairs, a list of (addr,val) pairs is not empty, then each
addr is initialized with val. If both initilizations are to be done, former is
done before the latter.

> ram words bits (flag,initval) initpairs =
>   make_pblock ("ram_"++(show words)++"_"++(show bits))
>                 (["wr"]++(wire_vec "din" 0 bits)++(wire_vec "addr" 0 (log2_ceil words))) (wire_vec "dout" 0 bits)
>                 ("  reg [0:"++(show (bits-1))++"] ram [0:"++(show (words-1))++"];\n"++
>                  (ram_init words bits (flag,initval) initpairs)++(ram_rd "" bits (log2_ceil words))++
>                  (ram_wr "" bits (log2_ceil words)))


**** Obsolete
synch_ram takes a ram block as input registers its input data, address and
write single(s) (multiple if more than one port). clk and reset (present if
reg_ram) are not registered. clk (if absent) and en input signals are added.

>{- synch_ram ram = make_block ("synch_"++(name_ ram)) (["clk","reset"]++((in_ports_ ram)\\["clk","reset"])) (out_ports_ ram)
>                 [inst_block (chain' dfrl dfrl ["clk","reset","load"] [] (length ((in_ports_ ram)\\["clk","reset"])))
>                  (["clk","reset","wr"]++((in_ports_ ram)\\["clk","reset"])++
>                   (map ((++) "_") ((in_ports_ ram)\\ ["clk","reset"]))),
>                  inst_block ram ((map ((++) "_") ((in_ports_ ram)\\["clk","reset"]))++(out_ports_ ram))]-}


> {-ram_synch'' words bits (flag,initval) initpairs =
>   let in_ports = in_ports_ (ram words bits (flag,initval) initpairs)
>       out_ports = out_ports_ (ram words bits (flag,initval) initpairs)
>   in make_block ("ram_synch_"++(show words)++"_"++(show bits)) (["clk","reset"]++(in_ports)) out_ports
>         [inst_block (chain' dfrl dfrl ["clk","reset","load"] [] ((length in_ports)-1))
>          (["clk","reset","en"]++in_ports++(map ((++) "_") in_ports)),
>          inst_block (ram words bits (flag,initval) initpairs) ((map ((++) "_") in_ports)++out_ports)]-}

> ram_synch words bits (flag,initval) initpairs = let ram' = ram words bits (flag,initval) initpairs
>                                                 in (reni (["clk","reset","en"]++(in_ports_ ram'))
>                                                           (ser (chain' dfrl dfrl ["clk","reset","load"] []
>                                                                          ((log2_ceil words)+bits+1)) ram'))

> ram_1r1w' words bits (flag,initval) initpairs =
>   make_pblock ("ram_1r1w_"++(show words)++"_"++(show bits))
>   (["w_wr"]++(wire_vec "w_din" 0 bits)++(wire_vec "w_addr" 0 (log2_ceil words))++
>    (wire_vec "r_addr" 0 (log2_ceil words))) (wire_vec "r_dout" 0 bits)
>   ("  reg [0:"++(show (bits-1))++"] ram [0:"++(show (words-1))++"];\n"++(ram_init words bits (flag,initval) initpairs)++
>    (ram_rd "r_" bits (log2_ceil words))++(ram_wr "w_" bits (log2_ceil words)))

> ram_1r1w_synch' words bits (flag,initval) initpairs =
>   let ram'= ram_1r1w' words bits (flag,initval) initpairs --reg size = chain' dfrl dfrl ["clk","reset","load"] [] size
>   in reni (["clk","reset"]++(in_ports_ ram'))
>        ({-scatter-} (ser (par' (chain' dfr dfr ["clk","reset"] [] ((log2_ceil words)+bits+1))
>                       (chain' dfr dfr ["clk","reset"] [] (log2_ceil words))) ram'))


> ram_1r1w_synch words bits (flag,initval) initpairs =
>   let w_addr = wire_vec "w_addr" 0 (log2_ceil words)
>       w_din = wire_vec "w_din" 0 (fromIntegral bits)
>       w_dout = wire_vec "w_dout" 0 (fromIntegral bits)
>       r_addr = wire_vec "r_addr" 0 (log2_ceil words)
>       r_dout = wire_vec "r_dout" 0 (fromIntegral bits)
>       grp l = if ((length l)==1) then (head l) else "{"++intercalate "," l++"}"
>   in make_pblock ("xst_ram_1r1w_synch_"++(show words)++"_"++(show bits)++"_"++(show (hash initpairs)))
>        (["clk","reset"]++["w_wr"]++(wire_vec "w_din" 0 bits)++(wire_vec "w_addr" 0 (log2_ceil words))++
>         (wire_vec "r_addr" 0 (log2_ceil words))) (wire_vec "r_dout" 0 bits)
>        ("  wire [0:"++(show ((log2_ceil words)-1))++"] wa,ra; reg [0:"++(show ((log2_ceil words)-1))++"] _wa,_ra;"++
>         " wire [0:"++(show (bits-1))++"] wi,wo,ro;\n"++
>         "  reg [0:"++(show (bits-1))++"] ram [0:"++(show (words-1))++"];\n"++
>         (ram_init words bits (flag,initval) initpairs)++
>         "  always @(posedge clk) begin if (w_wr) ram[wa]<=wi; _wa<=wa; _ra<=ra; end\n"++
>         "  assign wa = "++(grp w_addr)++";\n  assign ra = "++(grp r_addr)++";\n  assign wi = "++(grp w_din)++
>         ";\n  assign "++(grp r_dout)++" = ram [_ra];\n")


> ram_2r1w_synch words bits (flag,initval) initpairs =
>   let w_addr = wire_vec "w_addr" 0 (log2_ceil words)
>       w_din = wire_vec "w_din" 0 (fromIntegral bits)
>       w_dout = wire_vec "w_dout" 0 (fromIntegral bits)
>       r_addr = wire_vec "r_addr" 0 (log2_ceil words)
>       r_dout = wire_vec "r_dout" 0 (fromIntegral bits)
>       grp l = if ((length l)==1) then (head l) else "{"++intercalate "," l++"}"
>   in make_pblock ("xst_ram_2r1w_synch_"++(show words)++"_"++(show bits)++"_"++(show (hash initpairs)))
>        (["clk","en","w_wr"]++(wire_vec "w_din" 0 bits)++(wire_vec "w_addr" 0 (log2_ceil words))++
>         (wire_vec "r_addr" 0 (log2_ceil words))) ((wire_vec "w_dout" 0 bits)++(wire_vec "r_dout" 0 bits))
>        ("  wire [0:"++(show ((log2_ceil words)-1))++"] wa,ra; reg [0:"++(show ((log2_ceil words)-1))++"] _wa,_ra;"++
>         " wire [0:"++(show (bits-1))++"] wi,wo,ro;\n"++
>         "  reg [0:"++(show (bits-1))++"] ram [0:"++(show (words-1))++"];\n"++
>         (ram_init words bits (flag,initval) initpairs)++
>         "  always @(posedge clk) begin if (en) begin if (w_wr) ram[wa]<=wi; _wa<=wa; _ra<=ra; end end\n"++
>         "  assign wa = "++(grp w_addr)++";\n  assign ra = "++(grp r_addr)++";\n  assign wi = "++(grp w_din)++
>         ";\n  assign "++(grp w_dout)++" = ram [_wa];\n  assign "++(grp r_dout)++" = ram [_ra];\n")

> ram_2r1w_rst_synch words bits (flag,initval) initpairs rst_val_r rst_val_w =
>   let w_addr = wire_vec "w_addr" 0 (log2_ceil words)
>       w_din = wire_vec "w_din" 0 (fromIntegral bits)
>       w_dout = wire_vec "w_dout" 0 (fromIntegral bits)
>       r_addr = wire_vec "r_addr" 0 (log2_ceil words)
>       r_dout = wire_vec "r_dout" 0 (fromIntegral bits)
>       grp l = if ((length l)==1) then (head l) else "{"++intercalate "," l++"}"
>   in make_pblock ("xst_ram_2r1w_synch_"++(show words)++"_"++(show bits)++"_"++(show (hash initpairs))
>        ++"_"++(show rst_val_r)++"_"++(show rst_val_w))
>        (["clk","reset"]++["en","w_wr"]++(wire_vec "w_din" 0 bits)++(wire_vec "w_addr" 0 (log2_ceil words))++
>         (wire_vec "r_addr" 0 (log2_ceil words))) ((wire_vec "w_dout" 0 bits)++(wire_vec "r_dout" 0 bits))
>        ("  wire [0:"++(show ((log2_ceil words)-1))++"] wa,ra;"++
>         "  wire [0:"++(show (bits-1))++"] wi;\n"++" reg [0:"++(show (bits-1))++"] wo,ro;\n"++
>         "  reg [0:"++(show (bits-1))++"] ram [0:"++(show (words-1))++"];\n"++
>         (ram_init words bits (flag,initval) initpairs)++
>         "  assign wa = "++(grp w_addr)++";\n  assign ra = "++(grp r_addr)++";\n  assign wi = "++(grp w_din)++
>         ";\n  assign "++(grp w_dout)++" = wo;\n  assign "++(grp r_dout)++" = ro;\n"++
>         "  always @(posedge clk) if (en) begin if (w_wr) ram[wa]<=wi; if (reset) begin ro<="++(show bits)++"'h"++
>         (showHex rst_val_r "")++"; wo<="++(show bits)++"'h"++(showHex rst_val_w "")++"; end else begin ro<=ram[ra];"++
>         " wo<=ram[wa]; end end\n")

**** DONE Add a combinator that connects two blocks in series automatically naming wires uniquely.
     [Added ser and ser'.]

> ha = make_pblock "ha" ["i0","i1"] ["sum","cout"] "  assign sum=i0^i1; assign cout=i0 & i1;\n"

> ha0 = make_block "ha0" ["i0","inc"] ["sum","cout"] [inst_block ha ["i0","inc","sum","cout"]]

hav (inc) implements ripple carry increment by one. it is interesting
that chain' allows the inc input to be supplied to ha0.

> hav size = chain' ha (make_block "ha0" ["i0","inc"] ["sum","cout"] [inst_block ha ["i0","inc","sum","cout"]]) []
>            ["i1", "cout"] size

> inc = ha

ha obtained from fa when i1=0 and ha' when i1=1

> inv_ha = make_block "inv_ha" ["i0","i1"] ["sum","cout"]
>          [inst_block gate_invert ["i0","i0_"], inst_block ha ["i0_","i1","sum","cout"]]

> inv_ha0 = make_block "inv_ha0" ["i0"] ["sum","cout"] [inst_block gate_invert ["i0","cout"],inst_block pblk_id ["i0","sum"]]

> twos_comp n = make_block ("twos_comp_"++(show n)) (wires0 "i" n) ((wires0 "o" n)++["cout"])
>               [inst_block (chain' inv_ha inv_ha0 [] ["i1", "cout"] n) ((wires0 "i" n)++(wires0 "o" n)++["cout"])]

> test_twos_comp n = tb_gen2 (tv_reorder (in_ports_ (twos_comp n))
>                                   (foldr1 tvc [((reverse (wires0 "i" n)),[0,1,2,3,4,5,6,7])]))
>                    (twos_comp n) tb_comb []

> ha' = make_pblock "ha_" ["i0","i1"] ["sum","cout"] "  assign sum=!(i0^i1); assign cout=i0 | i1;\n"

hav' (dec) implements ripple carry decrement by one.

> hav' size = chain' ha' (make_block "ha'0" ["i0","dec"] ["sum","cout"] [inst_block ha' ["i0","dec","sum","cout"]]) []
>             ["i1", "cout"] size

> dec = ha'

> fa = make_pblock "fa" ["i0","i1","cin"] ["sum","cout"]
>      "  assign sum=i0^i1^cin; assign cout=(i0 & i1)|(i1 & cin)|(cin & i0);\n"


fa0 for use in (chain'' "_" fa fa [] ["cin","cout"] m).

> fa0 = make_block "fa0" ["i0","i1","_cin"] ["sum","cout"] [inst_block fa ["i0","i1","_cin","sum","cout"]]

> fav size = chain' fa ha [] ["cin","cout"] size
>
> as = make_block "as" ["i0","i1","cin","as"] ["sum","cout"] [inst_block gate_xor2 ["as","i1","t"],
>                                                          inst_block fa ["i0","t","cin","sum","cout"]]
>
> as0 = make_block "as0" ["as","i0","i1"] ["sum","cout"] [inst_block as ["i0","i1","as","as","sum","cout"]]
>
> asv size = chain' as as0 ["as"] ["cin","cout"] size

incdec implements decrementer/incrementer by 1. its input incdec, when
asserted (1), implements dec instead of inc because then only fa0
needs an inverter (otherwise, all fas other than fa0 would need
inverters).

> incdec = make_block "incdec" ["i","incdec","cin"] ["sum","cout"] [inst_block fa ["i","incdec","cin","sum","cout"]]

> incdec0 = make_block "incdec0" ["i","incdec"] ["sum","cout"] [inst_block fa ["i","incdec","incdec_inv","sum","cout"],
>                                                    inst_block gate_invert ["incdec","incdec_inv"]]

> incdecv size = chain' incdec incdec0 ["incdec"] ["cin","cout"] size

> addsub = make_block "addsub" ["addsub","i0","i1","cin"] ["sumdiff","cout"]
>          [inst_block fa ["i0","t","cin","sumdiff","cout"],inst_block gate_xor2 ["i1","addsub","t"]]

> addsub0 = make_block "addsub0" ["addsub","i0","i1"] ["sumdiff","cout"]
>           [inst_block fa ["i0","t","addsub","sumdiff","cout"],inst_block gate_xor2 ["i1","addsub","t"]]

> addsubv size = chain' addsub addsub0 ["addsub"] ["cin","cout"] size


> comp_eq size = make_block ("comp_eq_"++(show size)) (wire_vec "i" 0 (2*size)) ["o"]
>                [inst_block (chain' gate_xnor2 gate_xnor2 [] [] size) ((wire_vec "i" 0 (2*size))++(wire_vec "t" 0 size)),
>                 inst_block (fst (xbintree_arb gate_and2 size)) ((wire_vec "t" 0 size)++["o"])]

> comp_const const size = make_block ("comp_const_"++(show const)++"_"++(show size)) (wire_vec "i" 0 size) ["o"]
>                         (((map (\i->inst_block (if testBit const ((fromIntegral size)-i-1) then  pblk_id else gate_invert)
>                                 [("i"++(show i)),("t"++(show i))]) [0..((fromIntegral size)-1)]))++
>                          [inst_block (fst (xbintree_arb gate_and2 size)) ((wire_vec "t" 0 size)++["o"])])

*** Bit sum
    Adds up all 2^n input bits to ouput n bit binary sum.


> bit_sum n = make_block ("bit_sum_"++(show n)) (wires0 "i" (2^n)) (wires0 "o" (n+1))
>             ((inst_block (chain' fa ha [] ["cin","cout"] (n+1)) ((wires2_0 "t" 2 n)++(wires0 "o" (n+1)))):
>              (if n==1 then [inst_block pblk_id ["i0","t0_0"], inst_block pblk_id ["i1","t1_0"]]
>               else [inst_block (bit_sum (n-1)) ((wires0 "i" (2^(n-1)))++(wires0 "t0_" n)),
>                     inst_block (bit_sum (n-1)) ((wires "i" (2^(n-1)) (2^(n-1)))++(wires0 "t1_" n))]))

**** Bit sum mersenne

     Adds 2^n-1 input bits (n>1), outputs n bit sum. Somewhat more satisfying
     than bit_sum as output utilizes all output bits (n bit output for 2^n
     possible utputs, bit_sum required n+1 bit output to represent 2^n+1
     possible outputs) and also implemented using FAs the cin of the lsb FA is
     used to process an extra bit at each node, so only n-1 levels (instead of
     n levels for bit_sum) are required. <2013-06-29 Sat>

     Using chain'' to avoid name clash on fa_2. <2013-06-29 Sat>

> bit_sum_mers n = make_block ("bit_sum_mers"++(show n)) (wires0 "i" ((2^n)-1)) (wires0 "o" n)
>              ((inst_block (chain'' "_" fa fa0 [] ["cin","cout"] (n-1))
>                ((wires2_0 "t" 2 (n-1))++["i"++(show ((2^n)-2))]++(wires0 "o" n))):
>               (if n==2 then [inst_block pblk_id ["i0","t0_0"], inst_block pblk_id ["i1","t1_0"]]
>                else [inst_block (bit_sum_mers (n-1)) ((wires0 "i" ((2^(n-1))-1))++(wires0 "t0_" (n-1))),
>                      inst_block (bit_sum_mers (n-1)) ((wires "i" ((2^(n-1))-1) ((2^(n-1))-1))++(wires0 "t1_" (n-1)))]))

Version accepting n=1. <2013-08-18 Sun>

> bit_sum_mers' n = if n==1 then pblk_id else (bit_sum_mers n)

> incdfr' = make_block "incdfr2o" ["clk","reset","cin"] ["cout","out","dfrout"]
>            [inst_block ha ["cin","dfrout","out","cout"], inst_block dfr ["clk","reset","out","dfrout"]]

> incdfr'0 = make_block "incdfr2o0" ["clk","reset","inc"] ["cout","out","dfrout"]
>             [inst_block ha ["inc","dfrout","out","cout"], inst_block dfr ["clk","reset","out","dfrout"]]

> incdfre' = make_block "incdfre2o" ["clk","reset","en","cin"] ["cout","out","dfrout"]
>             [inst_block ha ["cin","dfrout","out","cout"], inst_block dffen ["clk","reset","en","out","dfrout"]]

> incdfre'0 = make_block "incdfre2o0" ["clk","reset","en","inc"] ["cout","out","dfrout"]
>              [inst_block ha ["inc","dfrout","out","cout"], inst_block dffen ["clk","reset","en","out","dfrout"]]


> count_incdfr' size = chain' incdfr' incdfr'0 ["clk","reset"] ["cin","cout"] size

> incdfr = make_block "incdfr" ["clk","reset","cin"] ["cout","dfrout"]
>          [inst_block ha ["cin","dfrout","out","cout"], inst_block dfr ["clk","reset","out","dfrout"]]

> incdfr0 = make_block "incdfr0" ["clk","reset","inc"] ["cout","dfrout"]
>           [inst_block ha ["inc","dfrout","out","cout"], inst_block dfr ["clk","reset","out","dfrout"]]

> count_incdfr size = chain' incdfr incdfr0 ["clk","reset"] ["cin","cout"] size



> incdfs'' = make_block "incdfs" ["clk","reset","cin"] ["cout","out","dfrout"]
>            [inst_block ha ["cin","dfrout","out","cout"], inst_block dfs ["clk","reset","out","dfrout"]]

> incdfs''0 = make_block "incdfs0" ["clk","reset","inc"] ["cout","out","dfrout"]
>             [inst_block ha ["inc","dfrout","out","cout"], inst_block dfs ["clk","reset","out","dfrout"]]

> count_incdfs' size = chain' incdfs'' incdfs''0 ["clk","reset"] ["cin","cout"] size

> incdfrs1'' = make_block "incdfrs1" ["clk","reset","cin"] ["cout","out","dfrout"]
>              [inst_block ha ["cin","dfrout","out","cout"], inst_block dfr ["clk","reset","out","dfrout"]]

> incdfrs1''0 = make_block "incdfrs10" ["clk","reset","inc"] ["cout","out","dfrout"]
>               [inst_block ha ["inc","dfrout","out","cout"], inst_block dfs ["clk","reset","out","dfrout"]]

> count_incdfrs1' size = chain' incdfrs1'' incdfrs1''0 ["clk","reset"] ["cin","cout"] size


Components:

> incdffen = make_block "incdffen" ["clk","reset","en","cin"] ["cout"]
>            [inst_block inc ["cin","ffo","sum","cout"], inst_block dffen ["clk", "reset", "en", "sum","ffo"]]

> incdffen0 = make_block "incdffen0" ["clk","reset","en","inc"] ["cout"]
>             [inst_block inc ["inc","ffo","sum","cout"], inst_block dffen ["clk", "reset", "en", "sum","ffo"]]

> adddffen = make_block "adddffen" ["clk","reset","en","i","cin"] ["o","cout"]
>            [inst_block fa ["i","o","cin","sum","cout"], inst_block dffen ["clk","reset","en","sum","o"]]

> adddffen0 = make_block "adddffen0" ["clk","reset","en","i"] ["o","cout"]
>             [inst_block ha ["i","o","sum","cout"], inst_block dffen ["clk","reset","en","sum","o"]]

> adddffen'0 = make_block "adddffen0_" ["clk","reset","en","i"] ["o","cout"]
>              [inst_block ha' ["i","o","sum","cout"], inst_block dffen ["clk","reset","en","sum","o"]]

> addsubdffen' = make_block "addsubdffen_" ["clk","reset","en","addsub","i","cin"] ["aso","ffo","cout"]
>                [inst_block addsub ["addsub","ffo","i","cin","aso","cout"],
>                 inst_block dffen ["clk", "reset", "en", "aso","ffo"]]

> addsubdffen'0 = make_block "addsubdffen0_" ["clk","reset","en","addsub","i"] ["aso","ffo","cout"]
>                 [inst_block addsub ["addsub","ffo","i","addsub","aso","cout"],
>                  inst_block dffen ["clk", "reset", "en", "aso","ffo"]]

> addsubdffen'v size = chain' addsubdffen' addsubdffen'0 ["clk", "reset", "en", "addsub"] ["cin","cout"] size



> addsubdffen''0 = make_block "addsubdffen0_" ["clk","reset","en","addsub","i"] ["aso","ffo","cout"]
>                  [inst_block addsub ["addsub","ffo","i","addsub_","aso","cout"],
>                   inst_block dffen ["clk", "reset", "en", "aso","ffo"],
>                   inst_block gate_invert ["addsub", "addsub_"]]

This version of addsubdffen adds 1 during addition and subtracts 1
during subtraction. Doing so is required in the mstack so that the
value of k, which by design can vary from 1 to 2^m, but which use of m
wires restricts to 0 to 2^m-1, can be used. Above requirement can be
easily implemented by simply inverting the cin input to LSB the
adder/subtracter, as is done in addsubdffen''0 (compared to
addsubdffen'0).

> addsubdffen''v size = chain' addsubdffen' addsubdffen''0 ["clk", "reset", "en", "addsub"] ["cin","cout"] size



----stack (synchronous ram)

stack overflow accurate only if size (at least 2) is a power of
two. underflow is accurate regardless of stack size.

todo: "main" signals at end, so cout, sum? incdec, i?

note that incdecdffen output is that of incdec and not dffen since the output
will be registered in the synchronous ram as well.

** Rotnet


First operand of mod can be negative but seems correct.

> rotnet' n i = map (\j->inst_block mux2 ["t"++(show i)++"_"++(show j),
>                                         "t"++(show i)++"_"++(show (mod (j-(2^(n-i-1))) (2^n))), "u"++(show (n-i-1)),
>                                         "t"++(show (i+1))++"_"++(show j)]) [0..((2^n)-1)]

rotnet rotates input bit at postion i to position i+u.


> rotnet n = make_block ("rotnet"++(show n)) ((wire_vec "t0_" 0 (2^n))++(wire_vec "u" 0 n))
>            (wire_vec ("t"++(show n)++"_") 0 (2^n))
>            (concatMap (rotnet' n) [0..(n-1)])


** Stack

   *Inputs* /clk/, /reset/, /push/, /pop/, /i/

   *Outputs* /o/

   *Parameters* /words/, /bits/

   Stack can store /words/ number of words each having /bits/ number
   of bits. Each operation (push or pop) is completed in one clock
   cycle.

*** Structure

    A synchronous RAM with registered output is used because it enables the RAM
    to work at maximum clock frequency since inputs as well as outputs are
    registered. [not true, outputs unregistered [actually true, but why is
    output registered?]]

    The counter output is taken from the counter
    incrementer/decrementer rather than the counter register because
    the counter output will be registered in the synchronous RAM as
    well (see invariant below).

*** Operation

    *Invariant* The stack pointer points to the current top of
    stack. That is, stack pointer output is the memory address of the
    top most data item (strictly speaking, this is not true when the
    stack is empty).

    *Invariant* Contents of the counter register and the synchronous
    RAM address register are same (except before the first operation
    (push or pop) is initiated).

**** Push

     Before the clock edge[10], the /push/ input is asserted and valid
     data is applied on the /i/ input. As a result of the former, the
     counter ouput gets incremented. At the clock edge, the address
     (stack pointer output) and the data (/i/ input) are registered
     into the synchronous RAM and the stack pointer output is also
     registered in the counter registers. After the clock edge, the
     synchronous RAM goes about storing the data, which happens
     internal to the RAM is completed before the next clock edge
     arrives.

     After the clock edge, the stack pointer is pointing towards the
     top of the stack, and the counter register contents are same as
     SSRAM address register, thus satisfying both invariants.

**** Pop

     Before the clock edge, the /pop/ input is asserted due to which
     the counter output is decremented. At the clock edge, the
     decremented output is registered in the counter register as well
     as the SSRAM address register. Note that before the clock edge
     the SRAM address register would contain the address of the data
     item at the top of the stack. So at the clock edge, the above
     data item gets registered in the SRAM data register.

     Note that the counter register, as well as the SSRAM memory
     register get decremented by one, thus satisfying both invariants.

*** Remarks

    In a software implementation, the stack pointer is incremented
    before a push and decremented after a pop (or /vice versa/). So
    initially it seemed that two counters (whose values differ by one)
    would be required to perform each operatoin in a clock cycle. It
    took some though to come up with above simple structure.

*** Stack review on <2012-04-03 Tue>

    - No need for output register
    - For exposition, can make a stack with RAM without input register, only
      difference would be that the address would be from the register
    - remove one ' from incdecdffen' and incdecdffen''
    - make stackef without preventing push/pop when empty/full as it would be
      simpler and maybe could be used to construct the preventing version
    - Can _stack be used directly instead of stack?
    - push/pop in same cycle? maybe useful, else push and pop both asserted
      should be error...
    - cleanup __jkfr
    - Instead of other stuff, abbreviate (log2_ceil words) in stack defs


[10] Clock edge refers to the positive clock edge.


> incdecdffen' = make_block "incdecdffen_" ["clk", "reset", "en", "incdec","cin"] ["o","cout"]
>                [inst_block incdec ["ffo","incdec","cin","o","cout"], inst_block dffen ["clk", "reset", "en", "o","ffo"]]

> incdecdffen'0 = make_block "incdecdffen_0" ["clk", "reset", "en", "incdec"] ["o","cout"]
>                 [inst_block incdec0 ["ffo","incdec","o","cout"], inst_block dffen ["clk", "reset", "en", "o","ffo"]]

> incdecdffen'v size = chain' incdecdffen' incdecdffen'0 ["clk", "reset", "en", "incdec"] ["cin","cout"] size

> incdecdffen'' = make_block "incdecdffen_" ["clk", "reset", "en", "incdec","cin"] ["o","ffo","cout"]
>                 [inst_block incdec ["ffo","incdec","cin","o","cout"], inst_block dffen ["clk", "reset", "en", "o","ffo"]]

> incdecdffen''0 = make_block "incdecdffen_0" ["clk", "reset", "en", "incdec"] ["o","ffo","cout"]
>                  [inst_block incdec0 ["ffo","incdec","o","cout"], inst_block dffen ["clk", "reset", "en", "o","ffo"]]

> incdecdffen''v size = chain' incdecdffen'' incdecdffen''0 ["clk", "reset", "en", "incdec"] ["cin","cout"] size

> incdecdffenmux = make_block "incdecdffen_" ["clk", "reset", "en", "incdec","cin"] ["o","cout"]
>                  [inst_block incdec ["ffo","incdec","cin","ido","cout"],
>                   inst_block dffen ["clk", "reset", "en", "ido","ffo"],
>                   inst_block mux2 [""]]


** Stack

> _stack words bits = let va = wire_vec "a" 0 (log2_ceil words)
>                         vd d = wire_vec d 0 bits
>                    in make_block "_stack" (["clk", "reset","push","pop"]++(vd "i")) ((vd "o")++["cout"])
>                         [inst_block gate_or2 ["push","pop","en"],
>                          inst_block (incdecdffen'v (log2_ceil words)) (["clk", "reset", "en", "pop"]++va++["cout"]),
>                          inst_block (ssram words bits) (["clk","en","push"]++va++(vd "i")++(vd "t")),
>                          inst_block (chain' dff dff ["clk", "reset"] [] bits) (["clk", "reset"]++(vd "t")++(vd "o"))]

> stack words bits = let va = wire_vec "a" 0 (log2_ceil words)
>                        vd d = wire_vec d 0 bits
>                    in make_block "stack" (["clk", "reset","push","pop"]++(vd "i")) (vd "o")
>                         [inst_block (_stack words bits) (["clk", "reset","push","pop"]++(vd "i")++(vd "o")++["cout"])]

> stackef words bits = let va = wire_vec "a" 0 (log2_ceil words)
>                          vr = wire_vec "r" 0 (log2_ceil words)
>                          vd d = wire_vec d 0 bits
>                      in make_block ("stack_"++(show words)++"_"++(show bits)) (["clk", "reset","push","pop"]++(vd "i"))
>                           (["full","empty"]++(vd "o"))
>                           [inst_block gate_or2 ["push_en","pop_en","en"],
>                            inst_block (incdecdffen''v (log2_ceil (words+1))) (["clk", "reset", "en", "pop_en"]++va++
>                                                                               ["_msb"]++vr++["msb"]++["cout"]),
>                            inst_block (fst (xbintree_arb gate_or2 (log2_ceil words))) (vr++["zero_"]),
>                            inst_block gate_invert ["zero_","zero"],inst_block gate_invert ["msb","msb_"],
>                            inst_block gate_and2 ["zero","msb_","empty"],inst_block gate_invert ["empty","empty_"],
>                            inst_block gate_and2 ["zero","msb","full"],inst_block gate_invert ["full","full_"],
>                            inst_block gate_and2 ["push","full_","push_en"],inst_block gate_and2 ["pop","empty_","pop_en"],
>                            inst_block (ssram words bits) (["clk","en","push_en"]++va++(vd "i")++(vd "t")),
>                            inst_block (chain' dff dff ["clk", "reset"] [] bits) (["clk", "reset"]++(vd "t")++(vd "o"))]


> stackef' words bits = let va = wire_vec "a" 0 (log2_ceil words)
>                           vd d = wire_vec d 0 bits
>                       in make_block "stackef" (["clk","reset","push","pop"]++(vd "i")) (["full","empty"]++(vd "o"))
>                            [inst_block (_stack words bits) (["clk", "reset","_push","_pop"]++(vd "i")++(vd "o")++["cout"]),
>                             inst_block gate_or2 ["_pop","_push","load_cout"],
>                             inst_block dfrl ["clk","reset","load_cout","cout","cout_reg"],
>                             inst_block gate_and2 ["_push"{-or "push"?-},"cout_reg","j_full"],
>                             inst_block gate_or2["_pop","reset","k_full"],
>                             inst_block gate_and2 ["_pop"{-or "pop"?-},"cout_reg_","t"],
>                             inst_block gate_or2["t","reset","j_empty"],
>                             inst_block gate_and2 ["push","full_","_push"],inst_block gate_and2 ["pop","empty_","_pop"],
>                             inst_block __jkfr ["clk","reset","j_full","k_full","full"],
>                             inst_block __jkfr ["clk","reset","j_empty","_push","empty"],
>                             inst_block gate_invert ["full","full_"],inst_block gate_invert ["empty","empty_"],
>                             inst_block gate_invert ["cout_reg","cout_reg_"]]

*** FIFO (synch ram)

    When empty is high, rd has no affect. When full is high, wr has no affect.

**** Invariants

     1. rd_count [and rd_addr_reg?] point to data to be read [or one position
	earlier], unless empty is high.

     2. wr_count [and wr_addr_reg?] point to location where data is to be
        written [or one position earlier?], unless full is high.

**** Issues

     1. Variations: pipelined, pseudo-asynch?

     2. Retiming view: think of synch ram as registered asynch?

     3. Invariant: counters/regs pointing to current location or previous location?

     4. Isolate adder latency, one way is to use loadable counter with inc tied
        high, will it work (seem will need synch ram reg to be fed by counter reg)?

     5. Rename fifo to queue? More abstract literature uses queue and, even if
        fifo sounds more crisp, queue is more consistent, else stack should be
        called lifo, compared to which calling fifo queue is preferable.

     Already seems FWFT mode? <2013-05-24 Fri>

> fifo words bits (flag,initval) initpairs =
>   let r_addr=wire_vec "r_addr" 0 (log2_ceil words)
>       w_addr=wire_vec "w_addr" 0 (log2_ceil words)
>   in make_block ("fifo_"++(show words)++"_"++(show bits))
>        (["clk","reset","wr","rd"]++(wire_vec "din" 0 bits)) (["full","empty"]++(wire_vec "dout" 0 bits))
>        [inst_block pblk_id ["wr","w_wr"], inst_block pblk_id ["rd","r_rd"],
>         inst_block (chain' pblk_id pblk_id [] [] bits) ((wire_vec "din" 0 bits)++(wire_vec "w_din" 0 bits)),
>         inst_block (chain' pblk_id pblk_id [] [] bits) ((wire_vec "r_dout" 0 bits)++(wire_vec "dout" 0 bits)),
>         inst_block {-rdcount-} (count_incdfr' ((log2_ceil words)+1)) (["clk","reset","r_en","r_cout"]++r_addr++
>                                                                       ["r_addr"++(show (log2_ceil words))]++
>                                                                   (wire_vec "r_addr_reg" 0 ((log2_ceil words)+1))),
>         inst_block pblk_id ["r_addr_reg"++(show (log2_ceil words)),"rmsb"],
>         {-inst_block {-rdc-} dfr ["clk","reset","r_cout","rmsb"],-}
>         inst_block {-r_en-} gate_and2 ["full_","wr","w_en"],
>         inst_block {-wrcount-} (count_incdfr' ((log2_ceil words)+1)) (["clk","reset","w_en","w_cout"]++w_addr++
>                                                                       ["w_addr"++(show (log2_ceil words))]++
>                                                                   (wire_vec "w_addr_reg" 0 ((log2_ceil words)+1))),
>         inst_block pblk_id ["w_addr_reg"++(show (log2_ceil words)),"wmsb"],
>         {-inst_block {-wrc-} dfr ["clk","reset","w_cout","wmsb"],-}
>         inst_block {-w_en-} gate_and2 ["empty_","rd","r_en"],
>         inst_block {-rw_msbeq-} gate_xnor2 ["rmsb","wmsb","rw_msbeq"],
>         inst_block gate_invert ["rw_msbeq","rw_msbeq_"],
>         inst_block {-rw_eq-} (comp_eq (log2_ceil words)) ((wire_vec "r_addr_reg" 0 (log2_ceil words))++
>                                                           (wire_vec "w_addr_reg" 0 (log2_ceil words))++["rw_eq"]),
>         {-((concat (transpose [(wire_vec "r_addr_reg" 0 (log2_ceil words)),(wire_vec "w_addr_reg" 0 (log2_ceil words))]))++
>          ["rw_eq"]),-} --not required because chain' in comp_eq seems to do the required thing
>         inst_block {-full-} gate_and2 ["rw_msbeq_","rw_eq","full"], inst_block gate_invert ["full","full_"],
>         inst_block {-empty-} gate_and2 ["rw_msbeq","rw_eq","empty"], inst_block gate_invert ["empty","empty_"],
>         inst_block {-ram-} (ram_1r1w_synch words bits (flag,initval) initpairs) -- (True,0) [])
>         (["clk","reset","w_en"]++(wire_vec "w_din" 0 bits)++(wire_vec "w_addr" 0 (log2_ceil words))++
>                     (wire_vec "r_addr" 0 (log2_ceil words))++(wire_vec "r_dout" 0 bits))]


*** Queue (fifo2)

    Differences:
    - Name
    - No initialization: seems unecessary for queue

**** DONE (?) Can queue be implemented using count reg. output only? <2012-05-11 Fri>
     Both counter outputs were used so that the count registered in counter as
     well as in addr registers of mem block are same.
     But if count reg. value only can be used then the queue could be (?) more
     similar to mqueue.

     queue modified as above since it also seems to provide ftfw (first wod
     fall through) behaviour. So perhaps this variation is more "natural" but
     its functioning needs to be properly checked. <2013-06-29 Sat>

     Further thinking and experimentation has led to the following modification
     for queue block: use wad_reg for wr addr but rad for rd adder. This
     enables fwft behaviour while retaining the (somewhat elegant) empty/full
     logic. <2013-07-06 Sat>

> queue0 words bits =
>   let adsize = log2_ceil words
>   in make_block ("queue_"++(show words)++"_"++(show bits))
>        (["clk","reset","wr","rd"]++(wire_vec "din" 0 bits)) (["full","empty"]++(wire_vec "dout" 0 bits))
>        [inst_block {-rdcount-} (count_incdfr' (adsize+1))
>         (["clk","reset","ren","rcout"]++(wire_vec "rad" 0 adsize)++["rmsb"]++(wire_vec "rad_reg" 0 adsize)++["rmsb_reg"]),
>         inst_block {-wrcount-} (count_incdfr' (adsize+1))
>         (["clk","reset","wen","wcout"]++(wire_vec "wad" 0 adsize)++["wmsb"]++(wire_vec "wad_reg" 0 adsize)++["wmsb_reg"]),
>         inst_block gate_and2 ["wr","full_","wen"], inst_block gate_and2 ["rd","empty_","ren"],
>         inst_block {-ram-} (ram_1r1w_synch words bits (True,0) [(0,0)]) --use non-initialized version?
>         (["clk","reset","wen"]++(wire_vec "din" 0 bits)++(wire_vec "wad_reg" 0 adsize)++
>                     (wire_vec "rad" 0 adsize)++(wire_vec "dout" 0 bits)),
>         inst_block {-rwmsbeq-} gate_xnor2 ["rmsb_reg","wmsb_reg","rwmsbeq"], inst_block gate_invert ["rwmsbeq","rwmsbeq_"],
>         inst_block {-rweq-} (comp_eq adsize) ((wire_vec "rad_reg" 0 adsize)++(wire_vec "wad_reg" 0 adsize)++["rweq"]),
>         inst_block {-full-} gate_and2 ["rwmsbeq_","rweq","full"], inst_block gate_invert ["full","full_"],
>         inst_block {-empty-} gate_and2 ["rwmsbeq","rweq","empty"], inst_block gate_invert ["empty","empty_"]]

***** <2013-07-26 Fri>

      queue below modified from queue0 above because for Virtex-6 at least, a
      write into a bram (used in dual port mode), does not show up at the other
      (read) port (assuming rd/wr addrs are same) in the next clock cycle as
      assumed, it shows up in the clock cycle after that. Above condition
      starts when empty and wr are high (empty and wen were the intial thought,
      but empty and wr high (seem to) imply wen high). When condition starts, a
      register is loaded with written data (in addition to bram). In the next
      clock cycle, a mux is used to output data from register instead of
      bram. So, essentially, a faster path from din to dout in a specific
      circumstance.

> queue words bits =
>   let adsize = log2_ceil words
>   in make_block ("queue_"++(show words)++"_"++(show bits))
>        (["clk","reset","wr","rd"]++(wire_vec "din" 0 bits)) (["full","empty"]++(wire_vec "dout" 0 bits))
>        [inst_block {-rdcount-} (count_incdfr' (adsize+1))
>         (["clk","reset","ren","rcout"]++(wire_vec "rad" 0 adsize)++["rmsb"]++(wire_vec "rad_reg" 0 adsize)++["rmsb_reg"]),
>         inst_block {-wrcount-} (count_incdfr' (adsize+1))
>         (["clk","reset","wen","wcout"]++(wire_vec "wad" 0 adsize)++["wmsb"]++(wire_vec "wad_reg" 0 adsize)++["wmsb_reg"]),
>         inst_block gate_and2 ["wr","full_","wen"], inst_block gate_and2 ["rd","empty_","ren"],
>         inst_block {-ram-} (ram_1r1w_synch words bits (True,0) [(0,0)]) --use non-initialized version?
>         (["clk","reset","wen"]++(wire_vec "din" 0 bits)++(wire_vec "wad_reg" 0 adsize)++
>                     (wire_vec "rad" 0 adsize)++(wire_vec "_dout" 0 bits)),
>         inst_block {-rwmsbeq-} gate_xnor2 ["rmsb_reg","wmsb_reg","rwmsbeq"], inst_block gate_invert ["rwmsbeq","rwmsbeq_"],
>         inst_block {-rweq-} (comp_eq adsize) ((wire_vec "rad_reg" 0 adsize)++(wire_vec "wad_reg" 0 adsize)++["rweq"]),
>         inst_block (chain0' dfr ["clk","reset"] adsize) (["clk","reset"]++(wires0 "wad_reg" adsize)++(wires0 "wad_reg_d" adsize)),
>         inst_block (chain0' dfr ["clk","reset"] adsize) (["clk","reset"]++(wires0 "rad" adsize)++(wires0 "rad_d" adsize)),
>         inst_block dfr ["clk","reset","wen","wen_d"],
>         inst_block {-switch-comp-} (comp_eq adsize) ((wire_vec "rad_d" 0 adsize)++(wire_vec "wad_reg_d" 0 adsize)++["_switch"]),
>         inst_block gate_and2 ["wen_d","_switch","switch"], --inst_block dfr ["clk","reset","load","switch"],
>         inst_block {-reg-} (chain0' dfr ["clk","reset"] bits)
>                  (["clk","reset"]++(wires0 "din" bits)++(wires0 "__dout" bits)),
>         inst_block (chain0' mux2 ["j"] bits) ((wires0 "_dout" bits)++(wires0 "__dout" bits)++["switch"]++
>                                               (wires0 "dout" bits)),
>         inst_block {-full-} gate_and2 ["rwmsbeq_","rweq","full"], inst_block gate_invert ["full","full_"],
>         inst_block {-empty-} gate_and2 ["rwmsbeq","rweq","empty"], inst_block gate_invert ["empty","empty_"]]


> queue_one words bits =
>   let adsize = log2_ceil words
>   in make_block ("queue_"++(show words)++"_"++(show bits))
>        (["clk","reset","wr","rd"]++(wire_vec "din" 0 bits)) (["full","empty_out"]++(wire_vec "dout" 0 bits))
>        [inst_block {-rdcount-} (count_incdfr' (adsize+1))
>         (["clk","reset","ren","rcout"]++(wire_vec "rad" 0 adsize)++["rmsb"]++(wire_vec "rad_reg" 0 adsize)++["rmsb_reg"]),
>         inst_block {-wrcount-} (count_incdfr' (adsize+1))
>         (["clk","reset","wen","wcout"]++(wire_vec "wad" 0 adsize)++["wmsb"]++(wire_vec "wad_reg" 0 adsize)++["wmsb_reg"]),
>         inst_block gate_and2 ["wr","full_","wen"], inst_block gate_and2 ["rd","empty_out_","ren"],
>         inst_block {-ram-} (ram_1r1w_synch words bits (True,0) [(0,0)]) --use non-initialized version?
>         (["clk","reset","wen"]++(wire_vec "din" 0 bits)++(wire_vec "wad_reg" 0 adsize)++
>                     (wire_vec "rad" 0 adsize)++(wire_vec "dout" 0 bits)),
>         inst_block {-rwmsbeq-} gate_xnor2 ["rmsb_reg","wmsb_reg","rwmsbeq"], inst_block gate_invert ["rwmsbeq","rwmsbeq_"],
>         inst_block {-rweq-} (comp_eq adsize) ((wire_vec "rad_reg" 0 adsize)++(wire_vec "wad_reg" 0 adsize)++["rweq"]),
>         inst_block gate_or2 ["prev_empty","empty","empty_out"], inst_block dfr ["clk","reset","empty","prev_empty"],
>         inst_block {-full-} gate_and2 ["rwmsbeq_","rweq","full"], inst_block gate_invert ["full","full_"],
>         inst_block {-empty-} gate_and2 ["rwmsbeq","rweq","empty"], inst_block gate_invert ["empty_out","empty_out_"]]


> queue_one1 words bits =
>   let adsize = log2_ceil words
>   in make_block ("queue1_"++(show words)++"_"++(show bits))
>        (["clk","reset","wr","rd"]++(wire_vec "din" 0 bits)) (["full","empty"]++(wire_vec "dout" 0 bits))
>        [inst_block (queue_one words bits) ((["clk","reset","wr","rd"]++(wire_vec "din" 0 bits))++
>                                        (["full","empty"]++(wire_vec "_dout" 0 bits))),
>         inst_block gate_and2 ["empty_","rd","ren"], inst_block gate_invert ["empty","empty_"],
>         inst_block {-dout reg-} (chain'' "__" dfrl dfrl ["clk","reset","load"] [] bits)
>         (["clk","reset","ren"]++(wires0 "_dout" bits)++(wires0 "dout" bits))]

**** queue1 (non-fwft)

     Non-fwft variant queue is made by simply registering dout, with rden used
     as load enable.

> queue1 words bits =
>   let adsize = log2_ceil words
>   in make_block ("queue1_"++(show words)++"_"++(show bits))
>        (["clk","reset","wr","rd"]++(wire_vec "din" 0 bits)) (["full","empty"]++(wire_vec "dout" 0 bits))
>        [inst_block (queue words bits) ((["clk","reset","wr","rd"]++(wire_vec "din" 0 bits))++
>                                        (["full","empty"]++(wire_vec "_dout" 0 bits))),
>         inst_block gate_and2 ["empty_","rd","ren"], inst_block gate_invert ["empty","empty_"],
>         inst_block {-dout reg-} (chain'' "__" dfrl dfrl ["clk","reset","load"] [] bits)
>         (["clk","reset","ren"]++(wires0 "_dout" bits)++(wires0 "dout" bits))]

** MIMO (multiple input multiple output) stacks/queues(fifos)

   MIMO stacks/queues can read/write multiple words in a clock cycle, instead
   of just a single word, as is usually the case. The number of words can vary,
   upto a design time constant (n).

   One approach to designing mimo queues would be to use piso and sipo blocks
   at input and output of standard queue block. Initially seems attractive due
   to separation of concerns based design. Also would require just one memory
   block (that can handle wide words). However, simple design would lead to
   extra latency due to extra latency in piso (and mybe sipo?). Also, overall
   complexity increases: for instance, at times words stored in piso plus
   incoming words would exceed n, causing overflow handling which would require
   extra complexity. Above condition would not occur in below approach.
   Further, stack design appears to be even more complex. Also, the advantage
   gained of having a single memory block may not be very useful, as such
   blocks are typically implemented using blocks with shorter word widths
   anyway. So approach seems complex and somewhat unnatural.

   Other approach is to use n memory blocks, each capable of storing a
   word. Combinational circuits at input and output would rotate the words into
   proper alignment.



*** PISO

> piso out_size in_par =
>   make_block ("piso_"++(show out_size)++"_"++(show in_par))
>                (["clk","reset","rd","wr"]++(wire_vec "din" 0 (out_size*in_par)))
>   (["empty","rds","rdr"]++(wire_vec "dout" 0 out_size))
>   ((map (\i->inst_block (sregpi' in_par) (["clk","reset","load","shift"]++(map (\j->"din"++(show (i+(j*out_size))))
>                                                                            [0..(in_par-1)])++
>                                           ["dout"++(show i)])) [0..out_size-1])++
>    [inst_block (ring_count (in_par)) ["clk","reset","shift","last"], inst_block gate_invert ["empty","empty_"],
>     inst_block gate_invert ["last","last_"], inst_block gate_invert ["wr","wr_"],
>     inst_block gate_and2 ["empty","wr","load"], inst_block gate_and2 ["last_","rd","t"], 
>     inst_block gate_or2 ["t","load","shift"], inst_block (fst (xbintree_arb gate_and2 3)) ["empty_","last","rd","u"],
>     inst_block gate_and2 ["empty","wr_","v"], inst_block gate_or2 ["u","v","_empty"],
>     inst_block dfs ["clk","reset","_empty","empty"], inst_block pblk_id ["empty","rdr"],
>     inst_block pblk_id ["empty_","rds"]])

*** Parallel input (serial output) FIFO (synch RAM)

> fifo_par_in par_words' word_size block_size (flag,initval) initpairs =
>   let r_addr=wire_vec "r_addr" 0 (log2_ceil block_size)
>       w_addr=wire_vec "w_addr" 0 (log2_ceil block_size)
>       par_words=2^(par_words')
>       blocks=par_words
>       in_bits=par_words*word_size
>       out_bits=word_size
>   in make_block ("fifo_"++(show par_words)++"_"++(show word_size)++"_"++(show block_size))
>        (["clk","reset","wr","rd"]++(wire_vec "din" 0 in_bits)) (["full","empty"]++(wire_vec "dout" 0 out_bits))
>        [inst_block pblk_id ["wr","w_wr"], inst_block pblk_id ["rd","r_rd"],
>         inst_block (chain' pblk_id pblk_id [] [] in_bits) ((wire_vec "din" 0 in_bits)++(wire_vec "w_din" 0 in_bits)),
>         --inst_block (chain' pblk_id pblk_id [] [] bits) ((wire_vec "r_dout" 0 out_bits)++(wire_vec "dout" 0 out_bits)),
>         inst_block {-rdcount-} (count_incdfrs1' ((log2_ceil block_size)+1)) (["clk","reset","roff_cout","r_cout"]++r_addr++
>                                                                       ["r_addr"++(show (log2_ceil block_size))]++
>                                                                   (wire_vec "r_addr_reg" 0 ((log2_ceil block_size)+1))),
>         inst_block pblk_id ["r_addr_reg"++(show (log2_ceil block_size)),"rmsb"],
>         inst_block {-rdoffset-} (count_incdfr' par_words') (["clk","reset","r_en","roff_cout"]++
>                                                             (wire_vec "roff_addr" 0 par_words')++
>                                                             (wire_vec "roff_addr_reg" 0 par_words')),
>         inst_block {-offsetcomp-} (comp_const (par_words-(1::Integer)) par_words') 
>         ((wire_vec "roff_addr_reg" 0 par_words')++["roff_max"]),
>         {-inst_block {-rdc-} dfr ["clk","reset","r_cout","rmsb"],-}
>         inst_block {-w_en-} gate_and2 ["full_","wr","w_en"],
>         inst_block {-wrcount-} (count_incdfr' ((log2_ceil block_size)+1)) (["clk","reset","w_en","w_cout"]++w_addr++
>                                                                       ["w_addr"++(show (log2_ceil block_size))]++
>                                                                   (wire_vec "w_addr_reg" 0 ((log2_ceil block_size)+1))),
>         inst_block {-wrcountinc-} (chain' ha ha0 [] ["i1","cout"] ((log2_ceil block_size)+1))
>         ((wire_vec "w_addr_reg" 0 ((log2_ceil block_size)+1)++["one"])++
>          (wire_vec "w_addr_reg_inc" 0 ((log2_ceil block_size)+1))++["w_addr_reg_inc_cout"]),
>         inst_block {-one-} one ["one"],
>         inst_block pblk_id ["w_addr_reg"++(show (log2_ceil block_size)),"wmsb"],
>         inst_block pblk_id ["w_addr_reg_inc"++(show (log2_ceil block_size)),"_wmsb"],
>         {-inst_block {-wrc-} dfr ["clk","reset","w_cout","wmsb"],-}
>         inst_block {-r_en-} gate_and2 ["empty_","rd","r_en"],
>         inst_block {-rw_msbeq-} gate_xnor2 ["rmsb","wmsb","rw_msbeq"],
>         inst_block {-rw_msbeq-} gate_xnor2 ["rmsb","wmsb","_rw_msbeq"],
>         inst_block gate_invert ["_rw_msbeq","_rw_msbeq_"],{-inst_block gate_invert ["rw_msbeq","rw_msbeq_"],-}
>         inst_block {-rw_eq-} (comp_eq (log2_ceil block_size)) ((wire_vec "r_addr_reg" 0 (log2_ceil block_size))++
>                                                                (wire_vec "w_addr_reg" 0 (log2_ceil block_size))++
>                                                                ["rw_eq"]),
>         inst_block {-_rw_eq-} (comp_eq (log2_ceil block_size)) ((wire_vec "r_addr_reg" 0 (log2_ceil block_size))++
>                                                                 (wire_vec "w_addr_reg_inc" 0 (log2_ceil block_size))++
>                                                                 ["_rw_eq"]),
>         {-((concat (transpose [(wire_vec "r_addr_reg" 0 (log2_ceil words)),(wire_vec "w_addr_reg" 0 (log2_ceil words))]))++
>          ["rw_eq"]),-} --not required because chain' in comp_eq seems to do the required thing
>         inst_block {-full-} gate_and2 ["_rw_msbeq_","_rw_eq","full"], inst_block gate_invert ["full","full_"],
>         inst_block {-empty-} (fst (xbintree_arb gate_and2 3)) ["rw_msbeq","rw_eq","roff_max","empty"],
>         inst_block gate_invert ["empty","empty_"],
>         inst_block {-ram-} (ram_1r1w_synch block_size in_bits (flag,initval) initpairs) -- (True,0) [])
>         (["clk","reset","w_en"]++(wire_vec "w_din" 0 in_bits)++(wire_vec "w_addr" 0 (log2_ceil block_size))++
>                     (wire_vec "r_addr" 0 (log2_ceil block_size))++(wire_vec "r_dout" 0 in_bits)),
>         inst_block (chain' dfr dfr ["clk","reset"] [] par_words')
>         (["clk","reset"]++(wire_vec "roff_addr_reg" 0 par_words')++(wire_vec "roff_addr_reg_reg" 0 par_words')),
>         inst_block (chain' (fst (xbintree_arb mux2 blocks)) (fst (xbintree_arb mux2 blocks))
>                     (map (\i->"j"++(show i)) [0..(par_words'-1)]) [] word_size)
>                     ((wire_vec "r_dout" 0 in_bits)++(wire_vec "roff_addr_reg" 0 par_words')++(wire_vec "dout" 0 out_bits))]


** Zero latency pop/read in stack/queue

   While reasonbly straightforward to provide, how useful? All it seems to
   change is the pop/read needs to be asserted a clock cycle later. Also may
   require pop/read to be done every cycle (unless RAM output registered) which
   is not power efficient.

   But if one has a zero lat. implementation can it be converted to a "normal"
   version by simply registering the dout? If so, in general, zero lat. may be
   preferable... <2012-05-16 Wed>


*** Related: Allow push/pop and (first and later) write/read in same cycle?

    So empty should go low when? And full should go high when?
    If read asserted full can't be asserted?
    If write asserted empty can't be deasserted?

Control FSM Combinators

> in_ports' blk = (in_ports_ blk)\\["clk","reset"]

> ipunion wire blk0 blk1 = ["clk","reset"]++(union (union (in_ports' blk0) (in_ports' blk1)) wire)

> opunion' wire blk0 blk1 = union (union (out_ports_ blk0) (out_ports_ blk1)) wire

> opunion blk0 blk1 = union (out_ports_ blk0) (out_ports_ blk1)

> fser wire blk0 blk1 = make_block ((name_ blk0)++"FS"++(name_ blk1)) (ipunion wire blk0 blk1) (opunion blk0 blk1)
>                       [inst_block blk0 ((in_ports_ blk0)++(replace "o" "ti" (out_ports_ blk0))),
>                        inst_block blk1 ((replace "i" "to" (in_ports_ blk0))++(out_ports_ blk0)),
>                        inst_block gate_and2 ["ti","wire","to"]]

> floop wire0 wire1 blk = make_block ("FL"++(name_ blk)) ((in_ports_ blk)\\[wire1]) ((out_ports_ blk)\\[wire0])
>                         [inst_block blk (io_ports blk), inst_block pblk_id [wire0,wire1]]

