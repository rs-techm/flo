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


> module Test where

> import Data.Bits
> import Data.List

> import Flo
> import Misc
> import qualified Data.Map as Map

> ---Testbench
> tb_comb = 1

> tb_seq = 0

> tb_clk_reset = "  initial begin reset = 1'b1; #12.5 reset = 1'b0; end\n"++
>                 "  initial clk = 1'b0; always #5 clk =~ clk;\n"
>
> tb_dumpvars blkname = "  initial begin $dumpvars(0,tb); $dumpfile(\""++blkname++"tb.vcd\"); end\n"
>
> tb_wrinout mname wires = "`define "++mname++" $write(\"%t     "++
>                          (concatMap (\i->"%b"++(take (length i) (repeat ' '))) (tail wires))++"%b"++
>                          "\", $time,"++(intercalate "," wires)++");"
>
> tb_decl n_tests inputs outputs = "  reg clk,reset,"++(intercalate "," inputs)++";\n"++
>                                  "  wire "++(intercalate "," outputs)++";\n"++
>                                  "  reg [0:"++(show ((length inputs)-1))++"] test_mem [0:"++(show (n_tests-1))++"];\n"++
>                                  "  integer i,j;\n"

> tb_loop n_tests inputs outputs =
>   "  initial begin\n    $write (\"   time    "++(intercalate " " inputs)++"     time    "++
>                                              (intercalate " " outputs)++"\\n\\n\");\n"++
>   "    #6 for(i=0;i<"++(show n_tests)++";i=i+1)\n"++"      begin #8 `WRIN `WROUT #2 {"++(intercalate "," inputs)++
>   "}=test_mem[i]; end\n"++"    #8 `WRIN `WROUT #2 #8 `WRIN `WROUT #2 $finish;\n"++"  end // initial begin"


> tb_init_tests1 vec_size i test_vec = "    test_mem["++(show i)++"]="++((show vec_size)++"'b"++
>                                                                        (reverse (show_num_base_size 2 vec_size test_vec)))
>                                      ++";\n"

> tb_init_tests vec_size test_vecs = "  initial begin\n"++(concat (zipWith (tb_init_tests1 vec_size)
>                                                                  [0..((length test_vecs)-1)] test_vecs))++"  end\n"

> tb_init_tests2_1 vec_size i test_vec = "    test_mem["++(show i)++"]="++((show vec_size)++"'b"++
>                                                                        (test_vec))++";\n"

> tb_init_tests2 vec_size test_vecs = "  initial begin\n"++(concat (zipWith (tb_init_tests2_1 vec_size)
>                                                                  [0..((length test_vecs)-1)] test_vecs))++"  end\n"

> tb_block_inst block = "  "++(name_ block)++" "++(name_ block)++"_0"++" ("++
>                        (intercalate "," ((in_ports_ block)++(out_ports_ block)))++");\n"

Test vector product.

> tvp (ports0, tvecs0) (ports1, tvecs1) = (ports0++ports1, cart_prod_l tvecs0 tvecs1)

Test vector concatanate (columnwise).

> tvc::([String],[Integer])->([String],[Integer])->([String],[Integer])

> tvc (ports0, tvecs0) (ports1, tvecs1) = if ((length tvecs0) /= (length tvecs1))
>                                         then error $ "Unequal size lists in tvc."
>                                         else (ports0++ports1, zipWith (\n0 n1->(shiftL n0 (length ports1)) .|. n1)
>                                               tvecs0 tvecs1)

Test vector reorder: Order the test vector columns in the same order as ports of instantiated block.

> tv_reorder inst_ports (tv_ports, tvecs) = 
>   transpose (map ((Map.!) (Map.fromList (zip tv_ports (transpose (map (show_num_base_size 2 (length tv_ports)) tvecs)))))
>              inst_ports)

> tb_loop2 n_tests inputs =
>   "  initial begin\n"++
>   "    #6 for(i=0;i<"++(show n_tests)++";i=i+1)\n"++"      begin #10 {"++(intercalate "," inputs)++
>   "}=test_mem[i]; end\n"++"    #2700 $finish;\n"++"  end // initial begin"

> tb_sig_groups_decl (name,group) = "  wire ["++(show ((length group)-1))++":0] "++name++";\n"

> tb_sig_groups_wire (name,group) = "  assign "++name++" = {"++(intercalate "," (reverse group))++"};\n"

> tb_gen2 test_vecs block comb_seq sig_groups =
>   let inputs = if comb_seq == tb_seq then (in_ports_ block)\\["clk","reset"] else (in_ports_ block)
>       outputs = out_ports_ block
>   in  "\n`timescale 1 ns / 100 ps\n"++"\nmodule tb;\n"++
>         (tb_decl (length test_vecs) inputs outputs)++(concatMap tb_sig_groups_decl sig_groups)++
>         (concatMap tb_sig_groups_wire sig_groups)++
>         (tb_dumpvars (name_ block))++tb_clk_reset++
>         (tb_init_tests2 (length inputs) test_vecs)++
>         "  initial {"++(intercalate "," inputs)++"} = 0;\n"++  -- ++" initial\n"++
>         (tb_block_inst block)++(tb_loop2 (length test_vecs) inputs)++"\nendmodule\n"
>


> tb_gen test_vecs block comb_seq =
>   let inputs = if comb_seq == tb_seq then (in_ports_ block)\\["clk","reset"] else (in_ports_ block)
>       outputs = out_ports_ block
>   in  "\n`timescale 1 ns / 100 ps\n"++(tb_wrinout "WRIN" inputs)++" $write(\"   \");\n"++
>         (tb_wrinout "WROUT" outputs)++" $write(\"\\n\");\n"++"\nmodule tb;\n"++
>         (tb_decl (length test_vecs) inputs outputs)++(tb_dumpvars (name_ block))++tb_clk_reset++
>         (tb_init_tests (length inputs) test_vecs)++
>         "  initial {"++(intercalate "," inputs)++"} = 0;\n"++" initial $timeformat(-9,1,\"\",7);\n"++
>         (tb_block_inst block)++(tb_loop (length test_vecs) inputs outputs)++"\nendmodule\n"

> --main = let dut = (chain fa [] ["cin", "cout"] 3) in (putStr) (((fl__ver dut)++(tb_gen [0..9] dut tb_comb)))
> --main = let dut = (stack 16 4) in (putStr) (((fl__ver dut)++(tb_gen [0x0,0x20,0x21,0x22,0x23,0x0,0x10,0x0,0x24,0x0,0x10,0x0,0x10,0x0,0x25,0x0,0x10,0x10] dut tb_seq)))
> --main = let dut = (comp_range_gel 4 10 3) in (putStr) (((fl__ver dut)++(tb_gen [0..15] dut tb_comb)))
> --main = let dut = (mstack 2 8 4) in (putStr) (((fl__ver dut)++(tb_gen [0x0,0x9,0x5,0x5,0xd,0x9,0x6,0xa,0xe,0x6,0xa,0xe,0x6,0xa,0xe] dut tb_seq)))
> --main = let dut = (mstack 2 8 4) in (putStr) (((fl__ver dut)++(tb_gen [0x0,0x3210d,0x7654d,0x0000e,0x0000e] dut tb_seq)))

> -- main = let dut = (rotnet 3) in (putStr) (((fl__ver dut)++(tb_gen [0x010,0x110,0x210,0x310,0x410,0x510,0x610,0x710] dut tb_comb)))
