> module Flo where

> import Prelude
> import Data.Char
> import Numeric
> import Data.List
> import qualified Data.Map as Map

> import Misc

> {-indent1 spaces n r = (if ((n==';')&&(r/=[])) then (";\n"++(take spaces (repeat ' '))) else (n:"")):r-}

> {-indent spaces text = foldr (indent1 spaces) [] text-}

> {-add_commas l = concat (intersperse "," l)-}

> {-lookup_l k l_map = if l_map==[] 
>                    then (error $ "lookup_l: key "++(show k)++"not found.\n"++(show l_map))
>                    else if k==(fst (head l_map))
>                         then (snd (head l_map))
>                         else (lookup_l k (tail l_map))-}

> --from Data.Map.Utils
> {-fm_lookup :: (Show key, Ord key) => key ->Map.Map key elt -> elt-}
> {-fm_lookup k fm = case Map.lookup k fm of
>                    Just x -> x
>                    Nothing -> error $ "fm_lookup" ++ ": could not find key " ++ (show k)-}

> {-m_insert_list z l = foldr (\n r-> Map.insert (fst n) (snd n) r) z l -}

> {-check_block block = unique_elems (io_ports block) -}

> {-check_pblock = check_block -}

> {-check_lblock = check_block -}

> {-check_fl block = trav_blocks (\b l->(check_block b) && (and l)) check_pblock check_lblock block -}

> out_ver = putStr . fl__ver

> data Block = Block_ {name_ :: String, in_ports_ :: [String], out_ports_ :: [String], inst_blocks_ :: [Inst_block]}
> --             deriving (Eq, Show)
>            | Pblock_ {name_ :: String, in_ports_ :: [String], out_ports_ :: [String], text_ :: String}
>            | Lblock_ {name_ :: String, in_ports_ :: [String], out_ports_ :: [String]}
>              deriving (Eq, Show)

> data Inst_block = Inst_block_ {block_ :: Block, wires_ :: [String]}
>                   deriving (Eq, Show)

> io_ports block = (in_ports_ block)++(out_ports_ block)

> trav_blocks fn fnp fnl block = case block of
>                                Block_ a b c d -> fn block (map ((trav_blocks fn fnp fnl) . block_) (inst_blocks_ block))
>                                Pblock_ a b c d -> fnp block
>                                Lblock_ a b c -> fnl block

> v_inst_mod (inst_block, i) = "  "++(name_ (block_ inst_block))++" "++(name_ (block_ inst_block))++"_"++(show i)++"("++
>                              ((concat (intersperse ", " (wires_ inst_block))))++");\n"

> dec_wires blk = intercalate ", "  
>                 ((if (in_ports_ blk)==[] then [] else ["input wire "++(((intercalate ", ") . in_ports_) blk)])++
>                 (if (out_ports_ blk)==[] then [] else ["output wire "++(((intercalate ", ") . out_ports_) blk)]))

> block__mod block = let all_wires = filter (\w->isAlpha(head w)||('_'==(head w))) (concatMap wires_ (inst_blocks_ block))
>                        wires = (\\) (nub all_wires) (io_ports block)
>                    in "\nmodule "++(name_ block)++" ("++(dec_wires block)++");\n"++
>                           (if (wires == []) then "" else ("  wire "++(concat (intersperse "," wires))++";\n"))++
>                           (concatMap v_inst_mod (zip (inst_blocks_ block) [0..]))++"endmodule\n"

> pblock__mod block = "\nmodule "++(name_ block)++" ("++(dec_wires block)++");\n"++(text_ block)++"endmodule\n"

> blocks_used block = nub (trav_blocks (\block blocks->block:(concat blocks)) (\block->[]) (\block->[]) block)

> pblocks_used block = nub (trav_blocks (\block blocks->(concat blocks)) (\block->[block]) (\block->[]) block)

> fl__ver block = (concatMap pblock__mod (pblocks_used block))++(concatMap block__mod (blocks_used block))

> {-attach inst_block port wire = inst_block {wires_ = map (\(p,w)->if p==port then wire else w)
>                                                    (zip (io_ports (block_ inst_block)) (wires_ inst_block))} -}

> {- attach_v inst_block ports wires = foldr (\(port,wire) cur_block-> attach cur_block port wire) inst_block (zip ports wires) -}

Other features:

1. flatten transform
2. testbench
3. signal probes?
4. behavioural descriptions? via fsms specified as recursive functions?
5. Finite State Transducer based control FSM specification using "transducer regular expressions"

> ports_vec ports vec_ports size = concatMap (\port-> if (elem port vec_ports)
>                                                     then map (\i->port++""++(show i)) [0..(size-1)]
>                                                     else [port]) ports 

> ports_vec_i ports vec_ports i =  map (\port-> if (elem port vec_ports) then (port++""++(show i)) else port) ports

> {-ports_vec_i' ports i = ports_vec_i ports ports i -}

> {-ports_wires1 subst_map port = case (lookup port subst_map) of
>                               Nothing -> port
>                               Just subst -> subst -}

> {-ports_wires ports subst_map = map (ports_wires1 subst_map) ports -}

> --subst_

> {-block_vec block vec_ports size = make_block ((name_ block)++"_vec_"++(show size))
>                                  (ports_vec (in_ports_ block) vec_ports size)
>                                  (ports_vec (out_ports_ block) vec_ports size)
>                                  (map (\i -> make_inst_block block (ports_wires (io_ports block)
>                                                                     (map (\vec_port->(vec_port, vec_port++"_"++(show i)))
>                                                                      vec_ports))) [0..(size-1)]) -}

> {-block_chain block vec_ports left right size = make_block ((name_ block)++"_chain_"++(show size))
>                                               (ports_vec (in_ports_ block) vec_ports size)
>                                               (ports_vec (out_ports_ block) vec_ports size)
>                                               (map (\i -> make_inst_block block (ports_vec_i (io_ports block) vec_ports i))
>                                                [0..(size-1)]) -}


*** Combinators

> ser a b = make_block ((name_ a)++"S"++(name_ b)) (in_ports_ a) (out_ports_ b)
>           [inst_block a ((in_ports_ a)++(out_ports_ a)), inst_block b ((out_ports_ a)++(out_ports_ b))]

> {-adds l = map ((++) "S") l -} --map (\w->if w=="clk" || w=="reset" then w else "S"++w) l --hack?

> {-ser' a b = make_block ((name_ a)++"S"++(name_ b)) (in_ports_ a) (adds (out_ports_ b))
>            [inst_block a ((in_ports_ a)++(adds (in_ports_ b))), inst_block b ((adds (in_ports_ b))++(adds (out_ports_ b)))] -}

**** DONE ser' is useful (synch_ram) but not general as (in_ports_ b) and (in_ports_ a) size may differ, what to do?
     [changed ser' def to something (hopefully) more useful.]

> par a b = make_block ((name_ a)++"P"++(name_ b)) ((in_ports_ a)++(in_ports_ b)) ((out_ports_ a)++(out_ports_ b))
>           [inst_block a ((in_ports_ a)++(out_ports_ a)), inst_block b ((in_ports_ b)++(out_ports_ b))]

> --id = make_block "id" ["a"] ["a"] []

> addp l = map (\w->if w=="clk" || w=="reset" then w else "P"++w) l -- map ((++) "P") l

**** TODO Use of nub in par'?

> par' a b = make_block ((name_ a)++"P"++(name_ b)) (nub ((in_ports_ a)++(addp (in_ports_ b))))
>            (nub ((out_ports_ a)++(addp (out_ports_ b))))
>            [inst_block a ((in_ports_ a)++(out_ports_ a)), inst_block b (addp ((in_ports_ b)++(out_ports_ b)))]

**** TODO Special treatment of clk and reset in ser' and par', whats a better way?

> --scatter l = make_block ("scatter_"++(show (length l))) (nub l) l []

> --scatter b = make_block ("scatter_"++(name_ b)) (nub (in_ports_ b)) (out_ports_ b) [inst_block b (io_ports b)]

> {-wire_eq' = dropWhile (\c->(c=='P')||(c=='S')) -}

> {-wire_eq u v = (wire_eq' u)==(wire_eq' v) -}

> -- scatter b = make_block ("scatter_"++(name_ b)) (nubBy wire_eq (in_ports_ b)) (out_ports_ b) [inst_block b (io_ports b)]
> {-scatter b = make_block ("scatter_"++(name_ b)) (nub (in_ports_ b)) (out_ports_ b) [inst_block b (io_ports b)] -}

**** TODO scatter name conflict, hash on list?

> --gather b = make_block ("gather_"++(name_ b)) (in_ports_ b) (nubBy wire_eq (out_ports_ b)) [inst_block b (io_ports b)]
> {-gather b = make_block ("gather_"++(name_ b)) (in_ports_ b) (nub (out_ports_ b)) [inst_block b (io_ports b)] -}
> -- gather l = make_block ("gather_"++(show (length l))) l (nub l) []

reni (rename inputs) essentially (by creating a new block in which b is
instantiated) replaces the list of input port names of b by the list l (which
should be of same size).

> reni l b = make_block ("reni_"++(name_ b)) l (out_ports_ b) [inst_block b (l++(out_ports_ b))]

*** Primitives

> {-ports_v wires_or_prefixes size = concatMap (\wp->if (last wp)=='_' then (map (\i->wp++(show i)) [0..(size-1)]) else [wp])
>                                  wires_or_prefixes -}

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

**** TODO Why here? bid in Lib.lhs is same. Remove pblk_id? <2013-05-22 Wed>

id_block:

> pblk_id = make_pblock "id" ["i"] ["o"] "  assign o = i;\n"

TODO: Replace "concat (intersperse..." by intercalate.
TODO: Replace input_ports_ by in_ (same for out)? 

todo: wire connect module ? could be id module with size parameter.
todo: remove wire names? instantiate modules like functions are called?

TODO: Only import Flo.lhs should be required in design files.

**** TODO inst_block variant that allows inst name to be specified.
