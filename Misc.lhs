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


> module Misc where

> import Numeric
> import Data.List
> import Data.Bits
> import qualified Data.Map as M
> import qualified Data.Set as S

Generic tree:

> data Tree a = Tree_ {node_::a, forest_::[Tree a]} deriving (Eq, Ord, Show)


> unfold :: (t -> Bool) -> (t -> a) -> (t -> t) -> t -> [a]
> unfold p f g x = if p x then [] else f x : unfold p f g (g x)


Take the last n elements of the list.

> take_last n l = reverse (take n (reverse l))

Rotate list l to the left by i places.

> rotatel i l = (drop i l)++(take i l)

> hylo e z p f g x = foldr f z (unfold p f g x)

> map' f l = if l==[] then [] else (f (head l))++(map' f (tail l))

> map2 f l0 l1 = map (\i-> map (f i) l1) l0

> map3 f l0 l1 l2 = map (\i-> map2 (f i) l1 l2) l0

Cartesian product of lists: Takes two "2D" lists (lists of lists) of sizes c_0
x r_0 and c_1 x r_1 as input, and outputs a "2D" list of size (c_0 +
c_1) x (r_0 * r_1).

> cart_prod_l l0 l1 = concat (map2 (++) l0 l1) 


int must be greater than zero

> log2_floor int = if int == 1 then 0 else (1+(log2_floor (div int 2)))


int must be greater than one

> log2_ceil int = log2_floor (int - 1) + 1

> unique_elems l = if (length (nub l)) == (length l) then True else False

> show_num_base base num = showIntAtBase base (head . show) num ""

> show_num_hex num = showHex num ""

> show_num_base_size base size num = let str = showIntAtBase base (head . show) num ""
>                                    in (take (size - (length str)) (repeat '0'))++str

> read_dec str = (snd.head.readDec) str

> read_hex str = (fst.head.readHex) str

> replace elem new_elem list = map (\elem'->if elem'==elem then new_elem else elem') list

> reverse_bits::(Bits a,Num a)=>Int->a->a
> reverse_bits size num = let size' = log2_ceil size
>                         in foldr (\i num'-> (if testBit num i then setBit else clearBit) num' (size'-i-1)) 0 [0..(size'-1)]

Map lookup <2013-10-02 Wed>

> lookup' key map = case M.lookup key map of
>                   Just a -> a
>                   Nothing -> error (show key)


Check if given two argument function (as a list of triples ((a,b),c)) is associative.

> is_assoc f = let arg = S.toList (foldr (\((x,y),z) s->S.insert y (S.insert x s)) (S.empty) f)
>                  args = concat (concat (map3 (\i j k-> (i,j,k)) arg arg arg))
>                  fn = M.fromList f
>                  assoc a b c = fn M.! ((fn M.! (a,b)),c) == fn M.! (a,(fn M.! (b,c)))
>              in foldr (\(a,b,c) r-> (show (a,b,c)++": "++(show(assoc a b c))):r) [] args

Replace one element of a pair

> replace_fst a' (a,b) = (a',b)

> replace_snd b' (a,b) = (a,b')
