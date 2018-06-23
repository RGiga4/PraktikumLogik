module MyVortrag where

import DNF
import qualified Data.Map as Map
import qualified Data.Set as Set
--import NNF
import Parsing_FOL
import Printer_FOL
import DefCnf
import Vortrag1
import FirstOrder

tmp1::Formula FOL
tmp1 = (Bottom)
bot = simpdnf tmp1
-- soll alle Terme mit n funktion geben

groundterms cntms funcs n 
	| n == 0 = cntms
	| otherwise = [(Fn (fst f) x) | f  <- funcs, x <- groundtuples cntms funcs (n-1) (snd f)]

-- soll alle [Term] fur m stellen und mit n funtionen geben
groundtuples cntms funcs n m =
	if m == 0 then 	
		if n == 0 then [[]]
		else []
	else [[x1] ++ x2 | k <- [0..n], x1 <- groundterms cntms funcs k, 
		x2 <- groundtuples cntms funcs (n-k) (m-1) ]



t1 = groundterms [(Fn "0" []), (Fn "1" [])] [("f", 1)] 1
t2 = groundtuples [(Fn "0" []), (Fn "1" [])] [("f", 1)] 0 1
t3 = groundtuples [(Fn "0" []), (Fn "1" [])] [("f", 1)] 1 1
t4 = groundterms [(Fn "0" [])] [("f", 1)] 10
t5 = groundterms [(Fn "1" [])] [("add", 2)] 1
t6 = groundterms [(Fn "0" [])] [("add", 2), ("succ", 1)] 3

snf = parse "D(x) ==> D(f_y(x))"

fm = parse "exists x. forall y. D(x) ==> D(y)"
t7 = gilmore fm
t8 = And snf fm

testfa fm = 
	let x = simpdnf fm in
	bot == x

--mfn Modifzierte formel
--tfn ? original formel
herbloop mfn tfn cntms funcs fvs n fl tried rest =
	if null rest then
		let newtuples = groundtuples cntms funcs n (length fvs) in
		herbloop mfn tfn cntms funcs fvs (n+1) fl tried newtuples
		
	else 
		let tup = head rest in--hier was printen1111111111111111111
		let tups = tail rest in
		if(elem tup tried) then herbloop mfn tfn cntms funcs fvs n fl tried tups
		else
			let sub = Map.fromList (zip fvs tup) in
			let fl' =  subst2 sub tfn in
			if testfa (And mfn fl') then--(n>=3) then 
				(tup:tried)
			else
				herbloop (And mfn fl') tfn cntms funcs fvs n fl (tup:tried) tups



gilmore fm =
	let sfm = skolemize(Not(generalize fm)) in
	let funcs = functions sfm in
	let cntms = [(Fn "c" [])] in
	let fvs = fv sfm in
	herbloop (Top) (sfm) cntms funcs fvs 0 [[]] [] [] --smipdnf einarbeiten

gilmore_loop fm = 
	simpdnf fm


