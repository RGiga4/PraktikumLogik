module MyVortrag where

import DNF
import qualified Data.Map as Map
import qualified Data.Set as Set
import DP
import Parsing_FOL
import Printer_FOL
import DefCnf
import Vortrag1
import FirstOrder


tmp1::Formula FOL
tmp1 = (Bottom)
bot = simpdnf tmp1
bot2 = simpcnf tmp1

tmp2::Formula FOL
tmp2 = (Top)
top1 = simpdnf tmp2
top2 = simpcnf tmp2
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





testfa fm = 
	let x = simpdnf fm in
	bot == x
testfb dnf = 
	
	bot == dnf
tfncnf cnf = 
	dp $ doge cnf
simpdnfinj fm = 
           let djs = Set.filter DNF.nontrivial fm
               nonsuperset s = Set.null $ Set.filter (flip Set.isProperSubsetOf s) djs
           in Set.filter nonsuperset djs
simpcnfinj fm =
           let cjs = Set.filter DNF.nontrivial fm
               nonsuperset s = Set.null $ Set.filter (flip Set.isProperSubsetOf s) cjs
           in Set.filter nonsuperset cjs

dnfAnd x y =
	let x' = Set.toList x in
	let y' = Set.toList y in
	simpdnfinj $ Set.fromList[Set.union a b | a <- x', b <- y']
cnfAnd x y =
	simpcnfinj $ Set.union x y 


herbloopdnf mfn tfn fl0 cntms funcs fvs n fl tried rest =
	if null rest then
		let newtuples = groundtuples cntms funcs n (length fvs) in
		herbloopdnf mfn tfn fl0 cntms funcs fvs (n+1) fl tried newtuples
		
	else 
		let tup = head rest in
		let tups = tail rest in
		if(elem tup tried) then herbloopdnf mfn tfn fl0 cntms funcs fvs n fl tried tups
		else
			let sub = Map.fromList (zip fvs tup) in
			let fl' = simpdnf (subst2 sub fl0) in
			if testfb (dnfAnd fl fl') then--(n>=3) then 
				(tup:tried)
			else
				herbloopdnf mfn tfn fl0 cntms funcs fvs n (dnfAnd fl fl') (tup:tried) tups

-- Vorsicht die sind unterschiedlich
herbloopcnf mfn tfn fl0 cntms funcs fvs n fl tried rest =
	if null rest then
		let newtuples = groundtuples cntms funcs n (length fvs) in
		herbloopcnf mfn tfn fl0 cntms funcs fvs (n+1) fl tried newtuples
		
	else 
		let tup = head rest in
		let tups = tail rest in
		if(elem tup tried) then herbloopcnf mfn tfn fl0 cntms funcs fvs n fl tried tups
		else
			let sub = Map.fromList (zip fvs tup) in
			let fl' = simpcnf (subst2 sub fl0) in
			if not $ tfncnf (cnfAnd fl fl') then--(n>=3) then 
				(tup:tried)
			else
				herbloopcnf mfn tfn fl0 cntms funcs fvs n (cnfAnd fl fl') (tup:tried) tups



gilmorednf fm =
	let sfm = skolemize(Not(generalize fm)) in
	let funcs = functions sfm in
	let cntms = [(Fn "c" [])] in
	let fvs = fv sfm in
	herbloopdnf (Top) [] (sfm) cntms funcs fvs 0 (top1) [] [] 
gilmorecnf fm =
	let sfm = skolemize(Not(generalize fm)) in
	let funcs = functions sfm in
	let cntms = [(Fn "c" [])] in
	let fvs = fv sfm in
	herbloopcnf (Top) [] (sfm) cntms funcs fvs 0 (top2) [] [] 

--p45 mittle schlimm 
--p24 einfach
--p20 speicher schlimm
p45 = parse "(forall x. P(x) /\\ (forall y. G(y) /\\ H(x,y) ==> J(x,y)) ==> (forall y. G(y) /\\ H(x,y) ==> R(y))) /\\ ~(exists y. L(y) /\\ R(y)) /\\ (exists x. P(x) /\\ (forall y. H(x,y) ==> L(y)) /\\ (forall y. G(y) /\\ H(x,y) ==> J(x,y))) ==> (exists x. P(x) /\\ ~(exists y. G(y) /\\ H(x,y)))"
p24 = parse "~(exists x. U(x) /\\ Q(x)) /\\ (forall x. P(x) ==> Q(x) \\/ R(x)) /\\ ~(exists x. P(x) ==> (exists x. Q(x))) /\\ (forall x. Q(x) /\\ R(x) ==> U(x)) ==> (exists x. P(x) /\\ R(x))"
p20 = parse "(forall x y. exists z. forall w. P(x) /\\ Q(y) ==> R(z) /\\ U(w)) ==> (exists x y. P(x) /\\ Q(y)) ==> (exists z. R(z))"


t1 = groundterms [(Fn "0" []), (Fn "1" [])] [("f", 1)] 1
t2 = groundtuples [(Fn "0" []), (Fn "1" [])] [("f", 1)] 0 1
t3 = groundtuples [(Fn "0" []), (Fn "1" [])] [("f", 1)] 1 1
t4 = groundterms [(Fn "0" [])] [("s", 1)] 10
t5 = groundterms [(Fn "1" [])] [("add", 2)] 1
t6 = groundterms [(Fn "0" [])] [("add", 2), ("succ", 1)] 3



drink = parse "exists x. forall y. D(x) ==> D(y)"
sfm = skolemize(Not(generalize drink))
t7 = gilmorednf drink
t8 = gilmorecnf drink
d1 = simpcnf $ parse "D(c())"
d2 = simpcnf $ parse "~D(c())"

d3 = cnfAnd d1 d2
d4 = simpcnf $ parse "D(c()) /\\ ~D(c())"
d5 = head $ Set.toList $ head $ Set.toList d4
d6 = head $ Set.toList $ last $ Set.toList d4

-- to cnf fur DL
doge cnf = 
	let x = Set.toList cnf in
	[[ c | c <- Set.toList y] | y <- x]

toProp::Formula FOL->Formula Prop
toProp fm = 
	case fm of
		Atom a -> Atom (P $ show(fm))
		Not f -> Not $ Atom (P $ show(f))

--main = show(p45)

