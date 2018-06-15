module MyVortrag where

--import DNF
--import qualified Data.Map as Map
--import qualified Data.Set as Set
--import NNF
import Parsing_FOL
import Printer_FOL
--import Vortrag1

-- soll Terme mit n funktion geben
--groundterms :: [a] -> [b] -> c -> [d]
groundterms cntms funcs n 
	| n == 0 = cntms
	| otherwise =  [(fst f)++" "++x | f  <- funcs, x <- groundtuples cntms funcs (n-1) (snd f)]

-- soll Terme fur m stellen und mit n funtionen geben
groundtuples cntms funcs n m =
	if m == 0 then 	
		if n == 0 then [""]
		else []
	else [x1 ++" "++ x2| k <- [0..n], x1 <- groundterms cntms funcs k, 
		x2 <- groundtuples cntms funcs (n-k) (m-1) ]
	


t1 = groundterms ["0","1"] [("f", 1)] 1
t2 = groundtuples ["0","1"] [("f", 1)] 0 1
t3 = groundtuples ["0","1"] [("f", 1)] 1 1
t4 = groundterms ["0"] [("f", 1)] 10
t5 = groundterms ["1"] [("add", 2)] 3
t6 = groundterms ["0"] [("add", 2), ("s", 1)] 3
