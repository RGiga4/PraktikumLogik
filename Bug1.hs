module MyVortrag where

import DNF
--import qualified Data.Map as Map
--import qualified Data.Set as Set
--import NNF
import Parsing_FOL
import Printer_FOL
import DefCnf
import Vortrag1
import FirstOrder


snf = parse "D(x) ==> D(f_y(x))"

fm = parse "exists x. forall y. D(x) ==> D(y)"


gilmore fm =
	let sfm = skolemize(Not(generalize fm)) in
	sfm



