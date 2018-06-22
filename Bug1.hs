module MyVortrag where

import DNF

import DefCnf
import FirstOrder

--import qualified Data.Map as Map
--import qualified Data.Set as Set
--import NNF
import Parsing_FOL
import Printer_FOL
import Vortrag1

snf = parse "D(x) ==> D(f_y(x))"

fm = parse "exists x. forall y. D(x) ==> D(y)"

gilmore fm =
  let sfm = skolemize (Not (generalize fm))
   in sfm

-- Bugfix
askolemize1 :: Formula FOL -> Formula FOL
askolemize1 fm = fst (skolem (nnf2 (simplify fm)) (map fst (functions fm)))

skolemize1 :: Formula FOL -> Formula FOL
skolemize1 fm = specialize (pnf (askolemize1 fm))

gilmore1 fm =
  let sfm = skolemize1 (Not (generalize fm))
   in sfm
