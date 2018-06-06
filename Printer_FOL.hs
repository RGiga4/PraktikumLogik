-- Printing of formulas --
-- After Harrison "Handbook ... "
module Printer_FOL
  ( pprint
  , print_formula
  , print_formula1
  , print_term
  ) where

import Data.String
import Parsing_FOL
import Prelude hiding ((<>))
import Text.PrettyPrint.HughesPJ ((<+>), (<>), hcat, text)
                        -- forgets all quantifier, we need to flag them later.

import qualified Text.PrettyPrint.HughesPJClass as PP

----------- FOL Printer Appendix 3
-------- bracket function without openbox is pointless...
strip_quant fm =
  case fm of
    Forall x (Forall y p) ->
      let (xs, q) = strip_quant (Forall y p)
       in (x : xs, q)
    Exists x (Exists y p) ->
      let (xs, q) = strip_quant (Exists y p)
       in (x : xs, q)
    Forall x p -> ([x], p)
    Exists x p -> ([x], p)
    _ -> ([], fm) ------ print_formula mutually recursive functions ------

print_qnt pfn qname (bvs, bod) =
  hcat
    ([PP.text qname] ++
     map (\v -> PP.space <> PP.text v) bvs ++ [PP.text "."] ++ [PP.space]) <>
  print_formula pfn 0 bod

print_prefix pfn newpr sym p = (PP.text sym) <> print_formula pfn (newpr + 1) p

print_infix pfn newpr sym p q =
  print_formula pfn (newpr + 1) p <+>
  text sym <> PP.space <> print_formula pfn newpr q

print_formula pfn pr fm =
  case fm of
    Top -> PP.text "false"
    Bottom -> PP.text "true"
    Atom (pargs) -> pfn pr pargs
    Not p -> PP.maybeParens (pr > 10) (print_prefix pfn 10 "~" p)
    And p q -> PP.maybeParens (pr > 8) (print_infix pfn 8 "/\\" p q)
    Or p q -> PP.maybeParens (pr > 6) (print_infix pfn 6 "\\/" p q)
    Imp p q -> PP.maybeParens (pr > 4) (print_infix pfn 4 "==>" p q)
    Iff p q -> PP.maybeParens (pr > 2) (print_infix pfn 2 "<=>" p q)
    Forall x p ->
      PP.maybeParens (pr > 0) (print_qnt pfn "forall" (strip_quant fm))
    Exists x p ->
      PP.maybeParens (pr > 0) (print_qnt pfn "exists" (strip_quant fm))

print_formula1 pfn = print_formula pfn 0
        -------- first-order term printer, used to print formulas --------

print_term prec fm =
  case fm of
    Var x -> text x
    Fn "^" [tm1, tm2] -> print_infix_term True prec 24 "^" tm1 tm2
    Fn "/" [tm1, tm2] -> print_infix_term True prec 22 " /" tm1 tm2
    Fn "*" [tm1, tm2] -> print_infix_term False prec 20 " *" tm1 tm2
    Fn "-" [tm1, tm2] -> print_infix_term True prec 18 " -" tm1 tm2
    Fn "+" [tm1, tm2] -> print_infix_term True prec 16 " +" tm1 tm2
    Fn "::" [tm1, tm2] -> print_infix_term True prec 14 "::" tm1 tm2
    Fn f args -> print_fargs f args

print_fargs f args =
  PP.text f <>
  if args == []
    then PP.empty
    else (PP.text "(" <> print_term 0 (head args) <+>
          hcat
            (map (\t -> PP.comma <> PP.space <> print_term 0 t) (tail args) ++
             [PP.rparen]))

print_infix_term isleft oldprec newprec sym p q =
  if oldprec > newprec
    then (PP.lparen)
    else PP.empty <>
         print_term
           (if isleft
              then newprec
              else newprec + 1)
           p <>
         PP.text sym <>
         PP.space <>
         print_term
           (if isleft
              then newprec + 1
              else newprec)
           q <>
         if oldprec > newprec
           then (PP.rparen)
           else PP.empty

printert tm = print_term 0 tm
        --------- first-order formula printer, substituted for pfn -----

print_atom prec (R p args) =
  if elem p ["=", "<", "<=", ">="] && length args == 2
    then print_infix_term False 12 12 (" " ++ p) (args !! 0) (args !! 1)
    else print_fargs p args
        ----- print_fol_formula

pprint = print_formula1 print_atom
--------- Propositional Logic Printer-- Ist in Vortrag 1 einfgefügt
--pname (P s) = s
--
--print_propvar prec p = PP.text (pname p)
--
--print_prop_formula = print_formula1 print_propvar
