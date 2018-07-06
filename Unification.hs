module Unification where


import Parsing_FOL
import Printer_FOL
import Vortrag1
import DefCnf
import FirstOrder
import Data.String
import Data.List
import qualified Data.Map as Map



-- Chapter 3.9 Unification --



-- istriv checks if a substitution is trivial, cylic or valid

istriv :: Map.Map String Term -> String -> Term -> Bool
--istriv env x (Var y) = y == x || (Map.member y env && istriv env x (env Map.! y))
istriv env x (Var y) = 
  case Map.lookup y env of
    Just _ -> y == x || istriv env x (env Map.! y) -- (True && istriv env x (env Map.! y))
    Nothing -> y == x -- || (False && istriv env x (env Map.! y))
istriv env x (Fn f args) = if (True `elem` [istriv env x arg | arg <- args])
  then error "cyclic"
  else False


-- core function

unify :: Map.Map String Term -> [(Term, Term)] -> Map.Map String Term
unify env eqs =
  case eqs of
    [] -> env
    ((Fn f fargs), (Fn g gargs)):oth -> if f == g && length fargs == length gargs
      then unify env (zip fargs gargs ++ oth)
      else error "impossible unification"
    (Var x, t):oth -> if (Map.member x env)
      then unify env ((env Map.! x,t):oth)
      else unify (if istriv env x t then env else Map.insert x t env) oth
    (t, Var x):oth -> unify env ((Var x,t):oth)


-- brings env to a fully solved form

solve :: Map.Map String Term -> Map.Map String Term
solve env =
    let env' = Map.map (tsubst2 env) env in
    if env' == env then env
    else solve env'


-- solves unification problem completely

fullunify :: [(Term, Term)] -> Map.Map String Term
fullunify eqs = solve (unify Map.empty eqs)


-- test function to check that the terms are indeed unified

unify_and_apply :: [(Term, Term)] -> [(Term, Term)]
unify_and_apply eqs = 
  let i = fullunify eqs in
  let apply (t1,t2) = (tsubst2 i t1, tsubst2 i t2) in
  map apply eqs


test0 = [(Fn "f" [Var "x", Fn "g" [Var "y"]], Fn "f" [Fn "f" [Var "z"], Var "w"])]
test1 = [(Fn "f" [Var "x", Var "y"], Fn "f" [Var "y", Var "x"])]
failtest0 = [(Fn "f" [Var "x", Fn "g" [Var "y"]], Fn "f" [Var "y", Var "x"])]
failtest1 = [(Fn "f" [Var "x"], Fn "g" [Var "x"])]
exptest = [(Var "x_0", Fn "f" [Var "x_1", Var "x_1"]), (Var "x_1", Fn "f" [Var "x_2", Var "x_2"]), (Var "x_2", Fn "f" [Var "x_3", Var "x_3"])]




