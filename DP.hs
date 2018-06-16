module DavisPutnam where


import qualified Data.Map as Map
import Data.List
import Parsing_FOL
import Printer_FOL
import Text.PrettyPrint.HughesPJClass as PP
import Vortrag1
import NNF
import DNF
import DefCnf
import Debug.Trace as D
import FPF



bigExample =  [[if mod a n == 0 then Atom $ P $ show (a*n) else Not $ Atom $ P $ show (a*n) | a <- [1..10], a*n < 1000] | n <- [1..10]]
example    =  [[Atom (P "blubb"), Atom (P "fisch")],[Atom (P "nase")], [Atom (P "fisch"), Not (Atom (P "nase")), Atom (P "zwerg")]]
-- {{blubb, fisch}, {nase}, {fisch, Not nase, zwerg}}


--negative :: Formula a -> Bool
--negative q =
--  case q of
--    (Not p) -> True
--    _ -> False


--opposite :: Formula a -> Formula a
--opposite q =
--  case q of
--    (Not p) -> p
--    p -> (Not p)






lists_to_cnf = list_conj.(map list_disj)

unions :: Eq a => [[a]] -> [a]
unions = nub.concat

setinsert x [] = [x]
setinsert x (y:ys) = if x == y then y:ys else y:setinsert x ys

allpairs f ks ls = [f x y | x <- ks, y <- ls]


one_literal_rule' clauses = do
                              u        <- if filter (\cl -> length cl == 1) clauses == []
                                            then Nothing
                                            else Just $ head $ head $ filter (\cl -> length cl == 1) clauses
                              u'       <- Just $ opposite u
                              clauses1 <- Just $ filter (\cl -> not (elem u cl)) clauses
                              Just $ map (\cl -> filter (/= u') cl) clauses1

one_literal_rule cls = case one_literal_rule' cls of
                            Just x -> x
                            _ -> error  "one_literal_rule"

affirmative_negative_rule' clauses =
  let (neg', pos) = partition negative $ unions clauses
      neg = map opposite neg'
      pos_only = pos \\ neg 
      neg_only = neg \\ pos
      pure =  pos_only ++ (map opposite neg_only) -- !! 
  in if pure == [] then Nothing
                          else Just $ filter (null.(intersect pure)) clauses -- !!


affirmative_negative_rule cls = case affirmative_negative_rule' cls of
                                     Just x -> x
                                     _ -> error "affirmative_negative_rule"

nontrivial_list :: (Eq a) => [Formula a] -> Bool
nontrivial_list lits = 
  let (pos, neg) = partition positive lits
  in null $ intersect pos $ map opposite neg

resolve_on :: Ord a => Formula a -> [[Formula a]] -> [[Formula a]]
resolve_on p clauses = 
  let p' = opposite p
      (pos,notpos) = partition (elem p) clauses
      (neg,other) = partition (elem p') notpos
      pos' = map (filter (\l -> l /= p)) pos
      neg' = map (filter (\l -> l /= p')) neg
      res0 = allpairs union pos' neg'
  in union other(filter nontrivial_list res0)

resolution_blowup cls l =
  let m = length $ filter (elem l) cls
      n = length $ filter (elem (opposite l)) cls
  in m * n - m - n



minimize f s = snd $ foldr1 (\a b -> if fst a < fst b then a else b)  $ map (\e -> (f e, e)) s

maximize f s = snd $ foldr1 (\a b -> if fst a > fst b then a else b)  $ map (\e -> (f e, e)) s

resolution_rule clauses =
  let pvs = filter positive (unions clauses)
      p = minimize (resolution_blowup clauses) pvs
  in resolve_on p clauses


dp clauses
   | clauses == [] = True
   | elem [] clauses =  False
   | otherwise = case one_literal_rule' clauses of
                      Just x  -> dp x
                      Nothing -> case affirmative_negative_rule' clauses of
                                 Just x -> dp x
                                 Nothing -> dp $ resolution_rule clauses

dpsat = dp.defcnfs

dptaut = not.dpsat.Not

posneg_count cls l =
  let m = length $ filter (elem l) cls
      n = length $ filter (elem (opposite l)) cls
  in m + n

dpll clauses
  | clauses == [] = True
  | elem [] clauses = False
  | otherwise = case one_literal_rule' clauses of
                    Just x  -> dpll x
                    Nothing -> case affirmative_negative_rule' clauses of
                                    Just x -> dpll x
                                    Nothing -> let pvs = filter positive (unions clauses)
                                                   p = maximize (posneg_count clauses) pvs 
                                               in (dpll $ setinsert [p] clauses) ||
                                                  (dpll $ setinsert [opposite p] clauses)

dpllsat  = dpll.defcnfs

dplltaut = not.dpllsat.Not


data Trailmix = Guessed | Deduced deriving Eq


unassigned cls trail =
    let litabs (Not q) = q
        litabs q = q in
    (unions $ map (map litabs) cls) \\ (map (litabs.fst) trail)

mapfilter f [] = []
mapfilter f (x:xs) = 
    case f x of
      Nothing -> mapfilter f xs
      Just x  -> x : mapfilter f xs

unit_subpropagate (cls,fn,trail) =
   let cls' = map (filter (not.(defined fn).opposite)) cls
       uu [c] = if not $ defined fn c then Just [c] else Nothing
       uu _ = Nothing
       newunits = unions $ mapfilter uu cls' in
   if newunits == [] then (cls' ,fn,trail) else
    let trail' = foldr (\p t -> (p,Deduced):t) trail newunits
        fn' = foldr (\u -> (u |-> ())) fn newunits in
    unit_subpropagate (cls',fn',trail')



unit_propagate (cls,trail) =
    let fn = foldr (\(x,_) -> (x |-> ())) undefinedf trail 
        (cls', fn', trail') = unit_subpropagate (cls,fn,trail) in (cls',trail')


backtrack ((p,Deduced):tt) = backtrack tt
backtrack trail = trail


dpli cls trail =
    let (cls',trail') = unit_propagate (cls,trail) in
    if elem [] cls' then
      case backtrack trail of
        (p,Guessed):tt -> dpli cls ((opposite p,Deduced):tt)
        _ -> False
    else
      case unassigned cls trail' of
        [] -> True
        ps -> let p = maximize (posneg_count cls') ps in
              dpli cls ((p,Guessed):trail')


dplisat fm = dpli (defcnfs fm) []
dplitaut = not.dplisat.Not 

backjump cls p trail =
    case backtrack trail of
      (q,Guessed):tt -> let (cls',trail') = unit_propagate (cls,(p,Guessed):tt) in
                        if elem [] cls' then backjump cls p tt else trail
      _ -> trail


dplb cls trail =
    let (cls',trail') = unit_propagate (cls,trail) in
    if elem [] cls' then
      case backtrack trail of
        (p,Guessed):tt ->
          let trail' = backjump cls p tt 
              declits = filter (\(_,d) -> d == Guessed) trail' 
              conflict = setinsert (opposite p) (map (opposite.fst) declits) in
          dplb (conflict:cls) ((opposite p,Deduced):trail')
        _ -> False
    else case unassigned cls trail' of
        [] -> True
        ps -> let p = maximize (posneg_count cls') ps in
              dplb cls $ (p,Guessed):trail'


dplbsat fm = dplb (defcnfs fm) []
dplbtaut = not.dplbsat.Not
