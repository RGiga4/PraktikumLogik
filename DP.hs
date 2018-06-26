module DavisPutnam where

import qualified Data.Map as Map
import Data.List
import Parsing_FOL
import Printer_FOL
import NNF
import DNF
import DefCnf

--unsatisfiable Example
unsatExample = [[Atom $ P "x",Atom $ P "y",Atom $ P "z"],[Atom $ P "x",Atom $ P "y",Not $ Atom $ P "z"],[Atom $ P "x",Not $ Atom $ P "y",Atom $ P "z"],[Atom $ P "x",Not $ Atom $ P "y",Not $ Atom $ P "z"],[Not $ Atom $ P "x",Atom $ P "y",Atom $ P "z"],[Not $ Atom $ P "x",Atom $ P "y",Not $ Atom $ P "z"],[Not $ Atom $ P "x",Not $ Atom $ P "y",Atom $ P "z"],[Not $ Atom $ P "x",Not $ Atom $ P "y",Not $ Atom $ P "z"]]
bigExample =  [[if mod a n == 0 then Atom $ P $ show (a*n) else Not $ Atom $ P $ show (a*n) | a <- [1..10], a*n < 1000] | n <- [1..10]]
example    =  [[Atom (P "blubb"), Atom (P "fisch")],[Atom (P "nase")], [Atom (P "fisch"), Not (Atom (P "nase")), Atom (P "zwerg")]]


lists_to_cnf :: [[Formula a]] -> Formula a
lists_to_cnf = list_conj.(map list_disj)


unions :: Eq a => [[a]] -> [a]
unions = nub.concat 

--Fügt x in Liste ein, wenn diese x nicht enthält
setinsert :: Eq t => t -> [t] 
                  -> [t]
setinsert x [] = [x]
setinsert x (y:ys) = if x == y then y:ys else y:setinsert x ys

allpairs :: (t1 -> t2 -> a) -> [t1] -> [t2] 
         -> [a]
allpairs f ks ls = [f x y | x <- ks, y <- ls]

--Wähle Element x aus liste, sd. f(x) minimal
minimize :: Ord a => (b -> a) -> [b] -> b
minimize f s = snd $ foldr1 (\a b -> if fst a < fst b then a else b)  $ map (\e -> (f e, e)) s

maximize :: Ord a => (b -> a) -> [b] -> b
maximize f s = snd $ foldr1 (\a b -> if fst a > fst b then a else b)  $ map (\e -> (f e, e)) s

--Wendet 1-literal rule an wenn möglich und hat sonst den Wert Nothing
one_literal_rule :: Eq a => [[Formula a]] -> Maybe [[Formula a]]
one_literal_rule clauses = do
                              u        <- case filter (\cl -> length cl == 1) clauses of
                                            [] -> Nothing 
                                            unit_clauses -> Just $ head $ head $ unit_clauses  
                              u'       <- Just $ opposite u
                              clauses1 <- Just $ filter (\cl -> not (elem u cl)) clauses
                              Just $ map (\cl -> filter (/= u') cl) clauses1

--Wendet affirmative negative rule an wenn möglich und hat sonst den Wert Nothing
affirmative_negative_rule :: Eq a => [[Formula a]] -> Maybe [[Formula a]]
affirmative_negative_rule clauses =
  let (neg', pos) = partition negative $ unions clauses
      neg = map opposite neg'
      pos_only = pos \\ neg 
      neg_only = neg \\ pos
      pure =  pos_only ++ (map opposite neg_only) --pos_only und (map opposite neg_only) sind disjunkt also kann ++ statt union verwendet werden
  in if null pure then Nothing
                          else Just $ filter (null.(intersect pure)) clauses 



nontrivial_list :: Eq a => [Formula a] -> Bool
nontrivial_list lits = 
  let (pos, neg) = partition positive lits
  in null $ intersect pos $ map opposite neg


resolve_on :: Ord a => Formula a -> [[Formula a]] 
                    -> [[Formula a]]
resolve_on p clauses = 
  let p' = opposite p
      (pos,notpos) = partition (elem p) clauses
      (neg,other) = partition (elem p') notpos
      pos' = map (filter (\l -> l /= p)) pos
      neg' = map (filter (\l -> l /= p')) neg
      res0 = allpairs union pos' neg'
  in union other $ filter nontrivial_list res0

resolution_blowup ::
  (Foldable t, Eq a) => [t (Formula a)] -> Formula a 
                     -> Int
resolution_blowup cls l =
  let m = length $ filter (elem l) cls
      n = length $ filter (elem (opposite l)) cls
  in m * n - m - n




resolution_rule :: Ord a => [[Formula a]] -> [[Formula a]]
resolution_rule clauses =
  let pvs = filter positive (unions clauses)
      p = minimize (resolution_blowup clauses) pvs
  in resolve_on p clauses


dp :: Ord a => [[Formula a]] -> Bool
dp clauses
   | null clauses = True
   | elem [] clauses =  False
   | otherwise = case one_literal_rule clauses of
                      Just x  -> dp x
                      Nothing -> case affirmative_negative_rule clauses of
                                 Just x -> dp x
                                 Nothing -> dp $ resolution_rule clauses

dpsat :: Formula Prop -> Bool
dpsat = dp.defcnfs

dptaut :: Formula Prop -> Bool
dptaut = not.dpsat.Not

posneg_count :: (Foldable t, Eq a) => [t (Formula a)] -> Formula a 
             -> Int
posneg_count cls l =
  let m = length $ filter (elem l) cls
      n = length $ filter (elem (opposite l)) cls
  in m + n

dpll :: Eq a => [[Formula a]] -> Bool
dpll clauses
  | null clauses = True
  | elem [] clauses = False
  | otherwise = case one_literal_rule clauses of
                    Just x  -> dpll x
                    Nothing -> case affirmative_negative_rule clauses of
                                    Just x -> dpll x
                                    Nothing -> let pvs = filter positive (unions clauses)
                                                   p = maximize (posneg_count clauses) pvs 
                                               in (dpll $ setinsert [p] clauses) ||
                                                  (dpll $ setinsert [opposite p] clauses)

dpllsat :: Formula Prop -> Bool
dpllsat  = dpll.defcnfs

dplltaut :: Formula Prop -> Bool
dplltaut = not.dpllsat.Not


data Trailmix = Guessed | Deduced deriving Eq

--Alle Literale aus cls denen im trail kein Wert zugewiesen wird
unassigned :: Eq a => [[Formula a]] -> [(Formula a, b)] 
                   -> [Formula a]
unassigned cls trail =
    let litabs (Not q) = q
        litabs q = q in
    (unions $ map (map litabs) cls) \\ (map (litabs.fst) trail)

--Wende f auf alle Elemente der Liste an und entferne alle Elemente x mit f x == Nothing
mapfilter :: (t -> Maybe a) -> [t] -> [a]
mapfilter f [] = []
mapfilter f (x:xs) = 
    case f x of
      Nothing -> mapfilter f xs
      Just x  -> x : mapfilter f xs

--Wir verwenden eine Map, um uns zu merken welche Literale sich im trail befinden,
--da man bei einer Map schnell prüfen kann ob sie auf einem Element definiert ist.
unit_subpropagate :: Ord a => ([[Formula a]], Map.Map (Formula a) (), [(Formula a, Trailmix)])
                           -> ([[Formula a]], Map.Map (Formula a) (), [(Formula a, Trailmix)])
unit_subpropagate (cls,fn,trail) =
   let cls' = map (filter (not.(`Map.member` fn).opposite)) cls --alle Literale die durch den trail den Wert False zugeschrieben bekommen  
                                                                --(d.h. deren negation im trail ist) werden entfernt
       uu [c] = if not $ Map.member c fn then Just [c] else Nothing  
       uu _ = Nothing
       newunits = unions $ mapfilter uu cls' in --newunits beinhaltet alle Einheitsklauseln, denen fn noch keinen Wert zuweist
    if null newunits then (cls', fn, trail) else 
      let trail' = foldr (\p t -> (p,Deduced):t) trail newunits --Alle Einheitsklauseln in cls' werden im trail zusammen mit 
                                                                --der flag Deduced gespeichert, um zu markieren, dass diese abgeleitet wurden#
                                                                --(Damit stehen ihre Werte fest) 
          fn' = foldr (\u -> Map.insert u ()) fn newunits in
      unit_subpropagate (cls',fn',trail')

--Wie unit_subpropagte, aber fn wird verworfen, da es nicht mehr gebraucht wird 
unit_propagate (cls,trail) =
    let fn = foldr (\(x,_) -> Map.insert x ()) Map.empty trail 
        (cls', _ , trail') = unit_subpropagate (cls,fn,trail) in (cls',trail')

--Springe an die letzte Stelle im trail zurück an der eine 
--Entscheidung getroffen wurde, d.h. an der der Wert eines Literals geraten wurde
backtrack :: [(a, Trailmix)] -> [(a, Trailmix)]
backtrack ((p,Deduced):tt) = backtrack tt
backtrack trail = trail


dpli :: (Eq a, Ord a) => [[Formula a]] -> [(Formula a, Trailmix)] 
                      -> Bool
dpli cls trail =
    let (cls',trail') = unit_propagate (cls,trail) in --Leite möglichst viele Literale ab
    if elem [] cls' then --Wenn es einen Konflikt gibt,
      case backtrack trail of --springe zurück bis zur letzten Entscheidung, d.h. bis zum letzten geratenen Literal
        (p,Guessed):tt -> dpli cls ((opposite p,Deduced):tt) --Gibt es eine, so muss das negierte Literal gelten
        _ -> False --Gibt es keine, so ist die Formel nicht erfüllbar 
    else
      case unassigned cls trail' of --Sonst suche Literal aus, dem noch kein Wert zugewiesen wurde
        [] -> True -- Gibt es keine, so haben wir eine Zuweisung, die die Formel erfüllt 
        ps -> let p = maximize (posneg_count cls') ps in --Gibt es solche, so wähle das mit dem größten posneg_count
              dpli cls ((p,Guessed):trail') 


dplisat :: Formula Prop -> Bool
dplisat fm = dpli (defcnfs fm) []
dplitaut :: Formula Prop -> Bool
dplitaut = not.dplisat.Not 

--Springe im Trail zurück, solange die Annahme p=True zu einem Konflikt führt ("Non-chronological back jumping")
backjump :: (Eq a, Ord a) => [[Formula a]] -> Formula a -> [(Formula a, Trailmix)] 
                          -> [(Formula a, Trailmix)]
backjump cls p trail =
    case backtrack trail of
      (q,Guessed):tt -> let (cls',trail') = unit_propagate (cls,(p,Guessed):tt) in
                        if elem [] cls' then backjump cls p tt else trail
      _ -> trail


dplb :: (Eq a,Ord a) => [[Formula a]] -> [(Formula a, Trailmix)] -> Bool
dplb cls trail =
    let (cls',trail') = unit_propagate (cls,trail) in
    if elem [] cls' then
      case backtrack trail of
        (p,Guessed):tt ->
          let trail' = backjump cls p tt --Springe zurück, solange die aktuellste Entscheidung zu einem Konflikt führt
              decisonlits = filter (\(_,d) -> d == Guessed) trail' --Dann lässt sich der Konflikt aus allen geratenen Literalen ableiten
                                                                   --Also kann die Konjunktion dieser Literale nicht gelten 
              conflict = setinsert (opposite p) (map (opposite.fst) decisonlits) in -- => Es gilt die Disjunktion der Negationen der Literale (also die conflict Klausel)
          dplb (conflict:cls) ((opposite p,Deduced):trail') --Also haben wir eine neue Klausel, die erfüllt sein muss ("Conflict-Driven-Learning")
        _ -> False
    else case unassigned cls trail' of
        [] -> True
        ps -> let p = maximize (posneg_count cls') ps in
              dplb cls $ (p,Guessed):trail'


dplbsat :: Formula Prop -> Bool
dplbsat fm = dplb (defcnfs fm) []
dplbtaut :: Formula Prop -> Bool
dplbtaut = not.dplbsat.Not
