module DNF where

import Parsing_FOL
import Vortrag1
import NNF
import qualified Data.Set as Set

-- Conjuncts all formulas
list_conj :: [Formula a] -> Formula a
list_conj = foldr conj Top
    where conj p acc = case acc of
              Top -> p
              _   -> And p acc 

-- Disjuncts all formulas
list_disj :: [Formula a] -> Formula a
list_disj = foldr disj Bottom
    where disj p acc = case acc of
              Bottom -> p
              _      -> Or p acc

-- Conjucts all formulas or their negation depending on their valuation
mk_lits :: [Formula a] -> (a -> Bool) -> Formula a
mk_lits pvs v = list_conj (map satisfied pvs)
    where satisfied p = if eval p v then p else Not p

-- Collects all valuations for which subfn is satisfied
allsatvaluations subfn v pvs = case pvs of
    []   -> if subfn v then [v] else []
    p:ps -> let v' t q = if q == p then t else v q
            in allsatvaluations subfn (v' False) ps ++ 
               allsatvaluations subfn (v' True) ps

-- Converts formula to DNF using the truthtable
dnf fm = let pvs = atoms fm
             satvals = allsatvaluations (eval fm) (\p -> False) pvs
         in list_disj $ map (mk_lits $ map (\p -> Atom p) pvs) satvals



-- Applies distrubtive law recursively
distrib fm = case fm of
    And p (Or q r) -> Or (distrib $ And p q) (distrib $ And p r)
    And (Or p q) r -> Or (distrib $ And p r) (distrib $ And q r)
    _              -> fm

-- Converts formula into DNF using the distributive law recursively
rawdnf fm = case fm of
    And p q -> distrib $ And (rawdnf p) (rawdnf q)
    Or p q  -> Or (rawdnf p) (rawdnf q)
    _       -> fm



-- Applies destribution law in set notation
distrib_sets s1 s2 = Set.fromList $ 
    [Set.union sub1 sub2 | sub1 <- Set.toList s1, sub2 <- Set.toList s2]

-- Converts formula to DNF in set based representation
purednf fm = case fm of
    And p q -> distrib_sets (purednf p) (purednf q)
    Or p q  -> Set.union (purednf p) (purednf q)
    _       -> Set.singleton $ Set.singleton fm

-- Checks whether a conjunction has no contradicting members
nontrivial lits = let (pos, neg) = Set.partition positive lits
                  in Set.null $ Set.intersection pos $ Set.map opposite neg

-- Converts formula to DNF in set based representation and simplifies it
simpdnf fm = if fm == Bottom then Set.empty
             else if fm == Top then Set.singleton $ Set.empty
                  else let djs = Set.filter nontrivial (purednf $ nnf fm)
                           nonsuperset s = Set.null $ Set.filter (flip Set.isProperSubsetOf s) djs
                       in Set.filter nonsuperset djs

-- Converts formula to DNF using set based representation
dnf' :: Ord a => Formula a -> Formula a
dnf' = list_disj . (map $ list_conj . Set.toList) . Set.toList . simpdnf



-- Converts formula to CNF in set based representation
purecnf :: Ord a => Formula a -> Set.Set (Set.Set (Formula a))
purecnf = (Set.map (Set.map opposite)) . purednf . nnf . Not

-- Converts formula to cnf in set based representation and simplifies it
simpcnf :: Ord a => Formula a -> Set.Set (Set.Set (Formula a))
simpcnf fm = if fm == Bottom then Set.singleton $ Set.empty
             else if fm == Top then Set.empty
                  else let cjs = Set.filter nontrivial (purecnf fm)
                           nonsuperset s = Set.null $ Set.filter (flip Set.isProperSubsetOf s) cjs
                       in Set.filter nonsuperset cjs

-- Converts formula to CNF using set based representation
cnf :: Ord a => Formula a -> Formula a
cnf = list_conj . (map $ list_disj . Set.toList) . Set.toList . simpcnf
