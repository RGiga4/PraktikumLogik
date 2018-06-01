import Parsing_FOL
import Data.List


test = parse_prop_formula "p /\\ q ==> q /\\ r"
und = parse_prop_formula "p /\\ q"
oder = parse_prop_formula "p \\/ q"
test2 = Imp oder und
taut1 = parse_prop_formula "p \\/ ~p"
taut2 = parse_prop_formula "(p \\/ q) /\\ ~(p /\\ q) ==> (~p <=> q)"
taut3 = parse_prop_formula "(p /\\ true) <=> p"


-- Test wahrheitsbelegung
tt (P "p") = True
tt (P "q") = False
tt (P "r") = True
tt _ = False




data Prop = P String deriving (Show, Eq)



pname :: Prop -> String
pname (P s) = s


parse_propvar :: [String] -> (Formula Prop, [String])
parse_propvar (p:oinp)
    | p /= "(" = (Atom (P p), oinp)
parse_propvar _ = error "parse_propvar"


parse_prop_formula :: String -> Formula Prop
parse_prop_formula = make_parser (parse_formula parse_propvar)

print_propvar :: Prop -> String
print_propvar (P s) = show s



mk_and :: Formula Prop -> Formula Prop -> Formula Prop
mk_and p q = (And p q)

mk_or p q = (Or p q)

dest_iff :: Formula Prop -> (Formula Prop, Formula Prop)
dest_iff (Iff p q) = (p, q)
dest_iff _ = error "dest_iff"

dest_and (And p q) = (p, q)
dest_and _ = error "dest_and"

dest_or (Or p q) = (p, q)
dest_or _ = error "dest_or"

conjuncts :: Formula Prop -> [Formula Prop]
conjuncts (And p q) = (conjuncts p) ++ (conjuncts q)
conjuncts fm = [fm]

disjuncts (Or p q) = (disjuncts p) ++ (disjuncts q)
disjuncts fm = [fm]

dest_imp (Imp p q) = (p, q)
dest_imp _ = error "dest_imp"

antecedent (Imp p q) = p
consequent (Imp p q) = q


onatoms :: (a -> Formula a) -> Formula a -> Formula a
onatoms f fm = case fm of
    Atom a -> f a
    Not p -> (Not (onatoms f p))
    And p q -> And (onatoms f p) (onatoms f q)
    Or p q -> Or (onatoms f p) (onatoms f q)
    Imp p q -> Imp (onatoms f p) (onatoms f q)
    Iff p q -> Iff (onatoms f p) (onatoms f q)
    Forall x p -> Forall x (onatoms f p)
    Exists x p -> Exists x (onatoms f p)
    _ -> fm


overatoms :: (a -> b -> b) -> Formula a -> b -> b
overatoms f fm b = case fm of
    Atom a -> f a b
    Not p -> overatoms f p b
    And p q -> overatoms f p (overatoms f q b)
    Or p q -> overatoms f p (overatoms f q b)
    Imp p q -> overatoms f p (overatoms f q b)
    Iff p q -> overatoms f p (overatoms f q b)
    Forall x p -> overatoms f p b
    Exists x p -> overatoms f p b
    _ -> b


atom_union :: (Eq b) => (a -> [b]) -> Formula a -> [b]
atom_union f fm = nub $ overatoms (\h t -> (f h) ++ t) fm []


atoms :: (Eq a) => Formula a -> [a]
atoms fm = atom_union (\a -> [a]) fm


eval :: Formula a -> (a -> Bool) -> Bool
eval fm v = case fm of
    Bottom -> False
    Top -> True
    (Atom x) -> v x
    (Not p) -> not $ eval p v
    (And p q) -> eval p v && eval q v
    (Or p q) -> eval p v || eval q v
    (Imp p q) -> not (eval p v) || eval q v
    (Iff p q) -> eval p v == eval q v




onallvaluations :: (Eq a) => ((a -> Bool) -> Bool) -> (a -> Bool) -> [a] -> Bool
onallvaluations subfn v ats = case ats of
    [] -> subfn v
    p:ps -> let v' t q = if q == p then t else v q in
                onallvaluations subfn (v' False) ps &&
                 onallvaluations subfn (v' True) ps



print_truthtable :: Formula Prop -> IO ()
print_truthtable fm =
    let ats = atoms fm in
    let width = 6 + ((length . pname . (maximumBy (\(P s) (P t) -> compare (length s) (length t)))) ats) in
    let fixw s = s ++ (take (width - (length s)) (repeat ' ')) in
    let truthstring p = fixw (if p then "true" else "false") in
    let mk_row v =  let lis = map (\ x -> truthstring (v x)) ats
                        ans = truthstring (eval fm v)
                    in putStrLn ((unwords lis) ++ "| " ++ ans) in
    let separator = take (width * (length ats) + 9) (repeat '-') in
    let printer v ats1 = case ats1 of
            [] -> mk_row v
            (p:ps) ->   let v' t q = if q == p then t else v q 
                        in (printer (v' False) ps) >> (printer (v' True) ps)
    in do   putStrLn ((concatMap (\ (P s) -> fixw s) ats) ++ "| formula")
            putStrLn separator
            printer (\ x -> False) ats




tautology :: (Eq a) => Formula a -> Bool
tautology fm = onallvaluations (eval fm) (\s -> False) (atoms fm)

unsatisfiable fm = tautology (Not fm)

satisfiable fm = not (unsatisfiable fm)


psubst :: (a -> Formula a) -> Formula a -> Formula a 
psubst subfn = onatoms subfn


dual :: Formula a -> Formula a
dual fm = case fm of
    Bottom -> Top
    Top -> Bottom
    Atom p -> fm
    Not p -> Not (dual p)
    And p q -> Or p q
    Or p q -> And p q
    _ -> error "Formula involves connectives ==> or <=>"




























