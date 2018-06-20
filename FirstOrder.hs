module FirstOrder where

import Parsing_FOL
import Printer_FOL
import Vortrag1
import NNF
import Data.String
import Data.List
import qualified Data.Map as Map




--3.3/3.4

--fvt gibt Liste der freien Variablen eines Terms zuück--
fvt:: Term->[String]
fvt tm=
       case tm of
                Var x -> [x]
                Fn f args -> nub (concat (map fvt args)) 



--fv gibt freie Variablen einer Formel zurück--
fv::Formula FOL->[String]
fv fm=
    case fm of
        Bottom->[]
        Top->[]
        Not p->fv p
        Atom ( R p args)->nub ( concat (map fvt args))
        And p q ->union (fv p)(fv q)
        Iff p q->union (fv p) (fv q)
        Imp p q ->union (fv p)(fv q)
        Or p q ->union (fv p)(fv q)
        Forall x p->filter (x/=) (fv p)
        Exists x p ->filter (x/=) (fv p)

--generalize bindet alle freien Variablen einer Formel mit einem Allquantor--
generalize::Formula FOL->Formula FOL
generalize fm=iterate_forall (fv fm) fm
    where iterate_forall (x:xs) fm'=iterate_forall xs (Forall x fm')
          iterate_forall [] fm'=fm'  

--tsubst wendet eine subfunktion sfn auf alle Variablen eines Terms an--
--subfn darf keine undefinierten Werte haben
tsubst::(String->Term)->Term->Term
tsubst subfn tm=
    case tm of
        Var x-> subfn x  
        Fn f args-> Fn f (map (tsubst subfn) args)


--tsubst2 ist eine Variante von tsubst die stattdessen eine Map verwendet
tsubst2:: (Map.Map String Term)->Term->Term
tsubst2 submap tm=
    case tm of 
        Var x-> if (Map.member x submap) then (submap Map.! x) else Var x
        Fn f args-> Fn f (map (tsubst2 submap) args)

--variant fügt zu einer gegebenen Variable x solange "'" hinzu bis die neue Variable nicht mehr in einer gegebenen Menge auftritt--
variant::String->[String]->String--
variant x vars=if (elem x vars) then variant (x++"'") vars else x

--subst wendet subfunktion auf alle freien Variablen einer Formel an--

subst::(String->Term)->Formula FOL->Formula FOL
subst subfn fm=    
    case fm of
        Bottom->Bottom
        Top->Top
        Atom(R p args)->Atom(R p (map (tsubst subfn) args)) 
        Not p->Not (subst subfn p) 
        And p q->And (subst subfn p) (subst subfn q) 
        Or p q ->Or (subst subfn p) (subst subfn q) 
        Imp p q ->Imp (subst subfn p) (subst subfn q) 
        Iff p q ->Iff (subst subfn p) (subst subfn q) 
        Forall x p ->substq subfn Forall x p 
        Exists x p ->substq subfn Exists x p
    where 
          substq subfn quant x  p=
            let x'= if (any (\y->elem x (fvt(subfn y ))) (filter (x/=) (fv p))) 
                then variant x (fv (subst (\z->if z==x then Var x else subfn z) p)) else x in
              quant x' (subst (\w->if w==x then Var x' else subfn w) p)

--subst2 wie subst, nur mit Map statt Funktion
subst2::(Map.Map String Term)->Formula FOL->Formula FOL
subst2 submap fm=    
    let subfn x=if (Map.member x submap) then (submap Map.! x) else (Var x) 
    in subst subfn fm   

--3.5 Prenex Normalform

--Hilfsfunktion die psimplify1 verallgemeinert--

simplify1::Formula FOL->Formula FOL
simplify1 fm=
    case fm of
        Exists x p -> if elem x (fv p) then fm  else p
        Forall x p -> if elem x (fv p) then fm  else p
        _->psimplify1 fm --psimplyf1 entfernt Tops und Bottoms

--entfernt überschüssige Quantifizerungen, Tops und Bottoms--
simplify::Formula FOL->Formula FOL
simplify fm=
    case fm of
        And p q ->simplify1 (And (simplify p) (simplify q))
        Or p q ->simplify1 (Or (simplify p)  (simplify q))
        Imp p q ->simplify1 (Imp (simplify p)  (simplify q)) 
        Iff p q ->simplify1 (Iff (simplify p)(simplify q))
        Forall x p ->simplify1 (Forall x (simplify p ))
        Exists x p ->simplify1 (Exists x (simplify p ))
        Not p->simplify1 (Not (simplify p))
        _->fm

--nnf2 bringt Formel in "no negation form", steht im Buch als nnf--
nnf2::Formula FOL->Formula FOL
nnf2 fm=
    case fm of
        And p q->And (nnf2 p) (nnf2 q)
        Or p q->Or (nnf2 p) (nnf2 q) 
        Imp p q ->Or (nnf2 (Not p))(nnf2 q)
        Iff p q ->Or (And (nnf2 p) (nnf2 q)) (And (nnf2 (Not p)) (nnf2 (Not q)))
        Not(Not p)->nnf2 p
        Not (And p q ) -> Or(nnf2 (Not p))(nnf2 (Not q))
        Not (Or p q) -> And (nnf2 (Not p)) (nnf2 (Not q))
        Not(Imp p q) -> And (nnf2 p) (nnf2 (Not q))
        Not(Iff p q)-> Or (And (nnf2 p)(nnf2(Not q))) (And (nnf2(Not p))(nnf2 q)) 
        Forall x p  -> Forall x (nnf2 p) 
        Exists x p  -> Exists x (nnf2 p)  
        Not (Forall x p ) -> Exists x (nnf2(Not p)) 
        Not (Exists x p) -> Forall x (nnf2(Not p))  
        _ -> fm



--pullquants "zieht" Quantifikatoren an den Anfang der Formel--
pullquants::Formula FOL->Formula FOL
pullquants fm=
    case fm of
        And (Forall x p) (Forall y q) -> pullq True True fm Forall And x y p q 
        Or (Exists x p) (Exists y q) -> pullq True True fm Exists Or x y p q 
        And (Forall x p) q -> pullq True False fm Forall And x x p q 
        And p (Forall y q) -> pullq False True fm Forall And y y p q 
        Or (Forall x p) q -> pullq True False fm Forall Or x x p q
        Or p (Forall y q) -> pullq False True fm Forall Or y y p q 
        And p (Exists y q ) -> pullq False True fm Exists And y y p q 
        And (Exists x p) q ->pullq True False fm Exists And x x p q
        Or (Exists x p) q  -> pullq True False fm Exists Or x x p q 
        Or p(Exists y q ) -> pullq False True fm Exists Or y y p q 
        _ -> fm
    where 
          pullq l r  fm quant op x y p q=
            let z = variant x (fv fm) 
            in let p' = if l then subst (\u ->if (u==x) then Var z else Var u) p else p 
                   q' = if r then subst (\v ->if (y==v) then Var z else Var v) q else q 
                in quant z (pullquants (op p' q') )

 
--prenex bringt eine Formel in Prenex Form wenn sie bereits in nnf ist--
prenex::Formula FOL->Formula FOL
prenex fm=
    case fm of 
        Forall x p  -> Forall x (prenex p) 
        Exists x p  -> Exists x (prenex p) 
        And p q  -> pullquants (And (prenex p) (prenex q)) 
        Or p q  -> pullquants (Or (prenex p) (prenex q)) 
        _ -> fm


--pnf bringt eine allgemeine Formel in Prenexnormalform--
pnf::Formula FOL->Formula FOL
pnf fm = prenex(nnf2(simplify fm))


--3.6 Skolemization--
--func/functions gibt die in einem/einer Term/Formel benutzten Funktionen (mit #Argumente) als Liste zurück-- 
funcs::Term->[(String, Int)]
funcs fm=
    case fm of
        Var x -> [] 
        Fn f args  -> union [(f,length args)](nub(concat( map funcs args)))

functions::Formula FOL->[(String, Int)]
functions fm = atom_union (\(R p a) -> nub(concat(map funcs a))) fm

--Skolemisierung einer Formel, die bereits in nnf ist, wobei das zweite Argument die Menge der schon benutzten Funktionen ist
skolem::Formula FOL->[String]->(Formula FOL,[String])
skolem fm fns=
    case fm of
        Exists y p ->   
            let xs = fv(fm) in 
            let f = variant (if (xs == []) then "c_"++y else "f_"++y) fns in
            let fx = Fn f (map (\x -> Var x) xs) 
            in skolem (subst (\z-> if z==y then fx else (Var z)) p) (f:fns) 
        Forall x p -> 
               let p' =fst (skolem p fns) 
                   fns'=snd(skolem p fns) 
               in ((Forall x p'),fns') 
        And p q  -> skolem2 (\(p,q) -> (And p q) ) (p,q) fns 
        Or p q  -> skolem2 (\(p,q) -> (Or p q))  (p,q) fns  
        _ -> (fm,fns)
    where 
          skolem2 cons (p,q) fns =
                let p' = fst(skolem p fns)
                    fns' = snd(skolem p fns) in 
                let q' = fst(skolem q fns')
                    fns'' = snd(skolem q fns') in
                (cons (p',q'),fns'')


--askolmize überführt vor dem Skolemizieren in NNF--
askolemize::Formula FOL->Formula FOL
askolemize fm=fst(skolem (nnf(simplify fm)) (map fst (functions fm)))

--specialize entfernt Allquantoren am Anfang--
specialize::Formula FOL->Formula FOL
specialize fm=
    case fm of
        Forall x p ->specialize p
        _->fm

--skolemize bringt eine Formel in Skolemform ohne Quantifikatoren--
skolemize::Formula FOL->Formula FOL
skolemize fm = specialize(pnf(askolemize fm))



testT1=Fn "h" [ Var "e", (Fn "h" [Var"x", Var "a'", Var "a"])] --Test für tsubst und funcs

testF0=Exists "d" (Atom(R "p" [Fn "k" [Var "x"]])) --kein test, nur für einfachere Notation

termSubTest "a"=testT1 --subfunktion für tsubst/subst
termSubTest "x"=Var "d"
termSubTest s= Var s

testF1=Exists "x" (Atom(R "p" [testT1])) --Test für subst 

testF2= Forall "x" (Exists "b" (Iff Bottom testF1)) --Test für simplify

testF3=Not (Exists "a" (Not testF1)) --bsp für nnf2

testF4=And testF1 testF0 --bsp für pullquants oder prenex sowie functions

testF5= Exists "a'" (Forall "e" testF1) --bsp für skolemization

  

  
  
  
  
  
  
  
  
  

