---- Chapter 2.8 
--Implementation of definitional CNF
module DefCnf where

import DNF
import qualified Data.Map as Map
import qualified Data.Set as Set
import NNF
import Parsing_FOL
import Printer_FOL
import Vortrag1

--instance Show (Formula Prop) where
--  show x = print_prop_formula x
--- "make proposition" mit Index n und erhöhe Index um 1
--
--Finite Partial Functions:
--Wir wollen Funktionen auf einer endlichen Domäne betrachten. Üblicherweise nutzt man dazu Assoziations Listen, wie [(a,b), (c,d)]. Ein Vorteil dieser Notation ist, dass die Funktion einfach erweitert werden kann, indem man ein weiteres Tupel hinzufügt.
-- Aufgrund der schlechten Laufzeiten für lange Listen nutzen wir "finite partial functions" (FPF). 
-- In OCaml ist der Typ der Finite Partial Functions von a nach b gegeben durch (a,b)func.
-- In Haskell kann der Typ "Map a b" aus dem Modul Data.Map diese Funktion übernehmen
-- a muss die Instanz Ord besitzen, damit dieser Typ gebildet werden kann.
-- In Ocaml, wird eine Funktion f um das Wertepaar (x,y) mittels "(x |-> y) f" erweitert. 
-- Dies erfolt in Haskell mit "insert x y f". (insert :: k -> a -> Map k a -> Map k a), wobei insert ein bereits vorhandendes Wertepaar (x,y') überschreibt.
-- 
-- lookup prüft ob ein Objekt in der Domäne liegt. Falls nicht, wird der Wert Nothing zurückgegeben. 
-- Map.lookup:: Ord k => k -> Map k a -> Maybe a
mkprop :: Int -> (Formula Prop, Int)
mkprop n = (Atom (P ("p_" ++ (show n))), n + 1)

type Triple
   = (Formula Prop, Map.Map (Formula Prop) (Formula Prop, Formula Prop), Int)

--Wir nehmen an, dass die Formel bereits in Negation Normalform ist.
--Argumente: Formel | Funktion, die eine Formel aufteilt | Variablen Counter
maincnf :: Triple -> Triple
maincnf (trip@(fm, defs, n)) =
  case fm of
    And p q -> defstep And (p, q) trip
    Or p q -> defstep Or (p, q) trip
    Iff p q -> defstep Iff (p, q) trip
    _ -> trip

--- defstep bekommt Constructor von "Formula a" als 1. Argument, keine Formel. 
defstep ::
     (Formula Prop -> Formula Prop -> Formula Prop)
  -> (Formula Prop, Formula Prop)
  -> Triple
  -> Triple
defstep op (p, q) (fm, defs, n) =
  let (fm1, defs1, n1) = maincnf (p, defs, n) --rekursion
      (fm2, defs2, n2) = maincnf (q, defs1, n1)
      fm' = op fm1 fm2
   in case Map.lookup fm' defs2 -- prüfe ob Formel bereits in den Def ist
            of
        Just (v, _) -> (v, defs2, n2)
        Nothing -> (v, Map.insert fm' (v, Iff v fm') defs2, n3)
          where (v, n3) = mkprop n2

-- falls defs2 (fm') = (v,fm), wobei fm irgendeine Formel ist, dann fügen wir nichts hinzu, sondern nutzen die bereits definierte Variable. Der Counter wird demnach auch nicht erhöht.
-- Andernfalls, füge neue atomare Proposition v hinzu, und erweitere defs2 um (fm' |->(v_n <=> fm')) 
--
-- Wir müssen sicherstellen, dass kein neu eingeführtes Atom bereits in der Ausgangsformel vorkommt.
--
--falls s == pfx_n', dann ist max_varindex pfx s n = max n n'
max_varindex :: String -> String -> Int -> Int
max_varindex pfx s n =
  let m = length pfx
      l = length s
   in if l <= m || take m s /= pfx -- beide mal folgt direkt s /= pfx_{Index}
        then n
        else let s' = take (l - m) (drop m s) -- String von m an, der Länge (l-m)
              in if all numeric s'
                   then max n (read s')
                   else n

--zuerst vereinfachen wir fm und ziehen die Negationen in die Atome. Dann bestimmen wir den Startpunkt des Variablencounters n und wenden fn (maincnf) an.
mk_defcnf :: (Triple -> Triple) -> Formula Prop -> [[Formula Prop]]
mk_defcnf fn fm =
  let fm' = nenf fm
      n = 1 + overatoms (max_varindex "p_" . pname) fm' 0
      (fm'', defs, _) = fn (fm', Map.empty, n) -- empty map
      deflist = map (snd . snd) (Map.toList defs) -- toList: FPF -> associationlist
   in map Set.toList $
      Set.toList $ Set.unions (simpcnf fm'' : map simpcnf deflist)

-- für defcnf1 ist fm'' eine Variable und simpcnf mehr oder weniger überflüssig, für defcnf aber kann fm'' komplexer sein. 
-- Die doppelte Anwendung von Set.toList resultiert aus der Definition von simpcnf. Die originale Implementierung aus dem Harrison Buch würde eine andere simpcnf Funktion voraussetzen.
--
defcnf1 :: (Formula Prop) -> (Formula Prop)
defcnf1 fm = list_conj $ map list_disj $ mk_defcnf maincnf fm

-- Formeln in dieser Normalform haben üblicherweise Redundanzen
-- Diese zu eliminieren ist bestenfalls in O(n²) möglich.
--
------------ Optimierter Algorithmus
subcnf ::
     (Triple -> Triple)
  -> (Formula Prop -> Formula Prop -> Formula Prop)
  -> (Formula Prop, Formula Prop)
  -> Triple
  -> Triple
subcnf sfn op (p, q) (fm, defs, n) =
  let (fm1, defs1, n1) = sfn (p, defs, n)
      (fm2, defs2, n2) = sfn (q, defs1, n1)
   in (op fm1 fm2, defs2, n2)

-- subcnf iteriert orcnf und andcnf auf den Teilformeln.
orcnf :: Triple -> Triple
orcnf (trip@(fm, defs, n)) =
  case fm of
    Or p q -> subcnf orcnf Or (p, q) trip
    _ -> maincnf trip

-- Das "Or" bleibt stehen, aber die Funktion wird auf den Teilformeln iteriert
andcnf :: Triple -> Triple
andcnf (trip@(fm, defs, n)) =
  case fm of
    And p q -> subcnf andcnf And (p, q) trip
    _ -> orcnf trip

defcnfs :: Formula Prop -> [[Formula Prop]]
defcnfs fm = mk_defcnf andcnf fm

defcnf :: Formula Prop -> Formula Prop
defcnf fm = list_conj (map list_disj (defcnfs fm))

andcnf3 :: Triple -> Triple
andcnf3 (trip@(fm, defs, n)) =
  case fm of
    And p q -> subcnf andcnf3 And (p, q) trip
    _ -> maincnf trip

defcnf3 :: Formula Prop -> Formula Prop
defcnf3 fm = list_conj (map list_disj (mk_defcnf andcnf3 fm))
