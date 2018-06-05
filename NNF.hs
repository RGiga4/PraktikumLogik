module NNF where

import Parsing_FOL

-- Cancels out Top's and Bottom's recursivly
psimplify fm =
  case fm of
    Not p -> psimplify1 $ Not $ psimplify p
    And p q -> psimplify1 $ And (psimplify p) (psimplify q)
    Or p q -> psimplify1 $ Or (psimplify p) (psimplify q)
    Imp p q -> psimplify1 $ Imp (psimplify p) (psimplify q)
    Iff p q -> psimplify1 $ Iff (psimplify p) (psimplify q)
    _ -> fm

-- Cancels out Top and Bottom
psimplify1 fm =
  case fm of
    Not Bottom -> Top
    Not Top -> Bottom
    Not (Not p) -> p
    And p Bottom -> Bottom
    And Bottom p -> Bottom
    And p Top -> p
    And Top p -> p
    Or p Bottom -> p
    Or Bottom p -> p
    Or p Top -> Top
    Or Top p -> Top
    Imp Bottom p -> Top
    Imp p Top -> Top
    Imp Top p -> p
    Imp p Bottom -> Not p
    Iff p Top -> p
    Iff Top p -> p
    Iff p Bottom -> Not p
    Iff Bottom p -> Not p
    _ -> fm

-- Returns whether a literal is positive or negative
negative lit =
  case lit of
    Not p -> True
    _ -> False

positive = not . negative

-- Converts negative literal into positive and vice versa
opposite lit =
  case lit of
    Not p -> p
    p -> Not p

-- Converts formula to NNF (negation normal form)
nnf1 fm =
  case fm of
    And p q -> And (nnf1 p) (nnf1 q)
    Or p q -> Or (nnf1 p) (nnf1 q)
    Imp p q -> Or (nnf1 $ Not p) (nnf1 q)
    Iff p q -> Or (And (nnf1 p) (nnf1 q)) (And (nnf1 $ Not p) (nnf1 $ Not q))
    Not (Not p) -> nnf1 p
    Not (And p q) -> Or (nnf1 $ Not p) (nnf1 $ Not q)
    Not (Or p q) -> And (nnf1 $ Not p) (nnf1 $ Not q)
    Not (Imp p q) -> And (nnf p) (nnf1 $ Not q)
    Not (Iff p q) ->
      Or (And (nnf1 p) (nnf1 $ Not q)) (And (nnf1 $ Not p) (nnf1 q))
    _ -> fm

-- Converts formula to NNF and simplifies it (stays in NNF)
nnf = psimplify . nnf1

-- Converts formula to NENF (like NNF but keeps equivalance)
nenf1 fm =
  case fm of
    And p q -> And (nenf1 p) (nenf1 q)
    Or p q -> Or (nenf1 p) (nenf1 q)
    Imp p q -> Or (nenf1 $ Not p) (nenf1 q)
    Iff p q -> Iff (nenf1 p) (nenf1 q)
    Not (Not p) -> nenf1 p
    Not (And p q) -> Or (nenf1 $ Not p) (nenf1 $ Not q)
    Not (Or p q) -> And (nenf1 $ Not p) (nenf1 $ Not q)
    Not (Imp p q) -> And (nenf1 p) (nenf1 $ Not q)
    Not (Iff p q) -> Iff (nenf1 p) (nenf1 $ Not q)
    _ -> fm

-- Converts fromula to NENF and simplifies it (stays in NENF)
nenf = psimplify . nenf1
