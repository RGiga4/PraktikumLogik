-- Parsing of formulas
-- After Harrison "Handbook ..." --
module Parsing_FOL where

import Data.String

-- Chapter 1.7 Lexing --
space x = x `elem` " \t\n\r"

punctuation x = x `elem` "()[]{},"

symbolic x = x `elem` "~‘!@#$%^&*-+=|\\:;<>.?/"

numeric x = x `elem` "0123456789"

alphanumeric x =
  x `elem` "abcdefghijklmnopqrstuvwxyz_’ABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789"

lexwhile prop (c:cs)
  | prop c = (c : tok, rest)
  where
    (tok, rest) = lexwhile prop cs
lexwhile prop x = ("", x)

lexer inp
  | (snd (lexwhile space inp) == "") = []
  | otherwise =
    let c = head (snd (lexwhile space inp))
        cs = tail (snd (lexwhile space inp))
        prop
          | alphanumeric c = alphanumeric
          | symbolic c = symbolic
          | otherwise = \x -> False
        (toktl, rest) = lexwhile prop cs
     in (c : toktl) : (lexer rest)

-- Chapter 1.7 Parsing --
make_parser pfn s =
  let (expr, rest) = pfn (lexer s)
   in if rest == []
        then expr
        else error "Unparsed input"

-- Appendix 3 General parsing functions --
parse_ginfix opsym opupdate sof subparser inp
  | (inp1 /= [] && head inp1 == opsym) =
    parse_ginfix opsym opupdate (opupdate sof e1) subparser (tail inp1)
  | otherwise = (sof e1, inp1)
  where
    (e1, inp1) = subparser inp

parse_left_infix opsym opcon =
  parse_ginfix opsym (\f e1 e2 -> (opcon (f e1) e2)) (\x -> x)

parse_right_infix opsym opcon =
  parse_ginfix opsym (\f e1 e2 -> f (opcon e1 e2)) (\x -> x)

parse_list opsym = parse_ginfix opsym (\f e1 e2 -> (f e1) ++ [e2]) (\x -> [x])

papply f (ast, rest) = (f ast, rest)

nextin inp tok = (inp /= []) && (head inp == tok)

parse_bracketed subparser cbra inp
  | nextin rest cbra = (ast, tail rest)
  | otherwise = error "Closing bracket expected"
  where
    (ast, rest) = subparser inp

-- Appendix 3 Parsing first-order terms --
is_const_name s = (all numeric s) || (s == [])

data Term
  = Var String
  | Fn String
       [Term]
  deriving (Eq, Ord)

parse_atomic_term [] = error "term expected"
parse_atomic_term ("(":rest) = parse_bracketed parse_term ")" rest
parse_atomic_term ("-":rest) =
  papply (\t -> Fn "-" [t]) (parse_atomic_term rest)
parse_atomic_term (f:"(":")":rest) = (Fn f [], rest)
parse_atomic_term (f:"(":rest) =
  papply
    (\args -> Fn f args)
    (parse_bracketed (parse_list "," parse_term) ")" rest)
parse_atomic_term (a:rest)
  | is_const_name a = (Fn a [], rest)
  | otherwise = (Var a, rest)

parse_term inp =
  parse_right_infix
    "++"
    (\e1 e2 -> (Fn "++" [e1, e2]))
    (parse_right_infix
       "+"
       (\e1 e2 -> (Fn "+" [e1, e2]))
       (parse_left_infix
          "-"
          (\e1 e2 -> (Fn "-" [e1, e2]))
          (parse_right_infix
             "*"
             (\e1 e2 -> (Fn "*" [e1, e2]))
             (parse_left_infix
                "/"
                (\e1 e2 -> (Fn "/" [e1, e2]))
                (parse_left_infix
                   "^"
                   (\e1 e2 -> (Fn "^" [e1, e2]))
                   (parse_atomic_term))))))
    inp

parset = make_parser parse_term

-- Appendix 3 Parsing first-order formulas
data FOL =
  R String
    [Term]
  deriving (Eq, Ord)

data Formula a
  = Bottom
  | Top
  | Atom a
  | Not (Formula a)
  | And (Formula a)
        (Formula a)
  | Or (Formula a)
       (Formula a)
  | Imp (Formula a)
        (Formula a)
  | Iff (Formula a)
        (Formula a)
  | Forall String
           (Formula a)
  | Exists String
           (Formula a)
  deriving (Eq, Ord)

parse_atom inp =
  let (tm, rest) = parse_term inp
   in if rest /= [] && head rest `elem` ["=", "<", "<=", ">", ">="]
        then papply
               (\tm' -> Atom (R (head rest) [tm, tm']))
               (parse_term $ tail rest)
        else case inp of
               (p:"(":")":rest') -> (Atom (R p []), rest')
               (p:"(":rest') ->
                 papply
                   (\args -> Atom (R p args))
                   (parse_bracketed (parse_list "," parse_term) ")" rest')
               (p:rest') ->
                 if p /= "("
                   then (Atom (R p []), rest')
                   else error "parse_atom"

parse_atomic_formula afn inp =
  case inp of
    [] -> error "formula expected"
    "false":rest -> (Bottom, rest)
    "true":rest -> (Top, rest)
    "(":rest -> parse_bracketed (parse_formula afn) ")" rest
    "~":rest -> papply (\p -> Not p) (parse_atomic_formula afn rest)
    "forall":x:rest -> parse_quant afn (\x p -> (Forall x p)) x rest
    "exists":x:rest -> parse_quant afn (\x p -> (Exists x p)) x rest
    _ -> afn inp

parse_quant afn qcon x inp =
  case inp of
    [] -> error "Body of quantified term expected"
    y:rest ->
      papply
        (\fm -> (qcon x fm))
        (if y == "."
           then parse_formula afn rest
           else parse_quant afn qcon y rest)

parse_formula afn inp =
  parse_right_infix
    "<=>"
    (\p q -> (Iff p q))
    (parse_right_infix
       "==>"
       (\p q -> (Imp p q))
       (parse_right_infix
          "\\/"
          (\p q -> (Or p q))
          (parse_right_infix
             "/\\"
             (\p q -> (And p q))
             (parse_atomic_formula afn))))
    inp

parse = make_parser (parse_formula parse_atom)

--
-- Parser for Propositions
-- This parser has been moved from Vortrag1.hs 
data Prop =
  P String
  deriving (Eq, Ord)

parse_propvar :: [String] -> (Formula Prop, [String])
parse_propvar (p:oinp)
  | p /= "(" = (Atom (P p), oinp)
parse_propvar _ = error "parse_propvar"

parse_prop_formula :: String -> Formula Prop
parse_prop_formula = make_parser (parse_formula parse_propvar)
