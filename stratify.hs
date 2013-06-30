{-# LANGUAGE GADTs
           , EmptyDataDecls
           , StandaloneDeriving
           , MultiParamTypeClasses
           , TemplateHaskell
           , ScopedTypeVariables
           , FlexibleInstances
           , FlexibleContexts
           , UndecidableInstances
           , NoMonomorphismRestriction
           , OverloadedStrings
           #-}
import Unbound.LocallyNameless
import Control.Monad.Error
import Data.String
import qualified Text.PrettyPrint as PP
import Text.PrettyPrint (Doc, (<+>), (<>))
import Control.Applicative

{-

The basic idea is that we would like to take an unstratified,
pure type system, and write down the stratified version.  So for
example, a PTS with only the (*,*) relation should result in
the type rules for the STLC.

As a warmup, we consider only systems on the lambda cube.

-}

data Sort = Star | Box
    deriving (Eq, Show, Ord)
data Axiom = Sort :~ Sort
    deriving (Eq, Show)
data Relation = Sort :. Sort
    deriving (Eq, Show, Ord)
data Rule = [Judgment] :=> Judgment
    deriving (Show)
data Judgment = [Statement] :|- Statement
    deriving (Show)
data Statement = Term :! Term | Context
    deriving (Show)

infixr :|-, :~, :., :=>, :!

-- technically a pseudoterm
-- we DON'T use binders because we care about how these so-called "binders" are named
-- this is all terribly unsound, subst for conveniently renaming stuff
data Term = Var (Name Term)
          | Sort Sort
          | App Term Term
          | Lambda (Name Term) Term Term
          | Pi (Name Term) Term Term
          | Subst (Name Term) Term Term -- fake
    deriving (Show)

$(derive [''Sort, ''Term])
instance Alpha Sort
instance Alpha Term
instance Subst Term Sort where
instance Subst Term Term where
    isvar (Var v) = Just (SubstName v)
    isvar _ = Nothing
instance IsString (Name Term) where fromString = string2Name
instance IsString Term where fromString = Var . fromString

type M = ErrorT String (LFreshM)
runM = either error id . runLFreshM . runErrorT

nv = fmap Var . lfresh

jAxiom = [] :=> [] :|- Sort Star :! Sort Box
jStart =
    [[Context] :|- "A" :! "s"] :=> [Context, "x" :! "A"] :|- "x" :! "A"
jWeak = undefined
jApp =
    [ [Context] :|- "M" :! (Pi "x" "A" "B")
    , [Context] :|- "N" :! "A"
    ] :=> [Context] :|- App "M" "N" :! Subst "x" "B" "N"

class Pretty p where
    ppr :: Int -> p -> Doc

pprint = putStrLn . ppshow
ppshow = PP.render . ppr 0

instance Pretty Sort where
    ppr _ Box = PP.text "☐"
    ppr _ Star = PP.text "★"

instance Pretty Term where
    ppr _ (Var n) = PP.text (show n)
    ppr _ (Sort c) = ppr 0 c
    ppr p (Lambda x t e) = prettyParen (p > 0) (pbind "λ" x t e)
    ppr p (Pi x t e) = (prettyParen (p > 0)) (pbind "Π" x t e)
    ppr p (App e1 e2) = prettyParen (p > 1) (ppr 1 e1 <+> ppr 2 e2)
    ppr p (Subst x e v) = PP.brackets (ppr 0 v <> PP.text "/" <> PP.text (show x)) <> (ppr 2 e)

instance Pretty Statement where
    ppr _ Context = PP.text "Γ"
    ppr _ (e :! t) = ppr 0 e <+> PP.colon <+> ppr 0 t

instance Pretty Rule where
    ppr _ (js :=> j) = PP.vcat (map (ppr 0) js ++ [PP.text "-----------------------", ppr 0 j])

instance Pretty Judgment where
    ppr _ (es :|- e) = PP.hsep (PP.punctuate (PP.text ",") (map (ppr 0) es)) <+> PP.text "⊢" <+> ppr 0 e

prettyParen True = PP.parens
prettyParen False = id
pbind b x t e = PP.hang (PP.text b <> PP.parens (PP.text (show x) <+> PP.colon <+> ppr 0 t) <> PP.text ".") 2 (ppr 0 e)

axioms = [Star :~ Box]

λarr = [Star :. Star]
λP = [Star :. Star, Star :. Box]
λω = [Star :. Star, Star :. Box, Box :. Box]
λC = [Star :. Star, Star :. Box, Box :. Box, Box :. Star]

{-

An extremely useful tool when understanding the judgments is to
rename the variables in a suggestive way; e.g. as per a stratification.
What invariant you would like is:

    e:τ:*
    τ:κ:☐

That is to say, while the kind of a τ may not be * (it could be a type
function * -> *), the sort of its kind is always ☐: taking the type
"one more time" removes any Πs.

~~~~

The algorithm begins by forming a directed acyclic graph out of the
axioms; in the case of the lambda cube, this graph is trivial, this is
true even for many generalized type systems. Cycles are not permitted,
as they result in the usual set-theoretic paradoxes.  (NB: * : * is not
the same as impredicativity!)  The idea is that this graph offers a
natural stratification of the calculus, but under some cases, we will
want to collapse levels together.  This hinges on the pi-rule:

    Γ ⊢ A:s₁   Γ, x:A ⊢ B:s₂
    ------------------------
      Γ ⊢ (Πx:A. B):s₂

Intuitively, λC is the system which we want to collapse the stratification
of; this is because we are given the rule derived from (☐, *):

    Γ ⊢ A:☐    Γ, x:A ⊢ B:*
    ------------------------
      Γ ⊢ (Πx:A. B):*

Rewriting this rule a bit (using the axiom), and providing the λ rule
along-side:

       Γ, x:* ⊢ B:*
    -------------------
      Γ ⊢ (Πx:*. B):*

       Γ, x:τ ⊢ M:B  Γ ⊢ (Πx:*. B):*
    -----------------------------------
      Γ ⊢ (λx:τ. M) : (Πx:*. B)


-}

{-

The algorithm is specified as follows: a pure type system is
specified as:

    - A set of sorts (e.g. *, ☐)
    - A set of axioms (e.g. * : ☐)
    - A set of relations

-}
