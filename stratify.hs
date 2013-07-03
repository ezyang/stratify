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
import Data.String
import qualified Data.Map as Map
import Data.Map (Map)
import Data.Graph.Inductive
import qualified Text.PrettyPrint as PP
import Text.PrettyPrint (Doc, (<+>), (<>))
import Control.Applicative
import Control.Monad.Writer (execWriter,tell)
import Control.Monad

{-

The basic idea is that we would like to take an unstratified,
pure type system, and write down the stratified version.  So for
example, a PTS with only the (*,*) relation should result in
the type rules for the STLC.

As a warmup, we consider only systems on the lambda cube.

-}

data Sort = Star | Box
    deriving (Eq, Show, Ord, Enum)
data Axiom = Sort :~ Sort
    deriving (Eq, Show)
afst (x :~ _) = x
asnd (_ :~ y) = y
data Relation = Sort :. Sort
    deriving (Eq, Show, Ord)
rel1 (s1 :. _) = s1
rel2 (_ :. s2) = s2
data Grammar = Grammar Term [Term]
    deriving (Show)
data Rule = Rule [Judgment] Judgment
    deriving (Show)
data Judgment = Judgment [Statement] Statement
    deriving (Show)
data Statement = Typed Term Term | Context
    deriving (Show)

sorts = [Star, Box]

(.|-) = Judgment
(.:) = Typed
(.=>) = Rule

infixr .|-, :~, :., .=>, .:

-- technically a pseudoterm
-- we DON'T use binders because we care about how these so-called "binders" are named
-- this is all terribly unsound, subst for conveniently renaming stuff
{- Results in:

stratify.hs:64:3:
    Warning: Duplicate constraint(s): Sat (ctx_axVY Term)
    In the context: (Sat (ctx_axVY (Name Term)),
                     Sat (ctx_axVY Sort),
                     Sat (ctx_axVY Term),
                     Sat (ctx_axVY X))
    While checking an instance declaration
    In the instance declaration for `Rep1 ctx_axVY Term'
-}
type X = Term -- EW EW EW
data Term = Var (Name Term)
          | Sort Sort
          | App Term Term
          | Lambda X Term Term
          | TyLambda X Term Term -- lol notation
          | Pi X Term Term
          | Arr Term Term
          | Subst X Term Term -- fake
    deriving (Show)

$(derive [''Sort, ''Term, ''Statement, ''Judgment, ''Rule])
instance Alpha Sort
instance Alpha Term
instance Alpha Statement
instance Alpha Judgment
instance Alpha Rule
instance Subst Term Sort where
instance Subst Term Term where
    isvar (Var v) = Just (SubstName v)
    isvar _ = Nothing
instance Subst Term Statement where
instance Subst Term Judgment where
instance Subst Term Rule where
instance IsString (Name Term) where fromString = string2Name
instance IsString Term where fromString = Var . fromString

nv = fmap Var . lfresh

jAxiom = [] .=> [] .|- Sort Star .: Sort Box
jStart =
    [[Context] .|- "A" .: "s"] .=> [Context, "x" .: "A"] .|- "x" .: "A"

jApp =
    [ [Context] .|- "M" .: Pi "x" "A" "B"
    , [Context] .|- "N" .: "A"
    ] .=> [Context] .|- App "M" "N" .: Subst "x" "B" "N"

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
    ppr p (TyLambda x t e) = prettyParen (p > 0) (pbind "Λ" x t e)
    ppr p (Pi x t e) = (prettyParen (p > 0)) (pbind "Π" x t e)
    ppr p (App e1 e2) = prettyParen (p > 1) (ppr 1 e1 <+> ppr 2 e2)
    ppr p (Subst x e v) = PP.brackets (ppr 0 v <> PP.text "/" <> PP.text (show x)) <> (ppr 2 e)
    ppr p (Arr e1 e2) = prettyParen (p > 0) (ppr 1 e1 <+> PP.text "→" <+> ppr 0 e2)

instance Pretty Statement where
    ppr _ Context = PP.text "Γ"
    ppr _ (Typed e t) = ppr 0 e <+> PP.colon <+> ppr 0 t

instance Pretty Rule where
    ppr _ (Rule js j) = PP.vcat (map (ppr 0) js ++ [PP.text "-----------------------", ppr 0 j])

instance Pretty Judgment where
    ppr _ (Judgment es e) = PP.hsep (PP.punctuate (PP.text ",") (map (ppr 0) es)) <+> PP.text "⊢" <+> ppr 0 e

prectuate _ _ []     = []
prectuate f p (x:xs) = (f <> x) : map (p <>) xs

instance Pretty Grammar where
    ppr _ (Grammar e es) = PP.hang (ppr 0 e) 2 ((PP.vcat (prectuate (PP.text "::= ") (PP.text "  | ") (map (ppr 0) es))))

prettyParen True = PP.parens
prettyParen False = id
pbind b x t e = PP.hang (PP.text b <> {- PP.parens -} (ppr 0 x <> PP.colon <> ppr 0 t) <> PP.text ".") 2 (ppr 0 e)

axioms = [Star :~ Box]
sortOf Star = Just Box
sortOf Box = Nothing

λarr = [Star :. Star]
λ2 = [Star :. Star, Box :. Star] -- polymorphic lambda calculus
λω = [Star :. Star, Box :. Star, Box :. Box]
λC = [Star :. Star, Box :. Star, Box :. Box, Star :. Box]

{-

WHAT DO YOU NEED TO DO?

  [X] We want to remove elements from the context, as they
      are guaranteed to be unused.

  [X] We want to replace Pi's with arrows when the variable is
      free (related to the previous thing, it is a case of which
      side of the turnstile you are on).

  [X] We want to rename metavariables according to the
      stratification.

  [X] We want to remove cases from grammar that cannot exist (since they
      have no relevant items), e.g. Pi at the term level.

  [X] We want to add cases to grammar when a binder's type
      is different (e.g. term lambda versus type lambda)

-}

{-

HOW DO YOU RENAME METAVARIABLES?

Barendregt states in his paper how to appropriate classify pseudoterms
as terms, types or kinds.  The basic idea is:

    e:τ:*
    τ:κ:☐

That is to say, while the kind of a τ may not be * (it could be a type
function * -> *), the sort of its kind is always ☐: taking the type
"one more time" removes any Πs.

-}

meta_name Nothing = "e"
meta_name (Just Star) = "τ"
meta_name (Just Box) = "κ"

var_name Nothing = "x"
var_name (Just Star) = "α"
var_name (Just Box) = "X"

-- nomenclature: we refer to 'x as under s' if 'x:?:s'; that is,
-- 's is the type of the type of x'
under Star = Nothing
under Box = (Just Star)

over = Just

lafresh x m = do
    n <- lfresh x
    avoid [AnyName n] (m n)

{-

HOW DO YOU REMOVE UNUSED ELEMENTS FROM THE CONTEXT?

The canonical example of wanting to remove unused elements
is the difference between λ→ and λP.  For SLTC, we would
like the Π rule to be written with arrows, since the binder
is always free; with dependence, however, we need full Π-types.

How can we tell when the binder is always free?  Looking at
the derivation trees, we are wondering:

        -----------
        Γ, Δ ⊢ A:s₁
      ---------------
      Γ, x:A, Δ ⊢ x:A  ??
      ---------------
            ....
    --------------------
      Γ, x:A:s₁ ⊢ B:s₂

i.e. could our proof tree ever end up using this particular proof term?
This is equivalent to asking whether or not A will ever become a goal in
the derivation.

So, how can we conclude that a rule will never show up?  We generate
a directed graph and consider connectivity.  For each rule (s₁, s₂)
we add an edge x → y to the graph, read 'When proving a goal of sort x,
one may need to prove a goal of sort y (where proof term : goal : sort)',
filling in the trivial reflexive relations.

    start:      s → s
    universal:  s → typeof s
    app-rule:   s₂ → s₁
    Π-rule:     typeof s₂ → typeof s₁
    λ-rule:     s₂ → typeof s₁, typeof s₂

In fact, we can simplify this: as universal paths exist taking
s to typeof s, the only modified paths are s₂ → s₁ and typeof s₂ → typeof s₁
when there does not already exist a universal path. (In the lambda
cube, the typeof s₂ → typeof s₁ paths are trivial, but they are not
necessarily... however, it does require such shenanigans as a Π term
being allowed to have two different types.)

To conclude that the Π-rule for some pair (s₁, s₂) will never use it's
variable, we must show that there is no path from 'typeof s₂ → s₁'.

Example 1: For λ→, we have the freely generated graph:

    * → *, ☐
    ☐ → ☐

For (*, *), there is no path ☐ → *, thus the binding may be dropped.

Example 2: For λ2, the graph is the same, as no backwards edges are
added. (*, *) is unchanged, but the new relation (*, ☐) trivially has
a path (thus requiring the polymorphic ∀ operator.)

Example 3: For λC, the rule (*, ☐) completes the graph.

    * → *, ☐
    ☐ → *, ☐

(*, *)  now does have its path ☐ → *, and the binding is necessary.
However, (☐, ☐) does NOT have a path, as typeof ☐ is not defined
on the lambda cube.  Put another way, there is no kind polymorphism
on the lambda cube, even in λC!

E E F G D C A G Eb D C

-}

sortGraph :: [Relation] -> UGr
sortGraph rels = mkGraph (map (\x -> (fromEnum x, ())) sorts)
                         (map (\(s1 :. s2) -> (fromEnum s2, fromEnum s1, ())) rels
                            ++ concatMap (\s -> maybe [] (\s' -> [(fromEnum s, fromEnum s', ())]) (sortOf s)) sorts)

needPiBinder rels s1 s2 =
    maybe False (\s3 -> s1 == s3 || fromEnum s1 `elem` dfs [fromEnum s3] (sortGraph rels)) (sortOf s2)

jPi ta tb b s1 s2 x p =
    [ [Context] .|- ta .: s1
    , ([Context] ++ if p then [x .: ta] else []) .|- tb .: s2
    ] .=> [Context] .|- (if p then Pi x ta tb else Arr ta tb) .: s2
jLambda ta tb b s1 s2 x p =
    [ [Context] .|- ta .: s1
    , [Context, x .: ta] .|- b .: tb
    , ([Context] ++ if p then [x .: ta] else []) .|- tb .: s2
    ] .=> [Context] .|- Lambda x ta tb .: (if p then Pi x ta tb else Arr ta tb)

make (s1 :. s2) rels rule = runLFreshM $
    lafresh (meta_name (over s1)) $ \ta -> -- le freak!
    lafresh (meta_name (over s2)) $ \tb ->
    lafresh (meta_name (under s2)) $ \b ->
    lafresh (var_name (under s1)) $ \x ->
    return $ rule (Var ta) (Var tb) (Var b) (Sort s1) (Sort s2) (Var x) (needPiBinder rels s1 s2)

{-

HOW DO YOU GENERATE THE GRAMMAR?

For the λ-cube, it is adequate to generate a grammar for each sort, as
well as a grammar for terms (which are under types).  The idea is
that if a production could not possibly well-typed under the rules,
then it is omitted from the grammar.

Π/λ productions are allowed exactly per the relations, except that λ
terms are "one under" their relation, i.e. a lambda term is permissible
in sort s if we have the relation (_, typeof s).  If the hierarchy has a
top, no lambda terms are permitted (what would their type be?)  The
application production is symmetric to the λ production.

There is some delicacy dealing with variable binding.  We can reuse
our logic for when Π is bindable, but we must also allow for lambda
binding; that is to say, if it is possible for some lambda to bind
a properly sorted variable, then we must include the variable production.

-}

grammar s rels = Grammar (meta_name s) . execWriter $ do
    let calc_rels p = filter (\r -> p (rel2 r) == s) rels
        lambda_rels = calc_rels under
        pi_rels     = calc_rels over
    when (not (null (lambda_rels ++ filter (\(s1 :. s2) -> needPiBinder rels s1 s2) pi_rels))) $ tell [Var (var_name s)]
    tell . map (Sort . afst) . filter (\a -> Just (asnd a) == s) $ axioms
    tell . concatMap (\(s1 :. s2) ->
            [ (if s1 == Box then TyLambda else Lambda) -- hack!
              (var_name (under s1))
              (meta_name (over s1))
              (meta_name (under s2))
            , App (meta_name (under s2)) (meta_name (under s1))
            ])
         $ lambda_rels
    tell . map (\(s1 :. s2) ->
            if needPiBinder rels s1 s2
                then Pi (var_name (under s1))
                     (meta_name (over s1))
                     (meta_name (over s2))
                else Arr (meta_name (over s1)) (meta_name (over s2)))
         $ pi_rels

{-

Things to worry about for generalized type systems:

    [ ] Ternary relation makes for more interesting pi-types

    [ ] Infinite universes using index variables

    [ ] Sometimes, it's not profitable to split up terms
        due to prenex-style restrictions, etc.

-}
