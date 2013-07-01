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
    deriving (Eq, Show, Ord)
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

The key is to focus on the variable introduction rules:
if it is not possible to introduce a variable under some sort
for another context, then they can be erased.

Algorithmically, whenever constructing a pi rule (and the pi-terms of
the lambda rule) for (s₁, s₂), we check if (s₁, typeof s₂) is fulfilled.
As an example, consider the generation of (*,*) rule.  The binder
requires (*,☐) to be present in order to be applicable.

E E F G D C A G Eb D C

This should make it clear that λC has some problems: it doesn't
have an infinite number of universes!

-}

arrOnly rels s1 s2 = maybe False (\s2' -> (s1 :. s2') `elem` rels) (sortOf s2)

jPi p =
    [ [Context] .|- "A" .: "s₁"
    , ([Context] ++ if p then ["x" .: "A"] else []) .|- "B" .: "s₂"
    ] .=> [Context] .|- (if p then Pi "x" "A" "B" else Arr "A" "B") .: "s₂"
jLambda p =
    [ [Context] .|- "A" .: "s₁"
    , [Context, "x" .: "A"] .|- "b" .: "B"
    , ([Context] ++ if p then ["x" .: "A"] else []) .|- "B" .: "s₂"
    ] .=> [Context] .|- Lambda "x" "A" "b" .: (if p then Pi "x" "A" "B" else Arr "A" "B")

make (s1 :. s2) rels rule = runLFreshM $
    lafresh (meta_name (over s1)) $ \ta -> -- le freak!
    lafresh (meta_name (over s2)) $ \tb ->
    lafresh (meta_name (under s2)) $ \b ->
    lafresh (var_name (under s1)) $ \x ->
    return $ substs
        [ ("A", Var ta)
        , ("B", Var tb)
        , ("b", Var b)
        , ("s₁", Sort s1)
        , ("s₂", Sort s2)
        , ("x", Var x)
        ] (rule (arrOnly rels s1 s2))

{-

HOW DO YOU GENERATE THE GRAMMAR?

For the λ-cube, it is adequate to generate a grammar for each sort, as
well as a grammar for terms (which are under types).

Pi/Lambda productions may be eliminated if they are not allowed
by the relations.  A pi-term is permissible in sort s if (_, s)
is present in the relations. A lambda-term is permissible in sort
s if (_, typeof s) is present in the relations (in particular, if
the sort is at the top of a hierarchy, no lambda terms are allowed,
since we cannot type their pi terms!)

Similarly as before, some pi productions are replaced with arrow
productions as determined by the previous section.

Additionally, some productions need to be duplicated as they are
instantiated by multiple relations:

    * Lambda, considering what the binder is under, and symmetrically,
      App.
    * Pi, considering what the binder is under (this is only
      really relevant λC, since so many pis trivialize)

-}

grammar s rels = Grammar (meta_name s) . execWriter $ do
    let calc_rels p = filter (\r -> p (rel2 r) == s) rels
        lambda_rels = calc_rels under
        pi_rels     = calc_rels over
    when (not (null lambda_rels)) $ tell [Var (var_name s)]
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
            if arrOnly rels s1 s2
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
