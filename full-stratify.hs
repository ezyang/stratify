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
           , Rank2Types
           #-}
import Unbound.LocallyNameless -- used only for LFresh
import Data.String
import qualified Data.Map as Map
import Data.Map (Map)
import Data.Graph.Inductive
import qualified Text.PrettyPrint as PP
import Text.PrettyPrint (Doc, (<+>), (<>))
import Control.Applicative
import Control.Monad.Writer (execWriter,tell)
import Control.Monad
import Data.Maybe

type Sort = String
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
-- so it's pretty unsound!
data Term = Var (Name Term)
          | Sort Sort
          | App Term Term
          | Lambda (Name Term) Term Term
          | TyLambda (Name Term) Term Term -- lol notation
          | Pi (Name Term) Term Term
          | Arr Term Term
          | Subst (Name Term) Term Term -- fake
    deriving (Show)

$(derive [''Term])

instance IsString (Name Term) where fromString = string2Name
instance IsString Term where fromString = Var . fromString

class Pretty p where
    ppr :: Int -> p -> Doc

pprint = putStrLn . ppshow
ppshow = PP.render . ppr 0

instance Pretty (Name a) where
    ppr _ n = PP.text (show n)

instance Pretty Term where
    ppr _ (Var n) = PP.text (show n)
    ppr _ (Sort c) = PP.text c
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

data GTS = GTS {
        sorts :: [Sort]
      , axioms :: [Axiom]
      , rels :: [Relation]
      -- just for the pretty printer!
      , meta_name :: IsString s => Maybe Sort -> s
      , var_name :: IsString s => Maybe Sort -> s
      , tr :: Sort -> Int -- generated
    }

gts λ = λ { tr = fromMaybe (error "tr") . flip Map.lookup (Map.fromList (zip (sorts λ) [0..])) }

λcube = gts $ GTS {
        sorts = ["*", "☐"]
      , axioms = ["*" :~ "☐"]
      , rels = []
      , meta_name = meta_name
      , var_name = var_name
      , tr = undefined
    }
    where meta_name Nothing = "e"
          meta_name (Just "*") = "τ"
          meta_name (Just "☐") = "κ"
          var_name Nothing = "x"
          var_name (Just "*") = "α"
          var_name (Just "☐") = "X"

-- forbids unicity-breaking
sortOf λ s = go (axioms λ)
    where go [] = Nothing
          go (s1 :~ s2 : xs) | s1 == s = Just s2
                             | otherwise = go xs

-- this actually might not work under some axiom schemes, hm!
under λ s = go (axioms λ)
    where go [] = Nothing
          go (s1 :~ s2 : xs) | s2 == s = Just s1
                             | otherwise = go xs

-- glorified identity
over _ = Just

λarr = λcube { rels = ["*" :. "*"] }
λ2   = λcube { rels = ["*" :. "*", "☐" :. "*"] }
λω   = λcube { rels = ["*" :. "*", "☐" :. "*", "☐" :. "☐"] }
λC   = λcube { rels = ["*" :. "*", "☐" :. "*", "☐" :. "☐", "*" :. "☐"] }

-- ugh!

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
the derivation trees, we are looking for these situations:

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

So, how can we conclude that a rule will never show up?  One strategy is
to generate a directed graph and pose the question as a connectivity
issue.  That is, the edges x → y to the graph indicate 'When proving a
goal of sort x, one may need to prove a goal of sort y (where proof term
: goal : sort)'.

These edges can be read off fairly directly from the rules. Here are
a few (omitting the reflexive relations):

    start:      s → s
    universal:  s → typeof s
    app-rule:   s₂ → s₁
    Π-rule:     typeof s₂ → typeof s₁
    λ-rule:     s₂ → typeof s₁, typeof s₂

In fact, we can simplify these rules: with the universal paths exist
taking s to typeof s, the only modified paths are s₂ → s₁ and typeof s₂
→ typeof s₁ when there does not already exist a universal path. (In the
lambda cube, the typeof s₂ → typeof s₁ paths are trivial, but they are
not necessarily... however, any system which permits this gives up
*unicity of types*, which is a stiff pill to swallow.)

Finally, to conclude that the Π-rule for some pair (s₁, s₂) will never use it's
variable, we must show that there is no path from 'typeof s₂ → s₁'.

Example 1: For λ→, we have the generated graph:

    * → *, ☐
    ☐ → ☐

Notice there are no non-trivial relations.  For (*, *), there is no path
☐ → *, thus the binding may be dropped.

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

sortGraph :: GTS -> UGr
sortGraph λ = mkGraph (map (\x -> (tr λ x, ())) (sorts λ))
                      (map (\(s1 :. s2) -> (tr λ s2, tr λ s1, ())) (rels λ)
                         ++ concatMap (\s -> maybe [] (\s' -> [(tr λ s, tr λ s', ())]) (sortOf λ s)) (sorts λ))

needPiBinder λ s1 s2 =
    maybe False (\s3 -> s1 == s3 || tr λ s1 `elem` dfs [tr λ s3] (sortGraph λ)) (sortOf λ s2)

jPi ta tb b s1 s2 x p =
    [ [Context] .|- ta .: s1
    , ([Context] ++ if p then [Var x .: ta] else []) .|- tb .: s2
    ] .=> [Context] .|- (if p then Pi x ta tb else Arr ta tb) .: s2
jLambda ta tb b s1 s2 x p =
    [ [Context] .|- ta .: s1
    , [Context, Var x .: ta] .|- b .: tb
    , ([Context] ++ if p then [Var x .: ta] else []) .|- tb .: s2
    ] .=> [Context] .|- Lambda x ta b .: (if p then Pi x ta tb else Arr ta tb)

make (s1 :. s2) λ rule = runLFreshM $
    lafresh (meta_name λ (over λ s1)) $ \ta -> -- le freak!
    lafresh (meta_name λ (over λ s2)) $ \tb ->
    lafresh (meta_name λ (under λ s2)) $ \b ->
    lafresh (var_name λ (under λ s1)) $ \x ->
    return $ rule (Var ta) (Var tb) (Var b) (Sort s1) (Sort s2) x (needPiBinder λ s1 s2)

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

production s λ = Grammar (meta_name λ s) . execWriter $ do
    let calc_rels p = filter (\r -> p (rel2 r) == s) (rels λ)
        lambda_rels = calc_rels (under λ)
        pi_rels     = calc_rels (over λ)
    when (not (null (lambda_rels ++ filter (\(s1 :. s2) -> needPiBinder λ s1 s2) pi_rels))) $ tell [Var (var_name λ s)]
    tell . map (Sort . afst) . filter (\a -> Just (asnd a) == s) $ axioms λ
    tell . concatMap (\(s1 :. s2) ->
            [ Lambda
              (var_name λ (under λ s1))
              (meta_name λ (over λ s1))
              (meta_name λ (under λ s2))
            , App (meta_name λ (under λ s2)) (meta_name λ (under λ s1))
            ])
         $ lambda_rels
    tell . map (\(s1 :. s2) ->
            if needPiBinder λ s1 s2
                then Pi (var_name λ (under λ s1))
                     (meta_name λ (over λ s1))
                     (meta_name λ (over λ s2))
                else Arr (meta_name λ (over λ s1)) (meta_name λ (over λ s2)))
         $ pi_rels

-- putting it all together

a $$ b = a PP.$$ PP.text "" PP.$$ b

grammar λ =
    ppr 0 (production Nothing λ) $$
    ppr 0 (production (Just "*") λ) $$
    ppr 0 (production (Just "☐") λ)

{-

Things to worry about for generalized type systems:

    [ ] Ternary relation makes for more interesting pi-types

    [ ] Infinite universes using index variables

    [ ] Sometimes, it's not profitable to split up terms
        due to prenex-style restrictions, etc.

-}
