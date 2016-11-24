{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE NamedFieldPuns #-}
module Tct.Trs.Processor.Poly.GUBS
  -- ( gubs
  -- , gubsDeclaration
  -- , Selector (..)
  -- , selectorArg )
where


--- * imports --------------------------------------------------------------------------------------------------------

import qualified Data.List                           as L (partition)
import qualified Data.Map.Strict                     as M
import           Data.Maybe                          (fromMaybe)
import           Data.Monoid                         ((<>))
import qualified Data.Set                            as S
import           Data.Tree                           (Tree (..), drawTree)

import           Control.Monad.State.Strict

import qualified Data.Rewriting.Rule                 as R

import           GUBS                                as G (Constraint (..), (<=>), (==>))
import qualified GUBS                                as G

import qualified Tct.Core.Common.Pretty              as PP
import qualified Tct.Core.Common.Xml                 as Xml
import qualified Tct.Core.Data                       as T

import qualified Tct.Common.Polynomial               as P
import qualified Tct.Common.PolynomialInterpretation as PI
import           Tct.Common.ProofCombinators         (ApplicationProof (..), OrientationProof (..))
import           Tct.Common.Ring                     (SemiRing, add, sub, zero)

import           Tct.Trs
import qualified Tct.Trs.Data.Problem                as Prob
import qualified Tct.Trs.Data.ProblemKind            as Prob
import qualified Tct.Trs.Data.Rules                  as RS (member, toList, funs)
import qualified Tct.Trs.Data.Signature              as Sig
import           Tct.Trs.Data.Symbol                 (fun, var)
import qualified Tct.Trs.Encoding.Interpretation     as I
import           Tct.Trs.Encoding.UsablePositions    (usableArgsWhereApplicable, usablePositionsOf)
import           Tct.Trs.Processors                  (Degree)


--- * NaturalPI ------------------------------------------------------------------------------------------------------

data Selector = All | Any | One
  deriving (Bounded, Enum, Eq, Show)

selectorArg :: T.Argument 'T.Required Selector
selectorArg = T.flag "selector" [ "This argument specifies which rules to orient Strictly  "]

type Kind = PI.Kind F

data PolyOrder c = PolyOrder
  { kind_ :: Kind
  , pint_ :: I.InterpretationProof (P.Polynomial c PI.SomeIndeterminate) (P.Polynomial c V)
  } deriving Show

type NaturalPIProof = OrientationProof (PolyOrder Int)

certification :: PolyOrder Int -> T.Optional T.Id T.Certificate -> T.Certificate
certification order cert = case cert of
  T.Null         -> T.timeUBCert bound
  T.Opt (T.Id c) -> T.updateTimeUBCert c (`add` bound)
  where bound = PI.bound (kind_ order) (PI.PolyInter . I.interpretations . I.inter_ $ pint_ order)

-- certification :: PolyOrder Int -> T.Id T.Certificate -> T.Certificate
-- certification order (T.Id c) = T.updateTimeUBCert c (`add` bound)
--   where bound = PI.bound (kind_ order) (PI.PolyInter . I.interpretations . I.inter_ $ pint_ order)

restricted :: Problem f v -> Sig.Symbols f
restricted prob = case Prob.startTerms prob of {Prob.BasicTerms{Prob.constructors=cs} -> cs; _ -> S.empty}


--- * encode ---------------------------------------------------------------------------------------------------------
-- construct a ConstraintSystem from a Trs problem

canonicalVar' :: Int -> V
canonicalVar' = var . ("_x" <>) . show

canonicalVar :: Int -> G.Term f V
canonicalVar = G.Var . canonicalVar'

canonicalFun' :: Int -> F
canonicalFun' = fun . ("_f" <>) . show

-- canonicalFun :: Int -> G.Term F V
-- canonicalFun i j = G.Fun (canonicalFun' i) []

fresh :: State ([G.Term F V],[F]) (G.Term F V)
fresh = do
  (cs,f:fs) <- get
  let c = G.Fun f []
  put (c:cs,fs)
  return c

withFreshFuns :: S.Set F -> State ([G.Term F v], [F]) a -> (a, [G.Term F v])
withFreshFuns funs m = fst <$> runState m ([], funs')
  where funs' = filter (`S.notMember` funs) $ canonicalFun' `fmap` [1..]


canonicalTerm :: (f,Int) -> G.Term f V
canonicalTerm (f,ar)= G.Fun f $ canonicalVar `fmap` [1..ar]

encodeTerm :: R.Term f v -> G.Term f v
encodeTerm (R.Fun f ts) = G.Fun f (encodeTerm `fmap` ts)
encodeTerm (R.Var v)    = G.Var v

-- | Constraint encoding for Polynomial Interpretations, where
-- montonicity: f(x1,...,xn)  >= sum (upos(f))
-- restricted:  x1,...,xn + k >= f(x1,...,xn)
--
-- Any:
-- l_i >= r_i + k_i
-- sum(k_i) >= 0
encode :: Selector -> Problem F V -> G.ConstraintSystem F V
encode selector prob =
  orientStrs strs
  <> orientWeakly `fmap` wtrs
  <> monotone `fmap` fs
  <> stronglyLinear cs

  where

  strs = RS.toList $ Prob.strictComponents prob
  wtrs = RS.toList $ Prob.weakComponents prob
  upos = usablePositionsOf $ usableArgsWhereApplicable prob (Prob.isDTProblem prob) True
  sig  = Prob.signature prob
  fs   = Sig.elems sig
  cs   = Sig.elems $ Sig.restrictSignature sig (restricted prob)
  funs = RS.funs (Prob.allComponents prob)

  orientStrs rs = case selector of
    All   -> orientStrictly `fmap` rs
    Any   -> (sum fs :>=: 1) :cs
       where (cs,fs) = withFreshFuns funs (forM rs orientStrictlyM)
    One -> if null rs then [] else orientStrictly (head rs) : fmap orientWeakly (tail rs)

  orientStrictlyM R.Rule{R.lhs=l,R.rhs=r} = fresh >>= \v -> return $ encodeTerm l :>=: encodeTerm r + v
  orientStrictly  R.Rule{R.lhs=l,R.rhs=r} = encodeTerm l :>=: encodeTerm r + 1
  orientWeakly    R.Rule{R.lhs=l,R.rhs=r} = encodeTerm l :>=: encodeTerm r

  monotone (f,i)        = canonicalTerm (f,i) :>=: sum (canonicalVar `fmap` upos f)
  stronglyLinear cs     = fst $ withFreshFuns funs (forM cs stronglyLinearM)
  stronglyLinearM (f,i) = fresh >>= \v -> return $ sum (canonicalVar `fmap` [1..i]) + v :>=: canonicalTerm (f,i)


--- * decode ---------------------------------------------------------------------------------------------------------
-- translate the result back to Tct

fromGPolynomial :: G.Polynomial G.Var Integer -> P.Polynomial Int PI.SomeIndeterminate
fromGPolynomial p = P.fromView  [ (fromIntegral c, k `fmap` ps) | (c,m) <- G.toMonos p, let ps = G.toPowers m ]
  where k (G.V v,i) = (toEnum v, i)

fromGInterpretation :: G.Interpretation f Integer -> I.Interpretation f (P.Polynomial Int PI.SomeIndeterminate)
fromGInterpretation (G.Inter m) = I.Interpretation $ M.map fromGPolynomial $ M.mapKeysMonotonic fst m

interpretf :: (Show c, Show fun, SemiRing c, Eq c, Ord fun, Ord var) => I.Interpretation fun (PI.SomePolynomial c) -> R.Term fun var -> P.Polynomial c var
interpretf ebsi = I.interpretTerm interpretFun interpretVar where
  interpretFun f = P.substituteVariables (I.interpretations ebsi `k` f) . M.fromList . zip (toEnum `fmap` [0..])
    where k m g = error ("NaturalPI.interpretf: " ++ show g) `fromMaybe` M.lookup g m
  interpretVar   = P.variable

decode :: Problem F V -> G.Interpretation F Integer -> I.InterpretationProof (P.Polynomial Int PI.SomeIndeterminate) (P.Polynomial Int V)
decode prob ginter =
  I.InterpretationProof
    { I.sig_       = Prob.signature prob
    , I.inter_     = inter
    , I.uargs_     = usableArgsWhereApplicable prob (Prob.isDTProblem prob) True
    , I.ufuns_     = Nothing
    , I.useURules_ = False
    , I.shift_     = I.All -- FIXME: MS: translate correctly for for newProblem
    , I.strictDPs_ = sDPs
    , I.strictTrs_ = sTrs
    , I.weakDPs_   = wDPs
    , I.weakTrs_   = wTrs }

  where
    inter = fromGInterpretation ginter

    (sDPs,wDPs) = L.partition isStrict (rs $ Prob.dpComponents prob)
    (sTrs,wTrs) = L.partition isStrict (rs $ Prob.trsComponents prob)
    isStrict (r,(lpoly,rpoly)) = r `RS.member` Prob.strictComponents prob && P.constantValue (lpoly `sub` rpoly) > 0
    rs trs = [ (r, (interpretf inter lhs, interpretf inter rhs)) | r@R.Rule{R.lhs=lhs,R.rhs=rhs} <- RS.toList trs ]


--- * processor ------------------------------------------------------------------------------------------------------

type GUBSProcessor = (G.Processor F Integer V T.TctM)

data SMTSolver = MiniSmt | Z3 deriving (Show, Bounded, Enum)

data SCC = SCC | NoSCC deriving (Show, Bounded, Enum)

data Minimize = Minimize | NoMinimize deriving (Show, Bounded, Enum)

data GUBSOptions = GUBSOptions
  { selector  :: Selector
  , degree    :: Degree
  , scc       :: SCC
  , smtSolver :: SMTSolver
  , minimize  :: Minimize }
  deriving Show

defaultGUBSOptions :: GUBSOptions
defaultGUBSOptions = GUBSOptions{..} where
  selector  = One
  degree    = 4
  scc       = SCC
  smtSolver = Z3
  minimize  = Minimize


data GUBS = GUBS
  { gubsOptions :: GUBSOptions
  , processor   :: GUBSProcessor }

data GUBSProof = GUBSProof
  { naturalPIProof :: NaturalPIProof
  , executionLog   :: G.ExecutionLog }

instance T.Processor GUBS where
  type ProofObject GUBS = ApplicationProof GUBSProof
  type In  GUBS         = Trs
  type Out GUBS         = Trs
  type Forking GUBS     = T.Optional T.Id

  execute p prob
    | Prob.isTrivial prob = T.succeedWith Closed (const zero) T.Null
    | otherwise           = entscheide p prob


entscheide GUBS{gubsOptions=GUBSOptions{..},..} prob = do
   res <- G.solveWith (encode selector prob) processor
   case res of
    (G.Sat i,l) ->
      T.succeedWith
        (Applicable GUBSProof{naturalPIProof=Order order,executionLog=l})
        (certification order)
        (T.Opt $ T.Id $ I.newProblem' prob (pint_ order))
      where
        order = PolyOrder{kind_=kind, pint_=pint}
        pint = decode prob i
        sig = Prob.signature prob
        err = error "Kind: not defined" -- FIXME: MS: PI.bound gets Kind but does not use it
        kind  = case Prob.startTerms prob of
          Prob.AllTerms{}                       -> PI.Unrestricted     err
          Prob.BasicTerms{Prob.constructors=cs} -> PI.ConstructorBased err (Sig.constructors sig)
    (G.Open _ _,l) -> T.abortWith $ drawTree (Node "Executionlog" l)

    _ -> T.abortWith "Incompatible"



--- * instances ------------------------------------------------------------------------------------------------------

defaultSMTOpts :: [f] -> G.SMTOpts f
defaultSMTOpts fs = G.SMTOpts
  { G.shape    = G.Mixed
  , G.degree   = 2
  , G.restrict = fs
  , G.maxCoeff = Nothing
  , G.maxConst = Nothing
  -- , G.minimize = False}
  , G.minimize = True }

gubs' :: GUBSOptions -> Trs -> TrsStrategy
gubs' gubsOptions@GUBSOptions{..} prob = T.Apply GUBS{gubsOptions, processor} where

  tof fp cs     = G.csToFile cs fp >> return (G.Progress cs)
  logCS cs      = G.logOpenConstraints cs >> return (G.Progress cs)
  logStr str cs = G.logMsg str >> return (G.Progress cs)

  logSMT opts   = logStr $ "SMT: trying " <> strongly <> shape <> " interpretation" <> degree where
    strongly = if G.maxConst opts == Just 1 then "strongly " else ""
    shape    = if G.degree opts == 1 then "linear" else case G.shape opts of {G.MultMixed -> "multmixed"; G.Mixed -> "mixed"}
    degree   = if G.degree opts >  2 then " of degree " ++ show (G.degree opts) else ""

  processor = logCS ==> G.try simplify ==> logCS ==> G.try (G.exhaustive (withSCC (logCS ==> G.try simplify ==> simple (candidates degree)))) where

    withSCC p = case scc of {SCC -> G.sccDecompose p; NoSCC -> p}

    opts = defaultSMTOpts (S.elems $ restricted prob)
    smt' = G.smt $ case smtSolver of {Z3 -> G.Z3; MiniSmt -> G.MiniSmt}
    stronglyMultMixed d = opts { G.degree = d, G.shape = G.MultMixed, G.maxCoeff = Just 1}
    multMixed d         = opts { G.degree = d, G.shape = G.MultMixed, G.maxCoeff = Nothing}
    mixed d             = opts { G.degree = d, G.shape = G.Mixed    , G.maxCoeff = Nothing}

    simple    = foldr (\s -> (==>) (logSMT s ==> G.try (smt' s))) logCS

    candidates deg
      | deg <= 1  = basics
      | otherwise = basics <> [stronglyMultMixed 2] <> extras deg

    basics     = [ stronglyMultMixed 1, multMixed 1 ]
    extras deg = foldr (\d xs -> multMixed d :mixed d :xs) [] [2..deg]
    simplify =
      G.try G.instantiate
      ==> G.try G.propagateEq
      ==> G.try (G.exhaustive (G.propagateUp <=> G.propagateDown))

gubs :: GUBSOptions -> TrsStrategy
gubs opts = tew $ T.withProblem $ \prob ->  gubs' opts prob

-- gubsDeclaration :: T.Declaration(
--   '[ T.Argument 'T.Optional Degree
--    , T.Argument 'T.Optional Selector ]
--   T.:-> TrsStrategy)
-- gubsDeclaration =
--   T.declare
--     "gubs"
--     [ "Polynomial Interpretations with GUBS" ]
--     ( degreeArg `T.optional` 3
--     , selectorArg `T.optional` All )
--     gubs

--- * proof data -----------------------------------------------------------------------------------------------------

instance Show GUBS where
  show = show .gubsOptions

instance PP.Pretty (PolyOrder Int) where
  pretty order = PP.vcat
    [ PP.pretty $ PP.pretty (pint_ order) ]

instance Xml.Xml (PolyOrder Int) where
  toXml order = I.xmlProof (pint_ order) xtype where
    xtype   = Xml.elt "type" [Xml.elt "polynomial" [xdomain, xdegree]]
    xdegree = Xml.elt "degree" [Xml.int $ PI.degree . PI.PolyInter . I.interpretations . I.inter_ $ pint_ order]
    xdomain = Xml.elt "domain" [Xml.elt "naturals" []]
  toCeTA = Xml.toXml

instance Show GUBSProof where
  show = show . PP.pretty

instance PP.Pretty GUBSProof where
  pretty GUBSProof{naturalPIProof=npi,executionLog=log} = PP.vcat
    [ PP.pretty npi
    , PP.text $ drawTree (Node "Executionlog" log)]

instance Xml.Xml GUBSProof where
  toXml GUBSProof{naturalPIProof=npi} = Xml.toXml npi

instance PP.Pretty GUBS where
  pretty _ = PP.text "GUBS"

instance Xml.Xml GUBS where
  toXml _ = Xml.empty

