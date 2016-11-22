module Tct.Trs.Processor.Poly.GUBS
  ( gubs
  , gubsDeclaration
  , Selector (..)
  , selectorArg )
where


--- * imports --------------------------------------------------------------------------------------------------------

import qualified Data.List                           as L (partition, (\\))
import qualified Data.Map.Strict                     as M
import           Data.Maybe                          (fromMaybe)
import           Data.Monoid                         ((<>))
import qualified Data.Set                            as S
import           Data.Tree                           (Tree (..), drawTree)

import           Control.Monad                       (forM)
import           Control.Monad.State.Strict

import qualified Data.Rewriting.Rule                 as R
import qualified Data.Rewriting.Term                 as R

import           GUBS                                as G (Constraint (..), (<=>), (==>))
import qualified GUBS                                as G

import qualified Tct.Core.Common.Pretty              as PP
import qualified Tct.Core.Common.Xml                 as Xml
import qualified Tct.Core.Data                       as T

import qualified Tct.Common.Polynomial               as P
import qualified Tct.Common.PolynomialInterpretation as PI
import           Tct.Common.ProofCombinators         (ApplicationProof (..), OrientationProof (..))
import           Tct.Common.Ring                     (Additive, SemiRing, add, sub)

import           Tct.Trs
import           Tct.Trs.Data
import qualified Tct.Trs.Data.Problem                as Prob
import qualified Tct.Trs.Data.ProblemKind            as Prob
import qualified Tct.Trs.Data.Rules                  as RS (member, toList, vars)
import qualified Tct.Trs.Data.Signature              as Sig
import           Tct.Trs.Data.Symbol                 (var)
import qualified Tct.Trs.Encoding.Interpretation     as I
import           Tct.Trs.Encoding.UsablePositions    (usableArgsWhereApplicable, usablePositionsOf)
import           Tct.Trs.Processors                  (Degree, degreeArg)


--- * NaturalPI ------------------------------------------------------------------------------------------------------

data NaturalPI = NaturalPI
  { degree   :: Degree
  , selector :: Selector
  } deriving Show

data Selector = Any | All | First
  deriving (Bounded, Enum, Eq, Show)

selectorArg :: T.Argument 'T.Required Selector
selectorArg = T.flag "orientRules" [ "This argument specifies which rules to orient Strictly  "]

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

restricted :: Problem f v -> Sig.Symbols f
restricted prob = case Prob.startTerms prob of {Prob.BasicTerms{Prob.constructors=cs} -> cs; _ -> S.empty}


--- * encode ---------------------------------------------------------------------------------------------------------
-- construct a ConstraintSystem from a Trs problem

canonicalVar' :: Int -> V
canonicalVar' = var . ("_x" <>) . show

canonicalVar :: Int -> G.Term f V
canonicalVar = G.Var . canonicalVar'

fresh :: State ([G.Term f V],[V]) (G.Term f V)
fresh = do
  (vs,i:is) <- get
  let v = G.Var i
  put (v:vs,is)
  return v

withFreshVars :: S.Set V -> State ([G.Term f V], [V]) a -> (a, [G.Term f V])
withFreshVars vars m = fst <$> runState m ([], filter (`S.member` vars) $ canonicalVar' `fmap` [1..])

canonicalTerm :: (f,Int) -> G.Term f V
canonicalTerm (f,ar)= G.Fun f $ canonicalVar `fmap` [1..ar]

encodeTerm :: R.Term f v -> G.Term f v
encodeTerm (R.Fun f ts) = G.Fun f (encodeTerm `fmap` ts)
encodeTerm (R.Var v)    = G.Var v

-- | Constraint encoding for Polynomial Interpretations, where
-- montonicity: f(x1,...,xn)  >= sum (upos(f))
-- restricted:  x1,...,xn + k >= f(x1,...,xn), for some (currently) fixed k
encode :: NaturalPI -> Problem F V -> G.ConstraintSystem F V
encode p prob =
  orientStrs strs
  <> orientWeakly `fmap` wtrs
  <> monotone `fmap` fs
  <> stronglyLinear `fmap` cs

  where

  strs = RS.toList $ Prob.strictComponents prob
  wtrs = RS.toList $ Prob.weakComponents prob
  upos = usablePositionsOf $ usableArgsWhereApplicable prob (Prob.isDTProblem prob) True
  sig  = Prob.signature prob
  fs   = Sig.elems sig
  cs   = Sig.elems $ Sig.restrictSignature sig (restricted prob)
  vars = RS.vars (Prob.allComponents prob)

  orientStrs rs = case selector p of
    All   -> orientStrictly `fmap` rs
    Any   -> (sum vs :>=: 1) :cs
       where (cs,vs) = withFreshVars vars (forM rs orientStrictlyM)
    First -> if null rs then [] else orientStrictly (head rs) : fmap orientWeakly (tail rs)

  orientStrictlyM R.Rule{R.lhs=l,R.rhs=r} = fresh >>= \v -> return $ encodeTerm l :>=: encodeTerm r + v
  orientStrictly  R.Rule{R.lhs=l,R.rhs=r} = encodeTerm l :>=: encodeTerm r + 1
  orientWeakly    R.Rule{R.lhs=l,R.rhs=r} = encodeTerm l :>=: encodeTerm r

  monotone (f,i)       = canonicalTerm (f,i) :>=: sum (canonicalVar `fmap` upos f)
  stronglyLinear (f,i) = sum (canonicalVar `fmap` [1..i]) + 16 :>=: canonicalTerm (f,i) -- FIXME: MS: use fresh var


--- * decode ---------------------------------------------------------------------------------------------------------
-- translate the result back to Tct

fromGPolynomial :: G.Polynomial G.Var Integer -> P.Polynomial Int PI.SomeIndeterminate
fromGPolynomial p = P.fromView $ k `fmap` G.toMonos p
  where k (c,m) = (fromIntegral c, (\(G.V v, i) -> (toEnum v,i)) <$> G.toPowers m)

fromGInterpretation :: G.Interpretation f Integer -> I.Interpretation f (P.Polynomial Int PI.SomeIndeterminate)
fromGInterpretation (G.Inter m) = I.Interpretation $ M.map fromGPolynomial $ M.mapKeysMonotonic fst m

interpretf :: (Show c, Show fun, SemiRing c, Eq c, Ord fun, Ord var) => I.Interpretation fun (PI.SomePolynomial c) -> R.Term fun var -> P.Polynomial c var
interpretf ebsi = I.interpretTerm interpretFun interpretVar where
  interpretFun f = P.substituteVariables (I.interpretations ebsi `k` f) . M.fromList . zip PI.indeterminates
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
    , I.shift_     = I.All
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

data GUBS = GUBS
  { naturalPI :: NaturalPI
  , processor :: GUBSProcessor }

data GUBSProof = GUBSProof
  { naturalPIProof :: NaturalPIProof
  , executionLog   :: G.ExecutionLog }

instance T.Processor GUBS where
  type ProofObject GUBS = ApplicationProof GUBSProof
  type In  GUBS         = Trs
  type Out GUBS         = Trs
  type Forking GUBS     = T.Optional T.Id

  execute p prob
    | Prob.isTrivial prob = T.abortWith (Closed :: ApplicationProof NaturalPIProof)
    | otherwise           = entscheide p prob

entscheide GUBS{naturalPI=naturalPI,processor=processor} prob = do
   res <- G.solveWith (encode naturalPI prob) processor
   case res of
    (G.Sat i,l) ->
      T.succeedWith
        (Applicable GUBSProof{naturalPIProof=Order order,executionLog=l})
        (certification order)
        (I.newProblem prob (pint_ order))
      where
        order = PolyOrder{kind_=kind, pint_=pint}
        pint = decode prob i
        sig = Prob.signature prob
        kind  = case Prob.startTerms prob of
          Prob.AllTerms{}                       -> PI.Unrestricted     undefined
          Prob.BasicTerms{Prob.constructors=cs} -> PI.ConstructorBased undefined (Sig.constructors sig)

    _ -> T.abortWith "Incompatible"



--- * instances ------------------------------------------------------------------------------------------------------

defaultSMTOpts :: [f] -> G.SMTOpts f
defaultSMTOpts fs = G.SMTOpts
  { G.shape    = G.Mixed
  , G.degree   = 2
  , G.restrict = fs
  , G.maxCoeff = Nothing
  , G.maxConst = Nothing
  , G.minimize = False}

gubs' :: Trs -> Degree -> Selector -> TrsStrategy
gubs' prob deg sl = T.Apply GUBS{naturalPI=naturalPI, processor=processor} where

  naturalPI = NaturalPI{degree=deg,selector=sl}

  logCS cs      = G.logOpenConstraints cs >> return (G.Progress cs)
  logStr str cs = G.logMsg str >> return (G.Progress cs)
  logSMT opts = logStr $ strongly <> shape <> "interpretation" <> degree where
    strongly = if G.maxConst opts == Just 1 then "strongly " else ""
    shape    = if G.degree opts == 1 then "linear" else case G.shape opts of {G.MultMixed -> "multmixed"; G.Mixed -> "mixed"}
    degree   = if G.degree opts >  2 then " of degree " ++ show (G.degree opts) else ""

  processor =
    logCS ==> G.try simplify ==> logCS ==> G.try (G.exhaustive (G.sccDecompose (logCS ==> G.try simplify ==> simple (candidates deg))))
      where
        opts = defaultSMTOpts (S.elems $ restricted prob)
        smt' = G.smt G.Z3
        stronglyMultMixed d = opts { G.degree = d, G.shape = G.MultMixed, G.maxCoeff = Just 1}
        multMixed d         = opts { G.degree = d, G.shape = G.MultMixed, G.maxCoeff = Nothing}
        mixed d             = opts { G.degree = d, G.shape = G.Mixed    , G.maxCoeff = Nothing}

        simple    = foldr (\s -> (==>) (logSMT s ==> G.try (smt' s))) logCS

        candidates deg
          | deg <= 1  = basics
          | otherwise = basics <> [stronglyMultMixed 2] <> extras deg

        basics     = [ stronglyMultMixed 1, multMixed 1, stronglyMultMixed 2 ]
        extras deg = foldr (\d xs -> multMixed d :stronglyMultMixed d :xs) [] [2..deg]
        simplify =
          G.try G.instantiate
          ==> G.try G.propagateEq
          ==> G.try (G.exhaustive (G.propagateUp <=> G.propagateDown))

gubs :: Degree -> Selector -> TrsStrategy
gubs sh sel = T.withProblem $ \prob -> gubs' prob sh sel


gubsDeclaration :: T.Declaration(
  '[ T.Argument 'T.Optional Degree
   , T.Argument 'T.Optional Selector ]
  T.:-> TrsStrategy)
gubsDeclaration =
  T.declare
    "gubs"
    [ "Polynomial Interpretations with GUBS" ]
    ( degreeArg `T.optional` 3
    , selectorArg `T.optional` All )
    gubs

--- * proof data -----------------------------------------------------------------------------------------------------

instance Show GUBS where
  show = show . naturalPI

instance PP.Pretty (PolyOrder Int) where
  pretty order = PP.vcat
    [ PP.text "We apply a polynomial interpretation of kind " <> PP.pretty (kind_ order) <> PP.char ':'
    , PP.pretty $ PP.pretty (pint_ order) ]

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

