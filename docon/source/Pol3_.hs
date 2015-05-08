------------------------------------------------------------------------
------------------------------------------------------------------------
--  The Algebraic Domain Constructor  DoCon,   version 2.12
--
--  Copyright  Serge Mechveliani,    2012
------------------------------------------------------------------------
------------------------------------------------------------------------


{-# LANGUAGE ScopedTypeVariables, MonoLocalBinds #-}

module Pol3_   -- Continuation for Pol_ ... Pol2_
               -- All needed from here is reexported by Pol.

(VecPol(..), vpRepr, vpEPPOTerm, vpECp, vpToV
 -- , instances for  VecPol  up to  LinSolvLModule (Pol a) (VecPol a)
)
where
import qualified Data.Map as Map (empty, lookup)

import DPrelude (Length(..), DShow(..), 
                 maxBy, ct, mapmap, fmapfmap, showsn, showsWithDom)

import Categs (Dom(..), CategoryName(..), Domain1(..), Domain2(..), 
                                                       Domains1)
import SetGroup 
import RingModule 
       (Ring(..), CommutativeRing(), GCDRing(..), EuclideanRing(..),
        LinSolvRing(..), LeftModule(..), LinSolvLModule(..), fromi, 
        isoRing, isoModule, isoLinSolvModule, isoDomains1, 
        isoDomains22, upLinSolvRing 
       )
import VecMatr (Vector(..))
import UPol_   (PolLike(..), UPol(..), lc, cPMul, lexPPO, cToUPol,
                                                             upolMons)
import Pol_  (Pol(..), reordPol, headVarPol, fromHeadVarPol)
import Pol2_ () 
import EPol_ (EPPComp, EPPOTerm, eppoECp, vecPolToEPol, epolToVecPol,
                                                  eppoMode, eppoWeights)




------------------------------------------------------------------------
data VecPol a = VP [Pol a] EPPOTerm 

  -- VecPol        is introduced because it is more generic than
  -- Vector . Pol  for the  LinSolvLModule  instance.
  --
  -- Namely, varying the  epp ordering  contained in  VP fs eo  
  -- one can view a free module over  Pol a  under different 
  -- orderings, for example, ecpTOP_weights.
  -- In  VP fs eo,  the list  fs  corresponds to polynomial vector.
  -- eo  is an admissible epp ordering, as in EPol.
  -- eo is needed to compare the monomials of different positions in
  -- vector. And it defines the *isomorphism* to  EPol a.
  --
  -- REQUIREMENT.
  -- eo  must agree with  cp  contained in polynomials,  that is
  -- cp and ecp restricted to any fixed position No i have to define 
  -- the same ordering.


instance Ring a => Show  (VecPol a) where showsPrec _ = showsn 0 
instance Ring a => DShow (VecPol a) where
                                    dShows opt = dShows opt . vpRepr
vpRepr :: VecPol a -> [Pol a]
vpRepr (VP fs _) = fs

vpEPPOTerm :: VecPol a -> EPPOTerm
vpEPPOTerm (VP _ o) =  o

vpECp :: VecPol a -> EPPComp
vpECp =  eppoECp . vpEPPOTerm  

vpToV :: VecPol a -> Vector (Pol a)
vpToV =  Vec . vpRepr

instance Eq a => Eq (VecPol a) where  u == v =  (vpRepr u == vpRepr v)

instance Dom VecPol 
  where  
  sample vp = case vpRepr vp of  f: _ -> sample f
                                 _    -> error "\nsample (VP [] _).\n"
  dom vp = case vpRepr vp of  f: _ -> dom f
                              _    -> error "\ndom (VP [] _).\n"


------------------------------------------------------------------------
-- before  LinSolvLModule,  the instances for VecPol  are 
-- isomorphic to the ones for  Vector .Pol


instance CommutativeRing a => Set (VecPol a)
  where
  compare_m = compareTrivially

  showsDomOf verb (VP fs o) = 
    case 
        (fs, eppoMode o, eppoWeights o)  
    of
    (f: _, _, _  ) -> showString "{VecPol " . shows (pVars f) . 
                      showChar ' ' . showsDomOf (pred verb) (sample f) . 
                      showChar '}'
    (_,    m, wts) -> 
                 error $ concat 
                 ["\nshowsDomOf (VP [] o),\nvpEPPOTerm o = (<ecp>, ", m,
                  " weights <cp>),\nweights =  ", shows wts 
                  "\n:\nVP  needs non-empty polynomial list.\n"]

  fromExpr (VP fs o) e = case fromExpr fs e of
                                         ([gs], "" ) -> ([VP gs o], "" )
                                         (_,    msg) -> ([],        msg)
  baseSet  vp@(VP _ o) dom =  
     case 
         Map.lookup Set dom  
     of
     Just (D1Set s) -> (dom, s)
     _              -> 
             let vToVP (Vec gs) = VP gs o
                 dom'           = isoDomains1 vpToV vToVP dom
                 (dom'1, s')    = baseSet (vpToV vp) dom'
             in  (isoDomains1 vToVP vpToV dom'1, isoOSet vToVP vpToV s')


instance CommutativeRing a => AddSemigroup (VecPol a)
  where
  add (VP fs o) v  = VP (zipWith add fs $ vpRepr v) o
  zero_m (VP fs o) = Just $ VP gs o   where  Vec gs = zeroS $ Vec fs
  neg_m (VP fs o)  = Just $ VP (map neg fs) o
  times_m (VP fs o) n = Just $ VP [times f n | f <- fs] o
                                               
  baseAddSemigroup vp@(VP _ o) dom = 
     case 
         Map.lookup AddSemigroup dom  
     of
     Just (D1Smg s) -> (dom, s)
     _              -> 
        let vToVP (Vec gs) = VP gs o
            dom'           = isoDomains1 vpToV vToVP dom
            (dom'1, s')    = baseAddSemigroup (vpToV vp) dom'
        in  (isoDomains1 vToVP vpToV dom'1, isoSemigroup vToVP vpToV s')


instance CommutativeRing a => AddMonoid (VecPol a)
instance CommutativeRing a => AddGroup  (VecPol a)
  where
  baseAddGroup vp@(VP _ o) dom =  
     case  
         Map.lookup AddGroup dom  
     of
     Just (D1Group s) -> (dom,s)
     _                -> 
            let vToVP (Vec gs) = VP gs o
                dom'           = isoDomains1 vpToV vToVP dom
                (dom'1, s')    = baseAddGroup (vpToV vp) dom'
            in  (isoDomains1 vToVP vpToV dom'1, isoGroup vToVP vpToV s')


instance CommutativeRing a => MulSemigroup (VecPol a)
  where
  mul (VP fs o) v =  VP (zipWith mul fs $ vpRepr v) o
  unity_m (VP fs o) = case  unity_m $ Vec fs  of
                                        Just (Vec gs) -> Just $ VP gs o
                                        _             -> Nothing
  inv_m (VP fs o) = case inv_m (Vec fs) of
                                        Just (Vec gs) -> Just $ VP gs o
                                        _             -> Nothing

  divide_m (VP fs o) (VP gs _) = case divide_m (Vec fs) (Vec gs)
                                 of
                                 Just (Vec hs) -> Just $ VP hs o
                                 _             -> Nothing
  divide_m2 _ _ = error 
                    "\ndivide_m2 (VP ..) _:   use  divide_m  instead.\n"

  power_m (VP fs o) n = Just $ VP [power f n | f <- fs] o
  root n (VP fs o) = fmapfmap (\ (Vec gs) -> VP gs o) $ root n $ Vec fs

  baseMulSemigroup vp@(VP _ o) dom = 
     case  
         Map.lookup MulSemigroup dom  
     of
     Just (D1Smg s) -> (dom, s)
     _              -> 
        let vToVP (Vec gs) = VP gs o
            dom'           = isoDomains1 vpToV vToVP dom
            (dom'1, s')    = baseMulSemigroup (vpToV vp) dom'
        in  (isoDomains1 vToVP vpToV dom'1, isoSemigroup vToVP vpToV s')


instance CommutativeRing a => MulMonoid (VecPol a)

instance CommutativeRing a => Num (VecPol a)  
  where  
  negate = neg
  (+)    = add
  (-)    = sub
  (*)    = mul
  signum _ = error "\nsignum (VP ..):  it is senseless for polynomial\
                                                           \ vectors.\n"
  abs _ = error "\nabs (VP ..):  it is senseless for polynomial \
                                                            \vectors.\n"
  fromInteger _ = error "\nfromInteger _  to (VecPol ..):  it is \
                                                    \senseless there.\n"


instance CommutativeRing a => Fractional (VecPol a)  
  where
  (/)            = divide
  fromRational _ = error "\nfromRational _  to (VecPol ..):  it is \
                                                    \senseless there.\n"


instance CommutativeRing a => Ring (VecPol a)
  where
  fromi_m (VP fs o) n = Just $ VP [fromi f n | f <- fs] o  

  baseRing vp@(VP _ o) dom =  
           case  
               Map.lookup Ring dom 
           of
           Just (D1Ring s) -> (dom, s)
           _               -> 
             let vToVP (Vec gs) = VP gs o
                 dom'           = isoDomains1 vpToV vToVP dom
                 (dom'1, s')    = baseRing (vpToV vp) dom'
             in  (isoDomains1 vToVP vpToV dom'1, isoRing vToVP vpToV s')


instance CommutativeRing a => CommutativeRing (VecPol a)

instance CommutativeRing a => LeftModule (Pol a) (VecPol a)
  where
  cMul f (VP fs o) = VP (map (mul f) fs) o

  baseLeftModule (f, vp@(VP _ o)) dom = 
      case  
          Map.lookup LeftModule dom  
      of
      Just (D2Module s) -> (dom, s)
      _                 -> 
          let vToVP (Vec gs) = VP gs o
              dom'           = isoDomains22 vpToV vToVP dom
              (dom'1, s')    = baseLeftModule (f, vpToV vp) dom'
          in  (isoDomains22 vToVP vpToV dom'1, isoModule vToVP vpToV s')


------------------------------------------------------------------------
instance EuclideanRing a => LinSolvLModule (Pol a) (VecPol a) 
  where
  -- this instance uses the isomorphism to  EPol a  defined by
  -- the epp ordering from VP

  canInvM f (VP gs o) = if  null gis  then  unity f
                        else           canInv $ fst $ maxBy comp gis
                       where 
                       gis = filter (not . isZero . fst) $ zip gs [1 ..]
                       comp (f, i) (g, j) = ecp (i, lpp f) (j, lpp g)
                       ecp                = eppoECp o

  canAssocM f v@(VP fs o) = let c = inv $ lc $ canInvM f v
                            in  
                            if c == unity c then  v
                            else                 VP (map (cPMul c) fs) o
  syzygyGensM smp mode [] = 
           error $ concat ["\nsyzygyGensM samplePol ", mode, " [],",
                           showsWithDom 1 smp "samplePol" "R[..]"
                           "\nNon-empty list over  VecPol R  needed.\n"]

  syzygyGensM smp mode (vp: vps) = 
                       syzygyGensM smp mode $ map (vecPolToEPol o) vs
                          where
                          {o = vpEPPOTerm vp;  vs = map vpToV (vp: vps)}

  gxBasisM _ []        = ([], [])
  gxBasisM f (vp: vps) = 
    let
       VP fs o   = vp
       (n, vs)   = (genLength fs, map vpToV (vp: vps))
       (egs, mt) = gxBasisM f $ map (vecPolToEPol o) vs
       vgs       = map ((\ (Vec gs) -> VP gs o) . epolToVecPol n) egs
    in (vgs, mt)

  moduloBasisM _ _    []  u         = (u, [])
  moduloBasisM f mode vps (VP hs o) =  
    let
       n         = genLength hs
       efs       = map (vecPolToEPol o . vpToV) vps
       (eh', qs) = moduloBasisM f mode efs $ vecPolToEPol o (Vec hs)
       Vec h's   = epolToVecPol n eh'
    in (VP h's o, qs)

  baseLinSolvLModule (f, vp@(VP _ o)) dom = 
    case 
        Map.lookup LinSolvLModule dom  
    of
    Just (D2LinSolvM s) -> (dom, s)
    _                   -> 
       let vToVP (Vec gs) = VP gs o
           dom'           = isoDomains22 vpToV vToVP dom
           (dom'1, s')    = baseLinSolvLModule (f, vpToV vp) dom'
       in   
       (isoDomains22 vToVP vpToV dom'1, isoLinSolvModule vToVP vpToV s')


------------------------------------------------------------------------
-- Trying isomorphism  PP = a[x1..xn][y1..yn] <--> a[x1..xn,y1..yn] 
-- for defining  gx-operations for  PP.

instance (LinSolvRing (Pol a), CommutativeRing a) => 
                                              LinSolvRing (UPol (Pol a))
  where
  -- gxBasis  in  P[y],  P = a[x1..xn].
  -- Map to  a[y,x1..xn]  apply  gxBasis there,  return to  P:

  gxBasis []       = ([], [])
  gxBasis fs@(f:_) = (map back gs, mapmap back mt)   -- !?
    where
    UPol _ p y dP    = f
    (o, n)           = (pPPO p, genLength $ pVars p)
    (toLex, fromLex) = (reordPol $ lexPPO n, reordPol o)
    p'               = toLex p
    dP' :: (LinSolvRing (Pol a), CommutativeRing a) => Domains1 (Pol a)
    dP' = upLinSolvRing p' Map.empty  
                                  -- p needs lexPPO reordering, then,
                                  -- its domain bundle needs change too!
    s' = cToUPol y dP' p'  
                      -- sample for P'[y],  P' = a[x1..xn]  with lexComp
    toOverP'   = ct s' . map (\ (a, j) -> (toLex a,   j)) . upolMons
    fromOverP' = ct f  . map (\ (a, j) -> (fromLex a, j)) . upolMons
                                                      -- P[y] <--> P'[y]
    back     = fromOverP' . headVarPol dP
    (gs, mt) = gxBasis $ map (fromHeadVarPol . toOverP') fs  


  moduloBasis mode gs f = (back t, map back qs)
    where                                     -- similarly as in gxBasis
    UPol _ p y dP    = f
    (o, n)           = (pPPO p, genLength $ pVars p)
    (toLex, fromLex) = (reordPol $ lexPPO n, reordPol o)
    p'               = toLex p
    dP'              = upLinSolvRing p' Map.empty  
    s'               = cToUPol y dP' p'  
    toOverP'   = ct s' . map (\ (a, j) -> (toLex a,   j)) . upolMons
    fromOverP' = ct f  . map (\ (a, j) -> (fromLex a, j)) . upolMons
    back       = fromOverP' . headVarPol dP
    h: hs      = map (fromHeadVarPol . toOverP') (f: gs)
    (t, qs)    = moduloBasis mode hs h

  syzygyGens _ _ = error "\nsyzygyGens _ _   for  UPol (Pol _):\n\
                         \not defined so far, sorry.\n"
  baseLinSolvRing _ _ = error "\nbaseLinSolvRing  for  UPol (Pol _):\n\
                              \not defined so far, sorry.\n"




{- reserve ****************************************************
instance (Ring a, Ring b, Convertible a b) =>
                             Convertible (VecPol a) (VecPol b)  where
  cvm vp vp' = case  (cvm (vpToV vp) (vpToV vp'), vpEPPOTerm vp')
               of(Just (Vec hs), o) -> Just (VP hs o);  _ -> Nothing
instance (Ring a, Ring b, Convertible a b) =>
                             Convertible (VecPol a) (Vector (Pol b))
  where cvm vp = cvm (vpToV vp)
instance (Ring a, Ring b, Convertible a b) =>
                             Convertible (Vector (Pol a)) (VecPol b)
  where  cvm v (VP gs o) = case  cvm v (Vec gs)  of
         Just (Vec hs) -> Just (VP hs o);    _ -> Nothing
***************************************************************
-}
