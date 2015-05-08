------------------------------------------------------------------------
------------------------------------------------------------------------
--  The Algebraic Domain Constructor  DoCon,   version 2.12
--
--  Copyright  Serge Mechveliani,    2012
------------------------------------------------------------------------
------------------------------------------------------------------------




module Pol2_ where  -- Continuation for Pol_, Pol1_ ...
                    -- All needed from here is reexported by  Pol.
 
-- LinSolvRing, EuclideanRing  instances for  UPol,
-- LinSolvRing                                Pol,
-- instance..=> LinSolvLModule (Pol  a) (EPol a),
--              LinSolvLModule (Pol  a) (Vector (Pol  a)),
--              LinSolvLModule (UPol a) (Vector (UPol a))


import qualified Data.Map as Map (empty, lookup,  insert)

import Data.List (groupBy)

import DPrelude (Length(..), PropValue(..), ct, lookupProp, maxBy, 
                                    mapmap, mapfmap, showsWithDom, sum1)
import Categs     
       (Dom(..), CategoryName(..), Domain1(..), Domain2(..),
        Domains1, EucRingTerm(..), GCDRingTerm(..),
        Property_EucRing(..), Property_GCDRing(..), 
        LinSolvRingTerm(..), Property_LinSolvRing(..), 
        LinSolvModuleTerm(..), Property_LinSolvModule(..)
       )
import SetGroup 
import RingModule (CommutativeRing(), GCDRing(..), 
                   EuclideanRing(..), LinSolvRing(..), Field(), 
                   LinSolvLModule(..), isField
                  )
import VecMatr (Vector(..), vecSize, rowMatrMul)
import UPol_   (PolLike(..), UPol(..), ppoComp, lc, cPMul, cToUPol,
                                                       lexPPO, upolMons)
import Pol_   (Pol(..), cToPol, toUPol, fromUPol)
import Pgcd_  ()
import EPol_  (EPol(..), epolPol,ecpTOP0,vecPolToEPol,epolToVecPol)
import GBasis (polNF, gBasis, polRelGens, gBasis_e, polNF_e, 
                                                    polRelGens_e)



------------------------------------------------------------------------
toOverHeadVar ::
         CommutativeRing a => Domains1 (UPol a) -> Pol a -> Pol (UPol a)
                              -- dX1 
-- Bring polynomial to tail variables: 
--                                   a[x1,x2...xn] --> (a[x1])[x2...xn].
-- n > 1  needed, and only  lexComp  ordering is considered on the power
-- products of [x1,x2..xn], [x2..xn].
-- New  PPOId  for  [x2..xn]  is  ("lex", n-1). 
-- dX1  is the domain description for  a[x1].

toOverHeadVar dX1 f@(Pol mons c _ vars dA) = 
  if 
    n < 2 then  error $ concat ["\ntoOverHeadVar domX1 f,\nf <- ", 
                               showsDomOf 1 (sample f) $ shows (pVars f)
                               "\n:\nmore than one variable needed.\n"]
  else
  sum1 (zeroP: (map lift $ groupBy eqX1deg mons))
    where                                  -- denote P = (a[x1])[x2..xn]
    (v: vars', n) = (vars, genLength vars) 
    zeroX1        = cToUPol v dA (zeroS c)
    zeroP         = cToPol (lexPPO (pred n)) vars' dX1 zeroX1

    eqX1deg (_, Vec (i: _)) (_, Vec (j: _)) =  i == j 
    lift ms =
          ct zeroP [(ct zeroX1 (a, i), Vec js) | (a, Vec (i: js)) <- ms]
               -- converts 
               -- group of monomials over `a' into polynomial over a[x1] 

------------------------------------------------------------------------
fromOverHeadVar :: CommutativeRing a => Pol (UPol a) -> Pol a

-- Inverse to  toOverHeadVar:  (a[y])[x1...xn] --> a[y,x1...xn] 
-- Only  lexComp  ordering is considered on the power products.

fromOverHeadVar (Pol mons c _ vars _) = sum1 (zero': (map convMon mons))
  where
  (n, a, dA, [v]) = (genLength vars, sample c, dom c, pVars c) 
  zero'           = cToPol (lexPPO $ succ n) (v: vars) dA (zeroS a)
  convMon (g, Vec js) = 
                       ct zero' [(a, Vec (i: js))| (a, i) <- upolMons g] 

     
------------------------------------------------------------------------
instance EuclideanRing a => LinSolvRing (UPol a)   
  where                                      -- apply  UPol a <--> Pol a 
  gxBasis fs = (map toUPol gs, mapmap toUPol mt)
                                     where  
                                     (gs, mt) = gBasis $ map fromUPol fs

  moduloBasis mode fs f = (toUPol r, map toUPol qs)
               where
               (r, qs) = moduloBasis mode (map fromUPol fs) (fromUPol f)

  syzygyGens mode fs = mapmap toUPol $ polRelGens mode $ map fromUPol fs

  baseLinSolvRing f dom = 
    case 
        (Map.lookup LinSolvRing dom, 
                                baseLinSolvRing (fromUPol f) Map.empty)
    of
    (Just (D1LinSolvR r), _     ) -> (dom, r)
    (_,                   (_, r)) ->
                        (Map.insert LinSolvRing (D1LinSolvR r') dom, r')
            where
            r' = LinSolvRingTerm {linSolvRingProps = linSolvRingProps r}



------------------------------------------------------------------------
instance Field a => EuclideanRing (UPol a)
  where                         -- Presumed:  (IsField, Yes) for  dom f.

  divRem _  = pDivRem                  
  eucNorm f = if isZero f then  error ("\neucNorm 0\nfor  " ++ 
                                                  (showsDomOf 1 f "\n"))
              else              deg f

  baseEucRing  smp@(UPol _ _ _ aDom)  dom =
    (case
         (Map.lookup EuclideanRing dom, Map.lookup Ring aDom)
     of
     (Just (D1EucR r), _               )-> (dom, r)
     (_,               Just (D1Ring aR))-> erg $ isField aR
     _                                  -> (dom, error $ msg msg')
    )
    where
    msg = showString "\nbaseEucRing samplePol pDom," . 
                                    showsWithDom 1 smp "samplePol" ""
    msg' = "\nRing term must reside in the coefficient domain,\nwith \
                                                      \isField /= No.\n"
    erg No = (dom, error $ msg msg')
    erg _  = (Map.insert EuclideanRing (D1EucR rg) dom, rg)
    rg = EucRingTerm 
                {eucRingProps = [(Euclidean, Yes), (DivRemCan, Yes), 
                                 (DivRemMin, Yes)]}


------------------------------------------------------------------------
instance EuclideanRing a => LinSolvRing (Pol a)   
  where
  -- Euclidean `a' is sufficient for the syzygy bases finding and 
  -- the ideal inclusion solvability.
  -- For the canonical reduction modulo ideal (presented by the
  -- fixed basis), it is required  ***(DivRemCan,Yes)***  for `a'.
  --
  -- See  Manual `linr',`pol.a.gr','gx'.

  gxBasis    = gBasis 
  syzygyGens = polRelGens     

  moduloBasis mode fs f =     -- mode = ""|"c"|"g"|"cg"
    let      
      m     = genLength fs
      cMode = if  elem 'c' mode  then "c"  else ""
      isGxB = m < 2 || elem 'g' mode
    in
    if  any (\ x -> not $ elem x "gc") mode  then
        error $ concat 
        ["\nmoduloBasis ", mode, " fs f,",
         showsWithDom 1 f "f" "" ("\nmode  string may be only" ++
                                  "  \"\",  \"c\",  \"g\",  \"cg\" \n")]
    else
    if isGxB then  polNF cMode fs f
                                   -- polNF does not find Groebner basis
    else 
    let {(gs, mt) = gBasis fs;  (r, qs) = polNF cMode gs f;
         zeroP   = zeroS f}
    in         
    if null gs then (f, map (const zeroP) fs)
    else            (r, rowMatrMul qs mt    )

  baseLinSolvRing f fdom =  
    (case 
         (Map.lookup LinSolvRing fdom, Map.lookup EuclideanRing (dom f))
     of
     (Just (D1LinSolvR r), _               ) -> (fdom, r)
     (_,                   Just (D1EucR aR)) -> szr $ eucRingProps aR
     _                                       ->
                                              (fdom, error $ msg msgLkp)
    )
    where
    msg = showString "\nbaseLinSolvRing samplePol pDom," . 
          showsWithDom 1 f "samplePol" "" 
    msgLkp = "\nEucRingTerm not found for coefficients\n"
    msgEuc = "\nisEucRing  yielded  No  for coefficients\n"
    szr ps = 
          case [lookupProp p ps | p <- [Euclidean,DivRemCan]] 
          of
          [No , _   ] -> (fdom, error $ msg msgEuc)
          [isE, isCn] -> (Map.insert LinSolvRing (D1LinSolvR r) fdom, r)
                where
                r = LinSolvRingTerm {linSolvRingProps =
                                         [(IsGxRing,             isCn),
                                          (ModuloBasisCanonic,   isCn),
                                          (ModuloBasisDetaching, isE ), 
                                          (WithSyzygyGens,       isE )]}

------------------------------------------------------------------------
instance EuclideanRing a => LinSolvLModule (Pol a) (EPol a)
  where
  canAssocM _ f = case (isZero f, inv $ canInv $ lc f)
                  of
                  (True, _) -> f
                  (_,    c) -> if c == unity c  then  f  else  cPMul c f

  canInvM smp f = if  isZero f  then  error ("\ncanInvM smp 0\nfor  "
                                               ++ (showsDomOf 1 f "\n"))
                  else  ct smp $ canInv $ lc f

  gxBasisM    _ = gBasis_e
  syzygyGensM _ = polRelGens_e 

  moduloBasisM _ mode fs f =
    let     
      m     = genLength fs
      cMode = if  elem 'c' mode  then "c"  else ""
      isGxB = m < 2 || elem 'g' mode
    in
    if  any (\ x -> not $ elem x "gc") mode  then
        error $ concat
        ["\nmoduloBasisM samplePair ", mode, " fs f,",
         showsWithDom 1 f "f" "" ("\nmode  string may be only" ++
                                  "  \"\",  \"c\",  \"g\",  \"cg\" \n")]
    else
    if isGxB then  polNF_e cMode fs f
    else 
    let {(gs, mt) = gBasis_e fs;      (r, qs) = polNF_e cMode gs f;
         zeroP    = zeroS $ epolPol f}
      in         
      if null gs then (f, map (const zeroP) fs)
      else            (r, rowMatrMul qs mt    )

  baseLinSolvLModule (pol, _) fdom =
    case 
        (Map.lookup LinSolvLModule fdom, dom pol)  
    of
    (Just (D2LinSolvM m), _ ) -> (fdom, m)
    (_,                   aD) ->
      (case (erM, isE)  
       of
       (Nothing, _ ) -> (fdom, error $ msg msgLkp)
       (_,       No) -> (fdom, error $ msg msgEuc)
       _             ->
                      (Map.insert LinSolvLModule (D2LinSolvM m) fdom, m)
      )
      where
      (erM, grM) = (Map.lookup EuclideanRing aD, Map.lookup GCDRing aD)
      (Just (D1EucR er), Just (D1GCDR gr)) = (erM, grM)
      (eps, gps) = (eucRingProps er, gcdRingProps gr)
      (cnAs, isE, canRem) = (lookupProp WithCanAssoc gps,
                             lookupProp Euclidean    eps,
                             lookupProp DivRemCan    eps)
      m = LinSolvModuleTerm 
             {linSolvModuleProps = [(IsGxModule,             canRem),
                                    (IsCanAssocModule,       cnAs  ),
                                    (ModuloBasisDetaching_M, isE   ),
                                    (ModuloBasisCanonic_M,   canRem),
                                    (WithSyzygyGens_M,       isE   )]
             }
      msg = showString "\nbaseLinSolvLModule (polSample, epolSample)\
                                                         \currentDom," .
                                       showsWithDom 1 pol "polSample" ""
      msgLkp = "\nEucRingTerm not found for coefficients.\n"
      msgEuc = "\nisEucRing  yielded  No  for coefficients.\n"

------------------------------------------------------------------------
instance EuclideanRing a => LinSolvLModule (Pol a) (Vector (Pol a))
  where
  -- This uses the isomorphism to  EPol a  defined by particular epp
  -- comparison (ecpTOP0 False).
  -- That is for (i,pp), compare first pp, then, if equal, see the 
  -- position No: the smaller i means the greater (i, pp).

  canInvM f (Vec gs) = if  null gis  then  unity f
                       else                canInv $ fst $ maxBy cpp gis
          where 
          gis = filter (not . isZero . fst) $ zip gs [1 ..]
          cpp (f, i) (g, j) = case (cp (lpp f) (lpp g), compare j i)
                              of
                              (EQ, c) -> c 
                              (c,  _) -> c
          cp = ppoComp (pPPO f)

  canAssocM f v = let c = inv $ lc $ canInvM f v
                  in  if c == unity c then  v  else  fmap (cPMul c) v

  syzygyGensM f mode vs = syzygyGensM f mode $ map (vecPolToEPol eo) vs
                                where
                                eo = (ecpTOP0 False cp, "a", [], cp)
                                cp = ppoComp $ pPPO f

  gxBasisM _ []        = ([], [])
  gxBasisM f vs@(v: _) = 
                   let (n, cp)   = (vecSize v, ppoComp $ pPPO f)
                       eo        = (ecpTOP0 False cp, "a", [], cp)
                       (egs, mt) = gxBasisM f $ map (vecPolToEPol eo) vs
                   in  (map (epolToVecPol n) egs, mt)

  moduloBasisM _ _    [] u = (u, [])
  moduloBasisM f mode vs u =  
                         let (n, cp)   = (vecSize u, ppoComp $ pPPO f)
                             eo        = (ecpTOP0 False cp, "a", [], cp)
                             eh: efs   = map (vecPolToEPol eo) (u: vs)
                             (eh', qs) = moduloBasisM f mode efs eh
                         in  (epolToVecPol n eh', qs)
 
  baseLinSolvLModule (f, v) vdom =
    case 
        (Map.lookup LinSolvLModule vdom, dom f) 
    of
    (Just (D2LinSolvM m), _ ) -> (vdom, m)
    (_,                   aD) ->
      (case (eRM, isE)
       of       
       (Nothing, _ ) -> (vdom, error $ msg msgLkp)
       (_,       No) -> (vdom, error $ msg msgEuc)
       _             -> 
                      (Map.insert LinSolvLModule (D2LinSolvM m) vdom, m)
      )
      where
      (gRM, eRM) = (Map.lookup GCDRing aD, Map.lookup EuclideanRing aD)
      (Just (D1GCDR gR), Just (D1EucR eR)) = (gRM, eRM)

      (gProps, eProps)    = (gcdRingProps gR, eucRingProps eR)
      (cnAs, isE, canrem) = (lookupProp WithCanAssoc gProps,
                             lookupProp Euclidean    eProps,
                             lookupProp DivRemCan    eProps
                            )
      m = LinSolvModuleTerm
             {linSolvModuleProps = [(IsCanAssocModule,       cnAs  ),
                                    (IsGxModule,             canrem),
                                    (ModuloBasisDetaching_M, isE   ),
                                    (ModuloBasisCanonic_M,   canrem),
                                    (WithSyzygyGens_M,       isE   )]
             }
      msg = showString "\nbaseLinSolvLModule (polSample, vSample) \
                                \currentDom,\nfor  Vector P  over  P," .
            showsWithDom 1 f "polSample" "P" . 
            showString "dim(Vector) =  " . shows (vecSize v)
      msgLkp = "\nEucRingTerm not found for coefficients.\n"
      msgEuc = "\nisEucRing  yielded  No  for coefficients.\n"


------------------------------------------------------------------------
instance EuclideanRing a => LinSolvLModule (UPol a) (Vector (UPol a))
  where
  canInvM f (Vec gs) = if  null gis  then  unity f
                       else                canInv $ fst $ maxBy cpp gis
        where 
        gis = filter (not . isZero . fst) $ zip gs [1 ..]

        cpp (f, i) (g, j) = case (compare (deg f) (deg g), compare j i)
                            of
                            (EQ, c) -> c 
                            (c,  _) -> c

  canAssocM f v = let c = inv $ lc $ canInvM f v
                  in  if  c == unity c  then  v  else  fmap (cPMul c) v

  syzygyGensM f mode vs = mapfmap toUPol $ syzygyGensM f' mode vs'
                          where
                          (f', vs') = (fromUPol f, mapfmap fromUPol vs)

  gxBasisM f vs = (mapfmap toUPol us, mapfmap toUPol mt)
                 where
                 (us, mt) = gxBasisM (fromUPol f) $ mapfmap fromUPol vs

  moduloBasisM f mode vs u =  
        let
           (fu, mapfu, mapto) = (fromUPol, fmap fromUPol, fmap toUPol)
           (r, qs)           =  
                       moduloBasisM (fu f) mode (map mapfu vs) (mapfu u)
        in (mapto r, map toUPol qs)
 
  baseLinSolvLModule (f, v) vdom =                    -- same as for Pol
    case 
        (Map.lookup LinSolvLModule vdom, dom f) 
    of
    (Just (D2LinSolvM m), _ ) -> (vdom, m)
    (_,                   aD) ->
      (case (eRM, isE)
       of       
       (Nothing, _ ) -> (vdom, error $ msg msgLkp)
       (_,       No) -> (vdom, error $ msg msgEuc)
       _             -> 
                      (Map.insert LinSolvLModule (D2LinSolvM m) vdom, m)
      )
      where
      (gRM, eRM) = (Map.lookup GCDRing aD, Map.lookup EuclideanRing aD)
      (Just (D1GCDR gR), Just (D1EucR eR)) = (gRM, eRM)
      (gProps, eProps)    = (gcdRingProps gR, eucRingProps eR)
      (cnAs, isE, canrem) = (lookupProp WithCanAssoc gProps,
                             lookupProp Euclidean    eProps,
                             lookupProp DivRemCan    eProps)
      m = LinSolvModuleTerm
             {linSolvModuleProps = [(IsCanAssocModule,       cnAs  ),
                                    (IsGxModule,             canrem),
                                    (ModuloBasisDetaching_M, isE   ),
                                    (ModuloBasisCanonic_M,   canrem),
                                    (WithSyzygyGens_M,       isE   )]
             }
      msg = showString "\nbaseLinSolvLModule (polSample, vSample) \
                                \currentDom,\nfor  Vector P  over  P," .
            showsWithDom 1 f "polSample" "P" .
            showString "dim(Vector) =  " . shows (vecSize v)
      msgLkp = "\nEucRingTerm not found for coefficients.\n"
      msgEuc = "\nisEucRing  yielded  No  for coefficients.\n"
