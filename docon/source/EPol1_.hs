------------------------------------------------------------------------
------------------------------------------------------------------------
--  The Algebraic Domain Constructor  DoCon,   version 2.12
--
--  Copyright  Serge Mechveliani,    2012
------------------------------------------------------------------------
------------------------------------------------------------------------




module EPol1_   -- Extended polynomial operations. Continuation.
                -- See  Pol*.hs, EPol0_.hs.
                -- All needed from here is reexported by  Pol.

(EPVecP, emonMul, mEPolMul, polEPolMul, epolToVecPol, vecPolToEPol, 
 sEPol, mEPVecPMul, sEPVecP
)
where
import Data.List hiding (sortBy, maximum) 
import Prelude   hiding (maximum)

import DPrelude (Length(..), -- class 
                 Natural, Z, maximum, mergeBy, ct, ctr, sortBy, 
                                                        showsWithDom)
import Categs     (Dom(..))
import SetGroup   (MulSemigroup(..), zeroS)
import RingModule (Ring(..), CommutativeRing(), GCDRing(..))
import VecMatr    (Vector(..))
import UPol_      (PolLike(..), Mon, ppoComp, lc)
import Pol_       (Pol(..), polMons, mPolMul)
import Pol__      (sPol)
import EPol0_ (EPol(..), EPPOTerm, EMon, eppoMode, eppoWeights, 
                                   epolMons, epolPol, epolLCoord)




------------------------------------------------------------------------
emonMul :: Ring a =>  a -> Mon a -> EMon a -> [EMon a]
                   -- zero

emonMul z (a, p) (b, (j,q)) =  let c = mul a b  
                               in   
                               if c == z then []  
                               else           [(c, (j, p+q))]

{-# specialize emonMul :: Z -> Mon Z -> EMon Z -> [EMon Z] #-}


mEPolMul :: Ring a => Mon a -> EPol a -> EPol a
mEPolMul              (a, p)   f      =
                      ctr f [(a*b, (i, p+q))| (b, (i, q)) <- epolMons f]

{-# specialize mEPolMul :: Mon Z -> EPol Z -> EPol Z #-}

------------------------------------------------------------------------
polEPolMul :: CommutativeRing a => Pol a -> EPol a -> EPol a
polEPolMul                         f        g = 
                                      ct g $ pm (polMons f) (epolMons g)
  where
  z = zeroS $ sample f
  pm []      _       = []   
  pm _       []      = []   
  pm (m: ms) (n: ns) = (emonMul z m n) ++ mons
       where
       mons = epolMons ((mEPolMul m $ ct g ns) + (ct g $ pm ms (n: ns)))

------------------------------------------------------------------------
epolToVecPol :: CommutativeRing a => Natural -> EPol a -> Vector (Pol a)
                                     -- n       f
  -- Convert e-polynomial  f  to the polynomial vector  Vec [f1..fn] 
  -- of the given size  n  >= (maximal coordinate No in f).
  -- It gathers the monomials of each coordinate to polynomial.
  -- If  f  does not contain monomials of  i-th  coordinate
  -- (for 1 =< i =< n), then  fi = 0.
  -- Detail of method:
  -- the gathered monomials are being sorted - unless the  eppoMode 
  -- in f starts with the `agreed' mode 'a'.
  -- Example:
  -- let f = EPol [(5, (2, x^2*y)), (5, (1, x)), (4, (2, x)), 
  --               (1, (4, y)), (4, (1, x^0*y^0))
  --              ] eo pol
  --     pol = cToPol o ["x","y"] 0  :: Pol Integer
  --     o   = (("", 2), degLex, [])
  --     eo  = (eAntiLex, "a", [], _)
  -- in  epolToVector 6 f -->  Vec [5*x+4, 5*x^2*y+4*x, 0, y, 0, 0]

epolToVecPol  n  f@(EPol emons eo pol) =  
  let
    (zeroP, mode)      = (zeroS pol, eppoMode eo)
    cp                 = ppoComp $ pPPO pol
    cmpp (_, p) (_, q) = cp q p 

    maxCoord   = if  null emons  then  0
                 else                  maximum $ map (fst . snd) emons
    lastZeroes =  
               if n < maxCoord then  
                  error $ concat ["\nepolToVecPol n f,\nn = ", shows n $
                                  showsWithDom 1 f "f" ""
                                  "\nn < maximalCoordinate(f).\n"]
               else  
               genericReplicate (n - maxCoord) zeroP

    toV []      _     = id
    toV (j: js) emons =
           let  
              (of_j, others) = partition ((== j) . fst . snd) emons
              monsOf_j       = [(a, p) | (a, (_, p)) <- of_j]

              sorted = case mode of 'a': _ -> monsOf_j
                                    _      -> sortBy cmpp monsOf_j
           in ((ct pol sorted) :) . toV js others
  in
  Vec $ toV [1 .. maxCoord] emons lastZeroes


------------------------------------------------------------------------
vecPolToEPol :: CommutativeRing a=> EPPOTerm -> Vector (Pol a) -> EPol a
                                    -- eo       Vec [f1..]
-- Inverse to  epolToVecPol. 
-- The monomials of each  fi  extend with the coordinate number i,  are 
-- sorted under  eo  (this is skipped if eo shows `agreed'), and merged 
-- to the previously accumulated (eo-ordered) e-polynomial.

vecPolToEPol eo (Vec []) = 
  let
     {m = eppoMode eo;  wts = eppoWeights eo}
  in
  error $ concat ["\nvecPolToEPol eppOrdTerm (Vec []),\neppOrdTerm = \
                  \(<eppComp>,", m, ",weights,<ppComp>)\nweigths =  ",
                  shows wts "\n\nEmpty vector.\n"]

vecPolToEPol eo (Vec fs) =  
  let
    (ecp, mode, _, _) = eo
    (f, n)            = (head fs, genLength fs)
    monGroups         = zipWith (\ i f -> (i, polMons f)) [1 .. n] fs
    cmp (_, p) (_, q) = ecp q p

    mergeMonGroup emons (i,mons) =
              let
                 emonsOf_i = [(c, (i, p)) | (c, p) <- mons]
                 sorted    = case mode of 'a': _ -> emonsOf_i
                                          _      -> sortBy cmp emonsOf_i
              in mergeBy cmp emons sorted
  in
  EPol (foldl mergeMonGroup [] monGroups) eo f


------------------------------------------------------------------------
sEPol :: GCDRing a => EPol a -> EPol a -> Maybe (EPol a, Mon a, Mon a)

-- sEPol f g  differs from  sPol  
-- in that it is in the Maybe format and returns 
-- Nothing            when the leading coordinates of f and g differ,
-- Just (s-epol, m1, m2),  otherwise

sEPol f g = if  epolLCoord f /= epolLCoord g  then  Nothing
            else
            let h           = epolPol f
                (a, b)      = (lc f, lc g)
                (_, m1, m2) = sPol (ct h (a, lpp f)) (ct h (b, lpp g))
            in          
            Just ((mEPolMul m1 f) + (mEPolMul m2 g), m1, m2) 

------------------------------------------------------------------------
type EPVecP a = (EPol a, [Pol a])                    -- similar to PVecP

mEPVecPMul m (f, v) = (mEPolMul m f, map (mPolMul m) v)

------------------------------------------------------------------------
sEPVecP :: 
     GCDRing a => EPVecP a -> EPVecP a -> Maybe (EPVecP a, Mon a, Mon a)
sEPVecP (f, v1) (g, v2) = 
  case  
      sEPol f g  
  of
  Nothing          -> Nothing
  Just (_, m1, m2) -> 
     let 
       epdiff = (mEPolMul m1 f) - (mEPolMul m2 g)
       vdiff  = zipWith (\ s t -> (mPolMul m1 s) - (mPolMul m2 t)) v1 v2
     in   
     Just ((epdiff, vdiff), m1, m2)




{- reserve **********************************
instance(Convertible a b, AddGroup b) => Convertible (EPol a) (EPol b)
  where cvm (EPol mons _ pol) (EPol _ eo' pol') =
    case (cvm pol pol', sample pol') of(Nothing, _) -> Nothing
      (_      , b) -> Just (reo (EPol (cvMons mons) eo' pol'))
      where reo = reordEPol eo';  cvMons = map (\ (a,p)->(cv a b,p))
instance (CommutativeRing a, Ring b, Convertible a b) => 
                               Convertible (Vector (Pol a)) (EPol b)
  where cvm v f = let  (e,md,w,c) = epolEPPOTerm f  
                        md'        = case  md  of  'a':xs -> xs
                                                   _      -> md
                   in   cvm (vecPolToEPol (e,md',w,c) v) f
instance (CommutativeRing a,Ring b, Convertible a b) => 
                           Convertible (EPol a) (Vector (Pol b))  where
  cvm f v = let (n,ems)  = (vecSize v, epolMons f)
                maxCoord = if  null ems  then  0
                           else         maximum (map (fst.snd) ems)
            in  if  maxCoord > n  then  Nothing
                else                    cvm (epolToVecPol n f) v
********************************************************
-}


