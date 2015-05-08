------------------------------------------------------------------------
------------------------------------------------------------------------
--  The Algebraic Domain Constructor  DoCon,   version 2.12
--
--  Copyright  Serge Mechveliani,    2012
------------------------------------------------------------------------
------------------------------------------------------------------------





module GBas_ 
  -- Groebner basis for polynomials over Euclidean ring.
  -- This module refers to the implementation given in 
  --                                                GBasFld_, GBasEuc_.
  -- All needed from here is  reexported by  GBasis.

(gBasis, gBasis_e, isGBasis, isGBasis_e, gBasisWithRadicals, 
 initVecs_  -- for Polrel_ only
)  
where
import Data.List (partition)

import DPrelude (Length(..), -- classes 
                 ct, PropValue(..), showsWithDom
                )
import SetGroup   (AddGroup(..), unity, zeroS, isZero)
import RingModule (Ring(..),EuclideanRing(..), isField, isEucRing)
import VecMatr    (scalarMt, Vector(..))
import Pol_       (Pol(..), polPPComp, polMons)
import EPol0_     (EPol(..), epolPol, polToEPol, epolToPol)
import GBasFld_   (gBas_field_ev_, isGBas_field_ev_)

import qualified GBasEuc_ (gbas_ev_, isgbas_ev_)






------------------------------------------------------------------------
initVecs_ :: AddGroup a => a -> [b] -> [ (b, [a]) ]
initVecs_ x ys =  zip ys $ scalarMt ys x$ zeroS x 


------------------------------------------------------------------------
gBasis :: EuclideanRing a => [Pol a] -> ([Pol a], [[Pol a]])
                             -- fs       gs       mt

{- The  reduced Groebner basis (g-basis)   gs  
   for the polynomials  fs  over an Euclidean GCD-ring R  (= `a').

   In particular, R may be a field.
   
When R is a  field,  gBasis  builds the  (strong)  reduced  Groebner 
basis, which is the unique representation of the *ideal*.
Otherwise, returned is a *weak* reduced Groebner basis
  - this is arranged so only because it is simpler to obtain the
  canonical remainder by  gs  applying the  polNF   reduction with 
  the "c" mode.
gs  is ordered increasingly by lpp by the pp-comparison contained in
fi.
For the field, and more generally,  for  R  possessing 
(WithCanAssoc,Yes),  gi  are in the canonical associated form.

The matrix  mt  is also accumulated such that 
                                mt*(transpose [fs]) == transpose [gs]

Zero elements of  fs  correspond to the zero columns in  mt.
In the case of all  fs  being zeroes, the result is  ([],[]).

Method.
-------
This is only the head function. The true method is given in  
gBas_field_ev_, gBas_euc_ev_ - see this file below and in 
GBasEuc.hs.
To reduce to these two functions, gBasis acts as follows.

Stores the positions of zeroes in  fs  and clears them from  fs;
embeds fs to e-polynomials setting the constant coordinate j = 1;
appends the i-th canonical polynomial vector  vi= (0..1..0)  to 
  each  fi  forming  fvs;
finds the coefficient ring property values  prop  - for the cases
  "field", "euclidean";
computes Groebner basis  gvs  by applying the "e-vector-ed" 
  version of the Groebner basis: gBas_field_ev_ or GBasEuc_.gbas_ev_
  - depending on the value of  prop;
unzip-s  gvs  to  (gs,vs)  and inserts the zero columns in the 
  matrix  vs  in the stored positions;
converts  gs  back to polynomials.

Also  gBasis  calls for a more generic function gBasis_e.  The 
latter provides the g-basis for  fs  in the module  M = P +...+ P
(r times) over the polynomial ring P, the elements of M being 
represented by the  e-polynomials  (see EPol.hs).
-}

gBasis []        = ([], [])
gBasis fs@(f: _) = (map epolToPol gs, mt)
                  where 
                  cp                = polPPComp f
                  ecp (_, p) (_, q) = cp p q
                  eo                = (ecp, "a", [], cp)
                  (gs, mt)          = gBasis_e $ map (polToEPol 1 eo) fs

------------------------------------------------------------------------
gBasis_e :: EuclideanRing a => [EPol a] -> ([EPol a], [[Pol a]])
gBasis_e fs =  
             if all isZero fs then ([], []) else (gs, vs')
 where
 pol@(Pol _ c _ _ aD) = epolPol $ head fs
 (zeroPol, unPol) = (zeroS pol, unity pol)
 (aD1, rC )       = baseRing c aD
 (_,   erC)       = baseEucRing c aD1
 m                = genLength fs   -- part zeroes
 nfs              = zip [1 .. m] fs
 (zNfs, nonzNfs)  = partition (isZero . snd) nfs
 (nonzInds, fs')  = unzip nonzNfs   -- fs' contains non-zero fi
 fvs = initVecs_ unPol fs'
 gvs = case (isField rC, isEucRing erC) 
       of  
       (Yes, _  ) -> gBas_field_ev_    fvs
       (_,   Yes) -> GBasEuc_.gbas_ev_ fvs 
       _          -> error $ messgGBasE_ fs "gBasis_e" 
                             "\nEuclidean coefficient ring required.\n"
 -----------------------------------------------------------------------
            -- return zeroes to the stored positions in each row from vs
 (gs, vs) = unzip gvs
 nvs      = map (zip nonzInds) vs
 zNfs_p   = [(i, zeroPol) | (i, _) <- zNfs]
 vs'      = map (merge zNfs_p) nvs

 merge []                 nfs                = map snd nfs
 merge nzs                []                 = map snd nzs
 merge nzs@((i, z): nzs') nfs@((j, f): nfs') =  
                                     if i < j then  z: (merge nzs' nfs )  
                                     else           f: (merge nzs  nfs')

------------------------------------------------------------------------
messgGBasE_ :: EuclideanRing a => [EPol a] -> String -> String -> String
messgGBasE_ fs@(f: _)   funcName =
                    showString (funcName ++ " fs,\nlength fs = ") . 
                    shows (genLength fs) . showsWithDom 1 f "head fs" "" 

------------------------------------------------------------------------
                                         -- "is a (weak) Groebner basis"
isGBasis :: EuclideanRing a => [Pol a] -> Bool
isGBasis []      = True
isGBasis (f: fs) = isGBasis_e $ map (polToEPol 1 eo) (f: fs)
                   where
                   cp                = polPPComp f
                   ecp (_, p) (_, q) = cp p q
                   eo                = (ecp, "a", [], cp)

isGBasis_e :: EuclideanRing a => [EPol a] -> Bool
isGBasis_e fs =  
  case  
      filter (not . isZero) fs  
  of
  []         -> True
  fs'@(f: _) ->  
             let pol@(Pol _ c _ _ aD) = epolPol f
                 (aD1, rC )           = baseRing    c aD
                 (_,   erC)           = baseEucRing c aD1
                 v                    = map (const pol) fs'
                             -- dummy vector parts suffice because there
                             -- is no  gBas.._e  function, only _ev  one
                 fvs' = [(f, v) | f <- fs']
             in
             case (isField rC, isEucRing erC)
             of
             (Yes, _  ) -> isGBas_field_ev_    fvs'
             (_,   Yes) -> GBasEuc_.isgbas_ev_ fvs'
             _          -> error $ messgGBasE_ fs "isGBasis_e" 
                           "\nan Euclidean coefficient ring required.\n"

------------------------------------------------------------------------------
trimIfMonomial :: AddGroup a => Pol a -> Pol a
trimIfMonomial f =                            -- Example:  x^3*y*z^2 --> x*y*z
                   case polMons f
                   of
                   [(c, Vec js)] -> ct f (c, Vec $ map (min 1) js)
                   _             -> f  

isMonomialWithMultipInPP :: Pol a -> Bool 
isMonomialWithMultipInPP f =  case polMons f  of
                                              [(_, Vec js)] -> any (1 <) js
                                              _             -> False

gBasisWithRadicals :: EuclideanRing a => [Pol a] -> [Pol a]
                                         -- fs      gs     
--
-- To be generalized to  square-freeing **
--
-- Trimming gives a stronger basis which defines the same variety.
-- Example:  x^3*y*z^2 = 0  is equivalent to  x*y*z.

gBasisWithRadicals fs =  let gs = fst $ gBasis fs
                         in
                         if  any isMonomialWithMultipInPP gs  then
                                 gBasisWithRadicals $ map trimIfMonomial gs
                         else    gs
