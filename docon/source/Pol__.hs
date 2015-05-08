------------------------------------------------------------------------
------------------------------------------------------------------------
--  The Algebraic Domain Constructor  DoCon,   version 2.12
--
--  Copyright  Serge Mechveliani,    2012
------------------------------------------------------------------------
------------------------------------------------------------------------





module Pol__   -- Some more items for (multivariate) Polynomials. 
               -- See  manual.txt  and  UPol_*, PP_*, Pol_*.
               -- All needed from here is  reexported by  Pol.

(PVecP, sPol, mPVecPMul, sPVecP, shows_,
 RPolVar, showsRPolVar, SPProduct, SPMon, SPPol', showsSPPol'
)
where
import qualified Data.Map as Map (lookup)

import DPrelude 
       (DShow(..), -- class
        ShowOptions(..), PropValue(..), less_m, addToShowOptions
       )
import Categs     (CategoryName(..), Domain1(..)        )
import SetGroup   (Set(..), MulSemigroup(..), zeroS, neg)
import RingModule (Ring(..), GCDRing(..), isOrderedRing ) 
import VecMatr    (vecRepr                              )
import PP_        (ppComplement                         )
import UPol_      (PolLike(..), Mon, lc                 )
import Pol_       (Pol(..), mPolMul                     ) 

import qualified Pol_ (sub_)





------------------------------------------------------------------------
sPol :: GCDRing a => Pol a -> Pol a -> (Pol a, Mon a, Mon a)
                                        -- sp  m1     m2
-- S-polynomial  (the one related to Groebner basis)
-- for the Non-zero polynomials:                    sp = m1*f-m2*g
-- It also returns the corresponding 
-- complementary monomial factors  m1, m2.

sPol f g = let {a = lc f;   b = lc g;   p = lpp f;   q = lpp g;
                d = gcD [a, b];
                (ppfc, ppgc) = (ppComplement p q, ppComplement q p);
                (m1, m2)     = ((b/d, ppfc), (a/d, ppgc))}
           in
           (Pol_.sub_ (mPolMul m1 f) (mPolMul m2 g),  m1, m2)

------------------------------------------------------------------------
shows_ :: Ring a => ShowOptions -> Pol a -> String -> String

-- LOCAL.
-- Write polynomial to string.
-- Prepends the polynomial image to the initial string  s.
-- If  a  is and Ordered ring, then the mode `ord'  is set which writes 
-- ..- m  instead of  ..+(-m)  for the negative coefficient monomials.
-- If  a  has unity  then unity coefficient images  are skipped.

shows_ opt (Pol mons c _ vars dom) =   
  (case 
       (zeroS c, unity_m c, Map.lookup Ring dom)  
   of
   (zr, unM, Just (D1Ring rR)) -> ss zr unM $ isOrderedRing rR
   _                           -> 
         error $ msg "\n\nRing term  not found in coefficient domain.\n"
  )
  where
  opt' = addToShowOptions (-1) opt
  msg  = showString "\nshows_ opt f str,  \nf <- " . showsDomOf 1 c . 
         shows vars . showString ",\nPower products = " . 
         shows (map (vecRepr . snd) mons)

  ss zr unM ordered =
   let  
     mons' = [(c, vecRepr v) | (c, v) <- mons]

     -- wpp :: [String] -> [Integer] -> String -> String
     --        vars                               writing power product
     --
     wpp _      []     = id
     wpp []     _      =  
                error $ msg "\n\nWrong representation for  f:\nsome \
                            \power product exceeds the variable list.\n"
     wpp (v: vs) (n: pp) = 
              case (n, all (== 0) pp) 
              of
              (0, _   ) -> wpp vs pp
              (1, True) -> (v++) . wpp vs pp
              (1, _   ) -> (v++) . ('*':) . wpp vs pp
              (n, True) -> (v++) . ('^':) . shows n . wpp vs pp
              _         -> (v++) . ('^':) . shows n . ('*':) . wpp vs pp
     -------------------------------------------------------------------
     wMon (c, pp) =  
       let 
          pp_str = wpp vars pp ""
       in
       case (unM, pp_str)  
       of 
       (_,       []) -> dShows opt' c
       (Nothing, _ ) -> dShows opt' c . ('*':) . (pp_str ++)
       (Just un, _ ) -> if c == un then (pp_str ++)
                        else        dShows opt' c . ('*':) . (pp_str ++)
     -------------------------------------------------------------------
     wr mons = 
        case (ordered, mons) 
        of
        (_,   []           ) -> ('0' :) 
        (_,   [m]          ) -> wMon m
        (Yes, m: (c, p): ms) ->
            if 
              less_m c zr then  wMon m . (" - "++) . wr ((neg c, p): ms)
            else                wMon m . (" + "++) . wr ((c,p)     : ms)

        (_,   m: ms        ) -> wMon m . (" + "++) . wr ms
   in
   ('(' :) . wr mons'. (')' :)


------------------------------------------------------------------------
type PVecP a = (Pol a, [Pol a])

-- Polynomial-vector-polynomial  fv = (f,v)  is supplied with the 
-- polynomial pre-vector  v.  
-- v  is often used to accumulate the coefficients  fi  of some  f
-- - relatively to some initial basis  gs:   f = f1*g1+...+fm*gm.
-- This serves for accumulating of the  quotient  (transformation)
-- part in  moduloBasis, gBasis.

mPVecPMul :: Ring a => Mon a -> PVecP a -> PVecP a
mPVecPMul              m    (f, gs) =  (mPolMul m f, map (mPolMul m) gs)


sPVecP :: (GCDRing a, Set (Pol a)) => 
          PVecP a -> PVecP a -> (PVecP a, Mon a, Mon a)
sPVecP    (f, us)    (g, vs) =  ((pdiff, vdiff), m1, m2)
              where                         -- s-polynomial for  PVecP a
              (_, m1, m2) = sPol f g
              pdiff       = Pol_.sub_ (mPolMul m1 f) (mPolMul m2 g)
              (ps, qs)    = (map (mPolMul m1) us, map (mPolMul m2) vs)
              vdiff       = (zipWith Pol_.sub_ ps qs)


------------------------------------------------------------------------
type RPolVar = [Integer]      
             -- r-pol (and sparse-pol) variable is actually a multiindex

showsRPolVar :: String -> RPolVar -> String -> String 
showsRPolVar    pref      ind     =  showString pref . showsInd ind
                 where
                 showsInd []      = id
                 showsInd (j: js) = showChar '_' . shows j . showsInd js
           

type SPProduct = [(RPolVar, Integer)]
type SPMon a   = (a, SPProduct)
type SPPol' a  = [SPMon a]       
  -- 
  -- This, with  SPPol,  has to replace in future most of  Pol.
  --
  -- Sparse-exponent pre-polynomial.
  -- Example:  x[1,1]*x[1,50]^2*x[9,1] - 2*x[1,50]^2 + x[1,50] - 1
  --           <-->
  --           [ ( 1,  [([1,1],1),([1,50],2),([9,1],1)] )
  --             ( -2, [ ([1,50],2) ]                   )
  --             ( 1,  [ ([1,50],1) ]                   )
  --             ( -1, []                               )

showsSPPol' :: 
            Ring a => ShowOptions -> a        -> Maybe a -> PropValue ->
                      String      -> SPPol' a -> String  -> String

showsSPPol' opt zr mbUn ord varName f =  ('(':) . wr f . (')':)
  where
  opt'    = addToShowOptions (-1) opt
  wr mons = 
    case (ord, mons) 
    of
    (_,   []           ) -> ('0' :) 
    (_,   [m]          ) -> wMon m
    (Yes, m: (c, p): ms) ->
       if  
         less_m c zr  then  wMon m . (" - "++) . wr ((neg c, p): ms)
       else                 wMon m . (" + "++) . wr ((c, p)    : ms)

    (_,   m: ms        ) -> wMon m . (" + "++) . wr ms

  wMon (c, pp) =  
    let  
       ppStr = wpp pp ""
    in
    case (mbUn, ppStr)  
    of 
    (_      , []) -> dShows opt' c
    (Nothing, _ ) -> dShows opt' c . ('*':) . (ppStr++)
    (Just un, _ ) -> if c == un then  (ppStr++)
                       else           shows c . ('*':) . (ppStr++)

  wpp []             = id
  wpp ((ind, n): pp) =  
    let  
       sv = showsRPolVar varName ind 
    in
    case (n, pp) of (1, []) -> sv 
                    (1, _ ) -> sv . ('*':) . wpp pp
                    (_, []) -> sv . ('^':) . shows n 
                    _       -> sv . ('^':) . shows n . ('*':) . wpp pp
