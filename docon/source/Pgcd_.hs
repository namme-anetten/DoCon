------------------------------------------------------------------------
------------------------------------------------------------------------
--  The Algebraic Domain Constructor  DoCon,   version 2.12
--
--  Copyright  Serge Mechveliani,    2012
------------------------------------------------------------------------
------------------------------------------------------------------------






------------------------------------------------------------------------
-- GCD of polynomials.
-- PREFACE.
--
-- The case of the univariate polynomials f, g <- R[x]  over  a field R 
-- is done by usual Euclidean method.
--
-- In the case of R[x],  R a GCD-ring, we apply pseudodivision which 
-- differs from the Euclidean one by the multiplication of the current  
-- f  by the same  b = lc g   - before each reduction. This also needs
-- extracting the polynomial  content  after each pseudodivision. This 
-- content is GCD of the coefficients.
--
-- For  f,g <- R[x1,...,xn]  we
--   reorder  f,g  with the lexicographic power product order;
--   map  f,g  to  f',g' <- (R[x2,...,xn])[x1] ;
--   find  res = gcd f' g'  using that  R[x2,...,xn]  has gcd by 
--                                                        recursion;
--   return  res  to  R[x1,...,xn]  and to the initial ordering.
--
-- Here the recursion means that  R, R[xn], R[x(n-1),xn],..,R[x1,..,xn]
-- became the rings with GCD.
--
-- For gcd in  E[x],  E an Euclidean ring,  the Chinese remainder 
-- method  upolGCD_Chinese  is implemented.
------------------------------------------------------------------------



module Pgcd_  -- all needed from here is  reexported by  Pol

( -- GCDRing instance  for  UPol a, Pol a
 gcdTerm_, upolGCD_generic, upolGCD_Chinese
)
where
import qualified Data.Map as Map (empty, lookup, insert)

import Data.Maybe (fromJust)

import DPrelude (Length(..), -- class
                 PropValue(..), lookupProp, ct, ctr, and3, showsn, 
                                                           showsWithDom)
import Categs (Dom(..), CategoryName(..), Domain1(..), Domains1,
               Subring(..), GCDRingTerm(..), Property_GCDRing(..),
                                                           ResidueE(..))
import SetGroup (Set(..), zeroS, isZero, unity, inv, divides, 
                                                     isFiniteSet)
import RingModule 
       (Ring(..), GCDRing(..), FactorizationRing(..),
        EuclideanRing(..), upGCDRing, upEucFactrRing, upField, isField, 
        isGCDRing, eucGCDE, eucIdeal, remEuc
       )
import VecMatr (Vector(..))
import UPol_ (PolLike(..), UPol(..), lexPPO, upolMons, lc, pCont, cPMul,
                                     cToUPol, upolPseudoRem
             )
import Pol_ (Pol(..), toUPol, fromUPol, reordPol, headVarPol, 
                                                      fromHeadVarPol)
import Pol1_    () -- instance..CommutativeRing (Pol a)
import ResEuc0_ (Residue(..))
import ResEuc_  ()






------------------------------------------------------------------------
instance GCDRing a => GCDRing (UPol a)
  where
  -- canInv,canAssoc  presume  
  -- ***(WithCanAssoc,Yes)***  for the coefficient ring

  canInv f = if isZero f then  error ("\ncanInv 0  in  " ++  
                                                 (showsDomOf 1 f ".\n"))
             else  ct f $ canInv $ lc f

  canAssoc f = if isZero f then  f
               else              cPMul (inv $ canInv $ lc f) f

  gcD []      = error "\ngcD []  :: UPol a.\n"
  gcD (f: fs) = 
    let 
      {z = zeroS f;  aR = snd $ baseGCDRing (sample f) $ dom f}
    in
    case isGCDRing aR
    of
    Yes -> foldl upolGCD_generic z $ filter (/= z) (f: fs)
    _   -> error $ concat 
           ["\ngcD (f: fs),", showsWithDom 1 f "f" "" 
            "\n(IsGCDRing, Yes) needed for the coefficient ring.\n"]
                 
  hasSquare      = upolHasSquare
  toSquareFree _ = 
    error $ concat 
      ["toSquareFree (UPol ..) :  it is not defined so far.\n",
       "It can be implemented by combining  pDeriv and gcD,\n",
       "or simply derived from  factor f,\n",
       "the latter may cost much more than (gcD - pDeriv) method).\n"]

  baseGCDRing f = gcdTerm_ (showsn 1 f "") (showsDomOf 1 f "") f

------------------------------------------------------------------------
upolHasSquare :: GCDRing a => UPol a -> Bool

upolHasSquare f =  not (isZero f)  &&  (hasSquare ct || hasSq fPrim)
  where
  ct     = pCont f                   -- f has square iff content(f)
  fPrim  = fromJust $ pCDiv f ct     -- or primitive part has square
  (a,dA) = (sample f, dom f)
  hasSq f =      -- here f is primitive, non-zero
    deg f > 1  
    && 
    (case (subringChar rA, aFiniteField)
     of
     (Just 0, _  ) -> deg (gcD [f, f']) > 0
     (Just q, Yes) -> caseFinField q
     _             -> 
       error $ concat ["\nhasSquare f,", showsWithDom 1 f "f" "R[.] :"
                   "\nonly the case   char(R) = 0  OR  finiteField(R)\n\
                   \(for a GCDRing R)  can handle, so far.\n"]
    )
    where
    f'           = pDeriv [(1, 1)] f
    (dA', sA)    = baseSet  a dA
    (_, rA)      = baseRing a dA'
    aFiniteField = and3 (isField rA) (isFiniteSet sA)
    caseFinField q =                                -- it may occur f'=0
                     all (== 0) rems || deg (gcD [f, f']) > 0
                                where
                                rems = [rem (snd m) q | m <- upolMons f]
                 --
                 -- If each exponent is a multiple of  q  then  f = g^q
                 -- - because each coefficient is the q-th power in  rA.
                 -- Otherwise, the squares are detected via f' (/= 0).


gcdTerm_ :: Dom p => String -> String -> p a -> Domains1 (p a) -> 
                                     (Domains1 (p a), GCDRingTerm (p a))
  -- common for  UPol, Pol, RPol

gcdTerm_ fStr fDomStr f dm = 
  (case  
       (Map.lookup GCDRing dm, Map.lookup GCDRing (dom f))
   of
   (Just (D1GCDR r), _               ) -> (dm, r)
   (_,               Just (D1GCDR aR)) -> gcr $ gcdRingProps aR
   _                                   -> (dm, error$ msg msg')
  )
  where
  msg = showString "\nbaseGCDRing polSample currentDom,\npolSample = " .
        showString (fStr ++ ("\n <-  " ++ fDomStr))
  msg' = "\n\nGCDRingTerm  must reside in the coefficient domain," ++
                                            "\nwith  isGCDRing /= No.\n"
  gcr aProps = 
    case [lookupProp p aProps | p <- [WithGCD, WithCanAssoc]]
    of
    No: _    -> (dm, error $ msg msg')
    [wg, wc] -> (Map.insert GCDRing (D1GCDR r) dm, r)
                where
                r = GCDRingTerm
                    {gcdRingProps = [(WithCanAssoc, wc), (WithGCD, wg)]}


------------------------------------------------------------------------
instance GCDRing a => GCDRing (Pol a)
  where
  baseGCDRing f = gcdTerm_ (showsn 1 f "") (showsDomOf 1 f "") f

  -- canInv, canAssoc  presume  
  -- ***(WithCanAssoc,Yes)***  for the coefficient ring

  canInv f = if isZero f then  error ("\ncanInv 0\nin  " ++ 
                                                  (showsDomOf 1 f "\n"))
             else  ct f $ canInv $ lc f

  canAssoc f = if isZero f then  f
               else              cPMul (inv $ canInv $ lc f) f

  gcD []      = error "\ngcD []  :: Pol a.\n"
  gcD (f: fs) = 
    let 
      {z = zeroS f;  aR = snd $ baseGCDRing (sample f) (dom f)}
    in
    case isGCDRing aR  
    of
    Yes -> foldl polgcd_ z $ filter (/= z) (f: fs)
    _   -> error $ concat ["\ngcD (f: fs),", showsWithDom 1 f "f" ""
                "\n(IsGCDRing, Yes) needed for the coefficient ring.\n"]

  hasSquare _ = 
              error "\nhasSquare (Pol _):  it is not defined, so far.\n"
  toSquareFree _ = 
           error "\ntoSquareFree (Pol _):  it is not defined, so far.\n"
      
------------------------------------------------------------------------
upolGCDOverField f g =  gcdp f g                                -- LOCAL 
  where
  z        = zeroS f
  gcdp f g = if g == z then canAssoc f  else  gcdp g (snd $ pDivRem f g)
                                   
------------------------------------------------------------------------
upolGCD_generic :: GCDRing a => UPol a -> UPol a -> UPol a      -- LOCAL 
upolGCD_generic f g =                                          
  (case 
       (isZero f, isZero g) 
   of
   (True, _   ) -> canAssoc g
   (_,    True) -> canAssoc f
   _            ->
     if  isField r == Yes  then  upolGCDOverField f g
     else
     case (deg f, deg g)    -- reduce to primitives
     of        
     (0, _) -> ct f $ gcD [lc f, ctg]
     (_, 0) -> ct f $ gcD [lc g, ctf]
     _      -> let cfGcd     = gcD [ctf, ctg]
                   fPrim     = divByCoef f ctf 
                   gPrim     = divByCoef g ctg
               in  cPMul cfGcd $ canAssoc $ gcdPrimitives fPrim gPrim
  )
  where
  (dm, un)   = (dom f, unity $ sample f)
  (ctf, ctg) = (pCont f, pCont g)
  r          = snd $ baseRing un dm

  divByCoef f c = 
    case (c == un, pCDiv f c) 
    of
    (True, _     ) -> f
    (_,    Just q) -> q
    _              -> 
                     error $ concat 
                     ["\nPgcd_.upolGCD_generic f g,\nf =  ",
                      showsn 1 f $ showsWithDom 1 g "g" ""
                      "\n... divByCoef:  coefficient division failed.\n\
                      \Are the coefficients from a GCD-ring ?\n"]

  -- Here  f,g  are primitive and non-constant.
  -- See D.Knuth "The art of programming", Vol.2, Algorithm E.
  -- section from 4.6.1.
  -- But the pseudodivision is slightly different ...
  -- The following method is simple and generic, but may cause a
  -- considerable intermediate coefficient growth. 

  gcdPrimitives f g =  if  deg f < deg g  then  p g f  else  p f g   
                                                      -- here f, g /= 0,
  p f g = let rem = upolPseudoRem f g                 -- deg f >= deg g
          in
          if  isZero rem  then  divByCoef g $ pCont g
          else
          if  deg rem == 0  then  unity f
          else                    p g $ divByCoef rem $ pCont rem

------------------------------------------------------------------------
polgcd_ :: GCDRing a => Pol a -> Pol a -> Pol a     -- multivariate case
polgcd_                 f        g     =       
  let
    (c, ord, vars, varsG) = (sample f, pPPO f, pVars f, pVars g)
    f'  = removeHeadVar f
    dm' = upGCDRing f' Map.empty    -- ! this refers again to polGCD

    (varNum, varNumG)                = (genLength vars, genLength varsG)
    removeHeadVar (Pol mons _ _ vs dm) =
                       Pol [(c, Vec $ tail ns) | (c, Vec ns) <- mons]
                           c 
                           (lexPPO ((genLength vs)-1)) (tail vs) dm

    prependHeadVar v (Pol mons _ _ vs dm) =
                      Pol [(c, Vec (0: ns)) | (c, Vec ns) <- mons]
                           c
                           (lexPPO (succ $ genLength vs)) (v: vs) dm
    --------------------------------------------------------------------
    -- Reducing to single variable.  f, g <- a[x1..xn] are non-zero.

    recurse f g =  
      case (pVars f, degInVar 0 1 f, degInVar 0 1 g) 
      of
      ([_],  _, _) -> fromUPol $ upolGCD_generic (toUPol f) (toUPol g)
      (v: _, 0, 0) -> prependHeadVar v $ recurse f' g' where
                                     [f', g'] = map removeHeadVar [f, g]

      (v: _, 0, _) -> prependHeadVar v $ recurse f' g'
                  where
                  {f' = removeHeadVar f;  g' = pCont $ headVarPol dm' g}

      (v: _, _, 0) -> prependHeadVar v $ recurse f' g'
                                       where
                  {g' = removeHeadVar g;  f' = pCont $ headVarPol dm' f}

      _            -> fromHeadVarPol $ upolGCD_generic f' g'
                                  where
                                  [f', g'] = map (headVarPol dm') [f, g]

    msg = showString "Pgcd_.polgcd_ f g,\nf =  " . showsn 1 f . 
          showsWithDom 1 g "g" ""
    --------------------------------------------------------------------
  in 
  case (varNum > 0, varNum == varNumG, isZero f, isZero g) 
  of
  (False, _,     _,    _   ) ->
                              error $ msg "\nNumber of variables < 1.\n"
  (_,     False, _,    _   ) -> 
                   error $ msg "\nf,g  have different variable lists.\n"
  (_,     _,     True, True) -> f  
  (_,     _,     True, _   ) -> canAssoc g 
  (_,     _,     _,    True) -> canAssoc f
  _                          -> let lexO = lexPPO varNum
                                    f'   = reordPol lexO f
                                    g'   = reordPol lexO g
                                in  reordPol ord $ recurse f' g'

------------------------------------------------------------------------
upolGCD_Chinese :: (EuclideanRing a, FactorizationRing a, 
                    GCDRing (UPol a), Ring (ResidueE a)     -- OI **
                   ) 
                   => UPol a -> UPol a -> UPol a

  -- Chinese - Remainder method for GCD in  a[x], 
  -- `a'  a c-Euclidean domain with the "primes" function,
  --                      (IsField,No), (WithPrimes,Yes)  required.
  -- Method.
  -- Reduce to the case of primitive  f, g.
  -- Find  h(p) = gcd (f mod p) (g mod p)  in  (a/(p))[x]  with
  --   different prime p (reciprocally non-associated),  p  does not
  --   divide  gcl = gcd (lc f) (lc g);  h(p) = gcl*h(p).
  --                                                     (?)  
  -- Repeating this, lift  h(p)  to  res, res' ...  over 
  --   a/(p1), a/(p1*p2) ... until  m = p1*...  is so large that
  --   res == res'  for the last current  res.
  --   If  deg h(p)  increases, this  p  is skipped,
  --   if it decreases, the lift loop restarts with this  h(p).
  -- Returning from `lift', if  cres = res/(cont res)  divides f and
  -- g,  then  cres  is the result, otherwise, the new lift loop 
  -- starts with next  p  and new first  res = h(p).
  -- The correctness of this method is proved in the books.
  --
  -- CAUTION.  This program was tested for  a = (Z/(p))[t]. 
  --           For  a = Integer,  it has a bug:   gcd (x-1) (x-1). 

upolGCD_Chinese f g = 
  (case  
       (isZero f, isZero g, deg f, deg g)
   of
   (True, _   , _, _) -> canAssoc g
   (_,    True, _, _) -> canAssoc f
   (_,    _,    0, _) -> ct f $ gcD [lc f, cntg]
   (_,    _,    _, 0) -> ct f $ gcD [lc g, cntf]
   _                  -> cPMul (gcD [cntf, cntg]) $ gcdPrim f' g'
  )
  where
  (cntf, cntg) = (pCont f, pCont g)
  f'           = canAssoc $ fromJust $ pCDiv f cntf
  g'           = canAssoc $ fromJust $ pCDiv g cntg
  divByCont f  = canAssoc $ fromJust $ pCDiv f (pCont f)

  gcdPrim f g =             -- here  f,g  are non-constant and primitive
    findBase
          (min degF degG) [p | p <- primes lcF, not $ divides p gcl]
                                                -- maybe, both ?
    where
    (degF, degG)    = (deg f, deg g)
    (lcF, lcG)      = (lc f, lc g)
    (unityPol, gcl) = (unity f, gcD [lcF, lcG])
    dividesBoth h   = divides h f && divides h g   -- SCC "dividesBoth"
    findBase bnd (p: ps) = let {res = gcdModulo p f g;  dres = deg res}
                           in 
                           case (dres, dres > bnd)  
                           of 
                           (0, _   ) -> unityPol
                           (_, True) -> findBase bnd ps
                           _         -> lift (cPMul gcl res) p ps

    lift res m (p: ps) =           -- res  is a "base" being "lifted" to
      let                          -- the candidate for  gcd f g.
                                   -- Here  (lc <everything>) = 1  (?)
        h    = cPMul gcl $ gcdModulo p f g           
        res' = reconstruct res h m p       -- SCC "reconstruct" 
        cres = divByCont res
      in
      case (deg h, compare (deg h) (deg res))
      of
      (0 , _ ) -> unityPol
      (_,  GT) -> lift res m ps     -- skip unlucky  p
      (_,  LT) -> lift h p ps       -- deg res must be smaller: 
                                    --                 start new base
      (dg, _ ) -> if  res' /= res  then  lift res' (m*p) ps 
                  else
                  if  dividesBoth cres  then  cres  else  findBase dg ps
          
-- Chinese Remainder Reconstruction.
-- For the mutualy prime A,B from Euclidean ring E, 
-- f,g  from (E/(A))[x], (E/(B))/[x], reconstruct  h  from  E[x],
-- with coefficients being canonical representatives in  E/(A*B).
-- f -> g -> A -> B -> h.
-- Each related coefficient pair  a,b  reconstructs to 
-- c = remEuc 'c' (a + (b-a)*u*A) (A*B)

reconstruct f g aA bB =  ct f $ rc (upolMons f) (upolMons g)
  where
  (d, u':_) = eucGCDE [aA, bB]     -- u',v:  u'*A + v*B = invertible
  u         = u'/d
  (uA, m')  = (u*aA, aA*bB)
  uACompl   = (unity u) - u*aA
  remCan x  = remEuc 'c' x m'

  rc []         g           = [(remCan (b*uA),      e) | (b,e) <- g]
  rc f          []          = [(remCan (a*uACompl), e) | (a,e) <- f]
  rc ((a,e): f) ((b,e'): g) = 
     case compare e e' 
     of
     EQ -> (remCan (a+uA*(b-a)), e ): (rc f g)   
     LT -> (remCan (b*uA),       e'): (rc ((a, e): f)  g)  -- a == 0
     _  -> (remCan (a*uACompl),  e ): (rc f ((b, e'): g))  -- b == 0
                     --
                     -- and zero coefficient cannot appear in result

                                                  -- ***
gcdModulo :: 
           (EuclideanRing a, FactorizationRing a, Ring (ResidueE a))
           =>
           a -> UPol a -> UPol a -> UPol a
                            -- project  f,g  to  (a/(p))[x],  find 
                            -- gcd there, return to  a[x]  by taking
gcdModulo p f g =           -- canonical representatives of residues

  -- SCC "gcdModulo"
  let un = unity p   
      pI = eucIdeal "" p [p] [un] [(p, 1)]
      r  = Rse un pI (upEucFactrRing p Map.empty)
      dR = upField r Map.empty
      pr = cToUPol "x" dR r
      toOverR h = ctr pr [(ctr r a, n) | (a, n) <- upolMons h] 
      mons      = upolMons $ upolGCDOverField (toOverR f) (toOverR g)
  in
  ct f [(resRepr a, n) | (a, n) <- mons] 





{- ?  new  ******************************************************
                                -- OI **
instance (Field a, EuclideanRing (UPol a), 
                   FactorizationRing (UPol a)
         ) =>                                GCDRing (UPol (UPol a))
  where
  -- gcd  specialization for the case  T[x], T = a[t],  `a' a field.
  -- The real optimization for  gcd  is expected for the case of a
  -- *finite* field  and is based on the Chinese-remainder method.
  -- In other case, the generic method applies.
  baseGCDRing f = gcdTerm_ (shows f "") (showsDomOf f "") f
  canInv f = ...
  canAssoc f = ...
  hasSquare = upolHasSquare   
  gcD []     = error "gcD []  :: UPol a\n"
  gcD (f:fs) =     let 
       z         = zeroS f ; (a,dA)    = (sample f, dom f)
       (dA', sA) = baseSet  a dA;    (dA'',rA) = baseRing a dA'
       (_,   rG) = baseGCDRing a dA'';  nonZeroes = filter (/= z) (f:fs)
    in  case  (and3 (isField rA) (isFiniteSet sA), isGCDRing rG) of
      (Yes, _  ) -> foldl upolGCD_Chinese z nonZeroes
      (_  , Yes) -> foldl upolGCD_generic z nonZeroes
      _          -> error $ ("gcD (f:fs),"++) $ showsWithDom f "f" "" 
                   "\n(IsGCDRing,Yes) needed for coefficient ring\n"
-}
