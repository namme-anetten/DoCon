------------------------------------------------------------------------
------------------------------------------------------------------------
--  The Algebraic Domain Constructor  DoCon,   version 2.12
--
--  Copyright  Serge Mechveliani,    2012
------------------------------------------------------------------------
------------------------------------------------------------------------





module Pol_   -- Various useful items for (multivariate) Polynomial.
              -- All needed from here is  reexported by  Pol.

              -- See first  UPol_*  - it is simpler.

  (Pol(..), PolPol,
   polMons, polPPOId, polPPComp, polPPOWeights, leastMon, cToPol, 
   reordPol, fromUPol, toUPol, monMul, mPolMul,
   monLcm, headVarPol, fromHeadVarPol, polToHomogForms, addVarsPol,
   coefsToPol, polDegs, polPermuteVars,
   neg_, add_, mul_, times_, sub_  -- local

   -- , instances for Pol:   Eq, Dom, Cast, PolLike
  )
where
import Data.List (genericDrop, genericSplitAt)
import Prelude hiding (maximum)

import DPrelude (Length(..), Cast(..), -- class
                 Natural, ct, ctr, allMaybes, sum1, product1, maximum, 
                 sortBy, partitionN, zipRem, cubeList_lex 
                )
import Categs   (Dom(..), Domains1)
import SetGroup (Set(..), AddSemigroup(..), MulSemigroup(..), 
                 AddGroup(..),  neg, zeroS, unity, isZero, times
                )
import RingModule (Ring(..), CommutativeRing(), GCDRing(..))
import Permut     (applyPermut                           )
import VecMatr    (Vector(..), vecRepr, vecHead, scalarMt)
import PP_        (PowerProduct, PPComp, ppLcm, lexComp  )

import UPol_ (PolLike(..), PPOrdTerm, PPOId, Mon, Multiindex,
              UPol(..), PolVar, ppoId,ppoComp,lexPPO,ppoWeights
             )
import qualified UPol_ (pmul)





------------------------------------------------------------------------
data Pol a = Pol [Mon a] a PPOrdTerm [PolVar] (Domains1 a)
--
-- (multivariate) polynomial.  See manual.


type PolPol a = Pol (Pol a) 

instance Dom Pol where  dom    (Pol _ _ _ _ d) = d
                        sample (Pol _ c _ _ _) = c

polMons       :: Pol a -> [Mon a]
polPPOId      :: Pol a -> PPOId 
polPPComp     :: Pol a -> PPComp
polPPOWeights :: Pol a -> [[Integer]]

polMons (Pol ms _  _  _  _ ) = ms

polPPOId      = ppoId      . pPPO
polPPComp     = ppoComp    . pPPO
polPPOWeights = ppoWeights . pPPO

iszero_ = null . polMons

leastMon :: Set a => Pol a -> Mon a
leastMon f =  
       case polMons f 
       of 
       m: ms -> last (m: ms)
       _     -> error $ concat ["\nleastMon 0  in  R", shows (pVars f)
                                ",\nR = ", showsDomOf 1 (sample f) "\n"]

instance Eq a => Eq (Pol a) where  f == g =  (polMons f) == (polMons g)

reordPol :: PPOrdTerm -> Pol a -> Pol a    -- bring to given pp ordering
reordPol ppo (Pol ms c _ vars dom) =  Pol (sortBy cmp ms) c ppo vars dom
                                      where 
                                      cmp (_, p) (_, q) = cp q p 
                                      cp                = ppoComp ppo
------------------------------------------------------------------------
instance AddGroup a => Cast (Pol a) (Mon a)
  where
  cast mode (Pol _ c o v d) (a, p) =  Pol mons c o v d
            where
            mons = if  mode == 'r' && isZero a  then []  else [(a, p)]
 
instance AddGroup a => Cast (Pol a) [Mon a] 
  where                                      
  cast mode (Pol _ c o v d) mons =  Pol ms c o v d  -- order NOT checked
       where                                          
       z  = zeroS c
       ms = if mode /= 'r' then  mons  else  filter ((/= z) . fst) mons

instance Ring a => Cast (Pol a) a
  where
  cast mode (Pol _ _ o vs d) a = 
                          case (mode, isZero a, Vec $ map (const 0) vs)
                          of  
                          ('r', True, _ ) -> Pol []        a o vs d
                          (_,   _   , pp) -> Pol [(a, pp)] a o vs d

{- wait Haskell-2 ****
instance Ring a => Cast (Pol a) PolVar   where
  cast _ (Pol _ a o _ d) vs = Pol [(unity a,...)] a o vs d
                                                  -- in new variables
- this overlaps with  Cast (Pol a) a    by  a = PolVar  !
-}


------------------------------------------------------------------------
instance PolLike Pol
  where  
  pIsConst f = case polMons f of (_, p): _ -> all (== 0) $ vecRepr p
                                 _         -> True
  pPPO  (Pol _  _  o  _  _ ) = o
  pVars (Pol _  _  _  vs _ ) = vs

  lm f = case polMons f of  
                  m: _ -> m
                  _    -> error $ concat 
                          ["\nlm 0  in  R,", shows (pVars f) ",\nR = ",
                                           showsDomOf 1 (sample f) "\n"]
  lpp f  = snd $ lm f
  pDeriv = deriv_
  pCoefs = map fst . polMons 

  pTail f = case polMons f  
            of 
            _: ms -> ct f ms 
            _     -> error $ concat 
                             ["\npTail 0  in  R", shows (pVars f) 
                              ",\nR = ", showsDomOf 1 (sample f) "\n"]

  pFreeCoef (Pol mons c _ _ _) = 
                   let {z = zeroS c;  (a, Vec js) = last mons}
                   in
                   if null mons then  z
                   else               if all (== 0) js then a else z
  pCoef f js = 
          let {p = Vec js;  cp = polPPComp f;  z = zeroS $ sample f}
          in
          case dropWhile ((== LT) . cp p . snd) $ polMons f 
          of 
          (a, q): _ -> if p == q then  a  else  z
          _         -> z

  ldeg f = case polMons f  
           of 
           (_, Vec js): _ -> sum1 js
           _              -> 
                error $ concat ["\nldeg 0  in  R", shows (pVars f)
                                ",\nR = ", showsDomOf 1 (sample f) "\n"]

  deg f = case  map (sum1 . vecRepr . snd) $ polMons f  
          of 
          d: ds -> maximum (d: ds)          
          _     -> error $ concat ["\ndeg 0  in  R", shows (pVars f)
                                ",\nR = ", showsDomOf 1 (sample f) "\n"]

  degInVar for0 i f = 
              (case (i >= 0, polMons f) 
               of
               (False, _ ) -> error $ msg "\n\nPositive i needed.\n"
               (_    , []) -> for0
               (_    , ms) -> maximum $ map (ith . vecRepr . snd) ms
              )
    where  
    ith js = case  genericDrop (pred i) js 
             of
             x: _ -> x
             _    -> error $ msg "\n\ni > numOfVars(f).\n"

    msg = showString "degInVar for0 i f,  \ni = " . shows i . 
          showString "\nf <-   " . showsDomOf 1 (sample f) . 
          shows (pVars f) 

  pCDiv f c = let (cs, pps) = unzip $ polMons f  
              in
              case  allMaybes [divide_m a c | a <- cs]
              of
              Just quots -> Just $ ct f $ zip quots pps
              _          -> Nothing

  pMapCoef mode f g =  cast mode g [(f a, pp) | (a, pp) <- polMons g]
  pMapPP f g =  ct g [(a, Vec $ f js) | (a, Vec js) <- polMons g]
  varPs a f = 
          [ct f (a, Vec js) | js <- scalarMt (pVars f) 1 (0 :: Integer)]
                                   -- because
                                   -- variable's power product is a row
                                   -- in the unity matrix of size |vars|
  pDivRem = divrem_
  pValue  = pvalue_
  pFromVec _ _ = error "\npFromVec (Pol ..) _:  it is not defined for\
                       \ multivariate polynomials.\n"
  pToVec _ _   = error "\npToVec _ (Pol ..):  it is not defined for\
                       \ multivariate polynomials.\n"


------------------------------------------------------------------------
divrem_ (Pol monsF c _ _ _) g =         -- LOCAL
  case
      (ctr g $ zeroS c, polMons g)
  of
  (_,       []) -> error $ concat ["\npDivRem f 0,\nin  ", 
                         showsDomOf 1 (sample g) $ shows (pVars g) "\n"]

  (zeroPol, (b, pp): msg') -> d monsF zeroPol                
    where
    d []                   q = (q, zeroPol)   
    d msf@((a, pp1): msf') q =                           
      let 
        dv@(Vec dpp) = pp1 - pp   
      in
      if  any (< 0) dpp  then  (q, ct g msf)
      else
      case  divide_m a b  
      of
      Nothing -> (q, ct g msf)
      Just e  -> let mon      = (e,dv)        
                     [f', g'] = [ct g ms | ms <- [msf', msg']]
                     msfNew   = polMons $ sub_ f' $ mPolMul mon g'
                 in  
                 d msfNew$ add_ q $ ct g mon

pvalue_ f cs =    -- Substitite values  ci <- a  to  f :: Pol a. 
  let             -- This method can be optimised via the Horner scheme.

    (z, mons)       = (zeroS $ sample f, polMons f) 
    (u, vars, csL)  = (unity z, pVars f, genLength cs)
    monValue (a, p) = 
              let (bs, es) = unzip $ filter ((/= u) . fst) $ 
                             filter ((/= 0) . snd) $ zip cs $ vecRepr p
              in
              if  any (== z) bs  then  z  
              else                     product1 (a: (zipWith (^) bs es))
  in
  if  csL < genLength vars  then
      error $ concat
      ["\npValue f values,\nf <-   ", showsDomOf 1 (sample f) $ 
       shows (pVars f) "\n(length values) = ", shows csL 
       "\n`values'  is shorter than the variable list.\n"]
  else
  sum1 (z: (map monValue mons))     

 
------------------------------------------------------------------------
fromUPol :: UPol a -> Pol a
fromUPol (UPol ms c v d) =  
                      Pol [(a, Vec [p])| (a, p)<- ms] c (lexPPO 1) [v] d
  -- conversion from 
  -- univariate polynomial means:  make a vector of size 1 from each 
  -- exponent, then set the variable list [v]  and  lexPPO ordering.

toUPol :: Ring a => Pol a -> UPol a
  -- To convert to univariate polynomial means to
  --   remove the pp-ordering term,  take the head variable only
  --   and the head of each power product, order the new monomials
  --   by degree,  sum up the monomials of repeating degree.

toUPol (Pol mons c _ vs dom) =  
  let
    cut (a, p)        = (a, vecHead p)
    cmp (_, x) (_, y) = compare y x
    (z, ms)           = (zeroS c, sortBy cmp $ map cut mons)
    sumup []           = []
    sumup ((a, p): ms) = let (ms', ms'') = span ((== p) . snd) ms
                             s           = sum1 (a: (map fst ms'))
                             rest        = sumup ms''
                         in  if s == z then rest  else  (s, p): rest
  in
  UPol (sumup ms) c (head vs) dom

------------------------------------------------------------------------
neg_ :: AddGroup a => Pol a -> Pol a                          -- f -> -f
neg_ f =  ct f [(neg a, pp) | (a, pp) <- polMons f]


add_, sub_ ::  AddGroup a => Pol a -> Pol a -> Pol a

add_ (Pol monsF c o _ _) g =  ct g $ pa monsF $ polMons g
  where
  (z, cp) = (zeroS c, ppoComp o)

  pa []       msG      = msG
  pa msF      []       = msF
  pa (m: msf) (n: msg) =
            let {(a,p) = m;  (b, q) = n;  d = add a b}
            in  
            case cp p q  
            of
            GT -> m: (pa msf (n: msg))  
            LT -> n: (pa (m: msf) msg)
            _  -> if d == z then  pa msf msg  else  (d, p): (pa msf msg)


sub_ f = add_ f . neg_


------------------------------------------------------------------------
monMul :: Ring a =>  a -> Mon a -> Mon a -> [Mon a]
                  -- zero

monMul z (a, p) (b, q) = let c = a*b in  if c == z then  []  
                                         else            [(c, p+q)]

mPolMul :: Ring a => Mon a -> Pol a -> Pol a
mPolMul              (a, p)   f     =  
                                 ctr f [(a*b, p+q)| (b, q) <- polMons f]

------------------------------------------------------------------------
times_ :: Ring a => (a -> i -> a) -> Pol a -> i -> Pol a
times_              t                f        n = 
                                 ctr f [(t a n, p)| (a, p) <- polMons f]
  -- t = `times' for `a'
------------------------------------------------------------------------
mul_ :: CommutativeRing a => Pol a -> Pol a -> Pol a
mul_                         f         g      = 
                      ct f $ UPol_.pmul zr cp id (polMons f) (polMons g)
                              where
                              {zr = zeroS $ sample f;  cp = polPPComp f}

------------------------------------------------------------------------
monLcm :: GCDRing a => Mon a -> Mon a -> Mon a
  --
  -- Lcm  of monomials over a  gcd-ring.
  -- For the *field* case, it is better not to call monLcm, but
  -- to set directly  (unity a, ppLcm ...)

monLcm (a, p) (b, q) = (a* (b/(gcD [a,b])), ppLcm p q) 


------------------------------------------------------------------------
-- Apply          cToPol ordTerm vars dom coef
--
-- to obtain the simplest (constant) polynomial from coefficient
-- (coef = zero  fits too).
-- dom :: Domains1 a   is the coefficient domain `a' description.
--
-- ATTENTION:
-- before applying   f = cToPol _ _ dom a  :: Pol a
-- 
-- supply  dom  with the sufficient set of descriptions.
-- The simplest way to do this is to apply  
--                     dom = up<C> a dom0,
--   <C>   being the strongest possible declared class for `a',
--   dom0  some initially known set of descriptions, say, Map.empty.
-- See the example below.
-- Without such  dom  preparation, the program may not recognise 
-- some natural properties of the domain of  f.


cToPol :: Ring a => PPOrdTerm -> [PolVar] -> Domains1 a -> a -> Pol a
cToPol              ord          vars        dom           a =
  if  
     a == zeroS a  then  Pol []       a ord vars dom
  else                   Pol [(a, p)] a ord vars dom
                         where
                         p = Vec $ map (const 0) vars
                         -- power product for  x1^0*..*xn^0,  xi<-vars
  -- Example.
  -- Create the unity polynomial  uT  of  PP = (Z[x,y])[t]
  -- with the degree-lexicographic ordering for [x,y];
  -- also create 0 and 2 of PP.
  --
  -- type P  = Pol Integer
  -- type PP = UPol P
  -- (uT,t0,t2) = let ord  = (("dlex",2),degLex,[])
  --                  uXY  = cToPol ord ["x","y"] dZ 1 :: P
  --                  domP = upGCDSyzRing uXY Map.emty :: Domains1 P
  --                  uT   = cToUPol "t" domP uXY      :: PP
  --              in
  --              (uT, fromi uT 0, fromi uT 2T)


------------------------------------------------------------------------
headVarPol ::
          CommutativeRing a => Domains1 (Pol a) -> Pol a -> UPol (Pol a)
                               -- pDom             f        g

-- Bring polynomial to head variable: a[x1,x2..xn]--> PP'= P'[x1],
-- P' = a[x2..xn],  n > 1.
-- This is ONLY for  lexComp  ordering on a[x1,x2..xn], a[x2..xn].
-- New  PPOId  on  a[x2..xn]  is  ("lex",n-1). 
-- pDom is the domain description for P'.
--
-- How to prepare  pDom ? 
-- Starting from the empty, it may be, say,  up<C> a Map.empty, 
-- with <C> the strongest declared class possible in environment.

headVarPol  pDom  f@(Pol mons c _ vars dom) = 
  (case 
       (genLength vars < 2, iszero_ f)  
   of
   (True, _    ) -> 
            error $ concat 
            ["\nheadVarPol pol'Dom f,\nf <- ", showsDomOf 1 (sample f) $ 
             shows (pVars f) "\n\nmore than one variable needed.\n"]
          
   (_,    True ) -> zero1P
   _             -> 
                   UPol (map lift $ partByPPhead mons) zeroTailP v1 pDom
  )
  where
  -- for this function script we call  tailPP, tailMon, tailP
  -- the power products, monomials, polynomials  in  [x2..xn];

  v1        = head vars
  tailVars  = tail vars
  n'        = pred $ genLength vars
  zr        = zeroS c
  weights'  = scalarMt tailVars 1 0
  ord'      = (("lex", n'), lexComp, weights')  

  zeroTailP = Pol [] zr        ord' tailVars dom     -- 0 of P'
  zero1P    = UPol [] zeroTailP v1 pDom              -- 0 of PP'

  lift (k, mons) = (Pol mons c ord' tailVars dom, k)  -- :: UMon P'
    --
    -- example:  (7, [x2,x3*x5^2]) -> x1^7 * (x2+x3*x5^2])

    -- Convert  mons  into groups (ki,mons_i), monomials with the 
    -- same  head(pp) = ki  go to one group.  mons_i  is a list of
    -- pairs  (c, ksi),  ksi  is the tail power product.
    --            
  partByPPhead []                       = []
  partByPPhead ((c, Vec (k: ks)): mons) = 
    let
      tailPPmon (c, Vec ns) = (c, Vec $ tail ns)
      (mons_k, mons')       = span ((== k) . vecHead . snd) mons
    in
    (k, (c, Vec ks): (map tailPPmon mons_k)): (partByPPhead mons')

------------------------------------------------------------------------
fromHeadVarPol :: UPol (Pol a) -> Pol a

  -- (a[x2,...,xn])[x1] -> a[x1,x2,...,xn],    n > 1.
  -- Inverse to  headVarPol.   For the  lexComp  ordering ONLY.
  -- New PPOId is  ("lex",n).

fromHeadVarPol (UPol mons cf v _) = 
  case cf
  of
  Pol _ a _ vars dom ->
                   Pol (concat $ map extendMonsOf_k mons) a o vars' dom
    where
    vars'   = v: vars
    o       = (("lex", genLength vars'), lexComp, weights)  
    weights = scalarMt vars' 1 0
    extendMonsOf_k (g, k) = [(c, Vec (k:ks)) | (c, Vec ks) <- polMons g]

------------------------------------------------------------------------
polToHomogForms ::
           (AddGroup a, Eq b) => (PowerProduct -> b) -> Pol a -> [Pol a]
                                 -- weight                
polToHomogForms w f = 
              map (ct f) $ 
              partitionN (\ (_, p) (_, q) -> (w p) == (w q)) $ polMons f
           --
           -- (non-ordered) list of homogeneous forms of polynomial over 
           -- `a'  with respect to the  weight :: PowerProduct -> b

------------------------------------------------------------------------
addVarsPol :: Char -> PPOrdTerm -> [PolVar] -> Pol a -> Pol a

-- Embed  a[x1..xn]  to  a[y1..ym x1..xn]  or to  a[x1..xn y1..ym] 
-- by prepending/appending the variable list  vars' = [y1..ym]  
-- to  vars  and extending exponents with zeroes.
-- CAUTION:
-- the new pp-order term  ord' is required which must *agree* with the 
-- old one:   (cp' restricted to y1=..=ym=0) == cp,
-- and the weights must agree too.
-- mode = 'h'        means prepending of vars' to head of vars,
--        any other  -     appending

addVarsPol mode ord' vars' (Pol mons c _ vars dom) =  
                     Pol (zip cs exps') c ord' (prepApp vars' vars) dom
       where
       zeroes        = map (const 0) vars'
       (cs, exps)    = unzip mons
       prepApp xs ys = if  mode == 'h' then  xs ++ ys  else  ys ++ xs
       exps'         = [Vec $ prepApp zeroes js | (Vec js) <- exps]


------------------------------------------------------------------------
deriv_ :: CommutativeRing a => Multiindex Integer -> Pol a -> Pol a
-- LOCAL.
-- Derivative of polynomial from  a[x1..xn]  w.r.to  multiindex 
-- [(v_1, i_1) ... (v_k, i_k)],    1 <= v_1 < v_2 .. <= n:
-- differentiate  i_m  times  by the variable No j_m.
-- Method:  apply  d/d_mIndex  monomial-wise.

deriv_ mIndex f =  ctr f $ map (monDeriv mIndex) $ polMons f
  where
  zr = zeroS $ sample f

  monDeriv []            mon         =  mon
  monDeriv ((v, m): ind) (a, Vec js) =  
     case 
         (a == zr, m) 
     of               -- this can be optimized using that vi are ordered
     (True, _) -> (zr, Vec [])
     (_,    0) -> monDeriv ind (a, Vec js)
     _         ->
        case genericSplitAt (pred v) js
        of
        (_,   []     ) ->
           error $ concat ["\npDeriv ", shows mIndex$ " f,\nf <- ", 
                           showsDomOf 1 (sample f) $ shows (pVars f)
                           "\n\nToo large variable No in multiindex.\n"]
        (js', j: js'') -> if  j < m  then  (zr, Vec [])
                          else       
                          monDeriv ind (b, Vec (js' ++ ((j-m): js'')))
                                   where 
                                   b = times a $ product [(j-m+1) .. j]


------------------------------------------------------------------------
coefsToPol :: Ring a => Char-> Pol a-> [Integer]-> [a]-> (Pol a, [a])
                     -- mode   sample  degs        cs 
-- Convert the coefficient list to polynomial of given sample.
-- Coefficients zip with the power products from the cube
-- [[k(1)..k(n)] | 0 <= k(i) <= d(i),  d(i) <- degs]  - 
-- listed in the lexComp order. 
-- Then the zero coefficient monomials are filtered out.
-- mode = 'l'  means the sample is under lexComp,  
--             in this case the final re-ordering is skipped.

coefsToPol mode smp degs cs =
  let
    (vars, o, degsL) = (pVars smp, pPPO smp, genLength degs)
    pps = reverse $ map Vec $ cubeList_lex [(0, d) | d <- degs]

    (ms, csRest, ppRest) = zipRem cs pps
    f                   = ctr smp ms
    f'                  = if  mode == 'l' then f  else  reordPol o f

    msg = showString ("\ncoefsToPol " ++ 
                      (mode: " samplePol degs coefs,\nin  ")) . 
          showsDomOf 1 (sample smp) . shows vars . 
          showString "\ndegs = " . msgD . showString "\ncoefs = " . 
          msgC . showString "\nlength degs = " . shows degsL    

    msgD = case degs of  d: _ -> shows d . showString " ..." 
                         _    -> showString "[]"
    msgC = case cs   of  c: _ -> shows c . showString " ..."
                         _    -> showString "[]"
  in
  case (zipRem degs vars, ppRest)
  of 
  ((_, [], []), []) -> (f', csRest)
  (_,           []) -> error $ msg "\n\ndegs  must correspond \
                                   \bijectively to variables.\n"
  _                 -> error $ msg "\n\nNot enough of  coefs.\n"

------------------------------------------------------------------------
polDegs :: [Integer] -> Pol a -> [Integer]

-- Degrees in each variable.  Returns  zdegs  for zero  f.
-- Example:
-- for f = x^2*z + x*z^4 + 1 <- Z[x,y,z],   polDegs [] f = [2,0,4]

polDegs zdegs f = case  map (vecRepr . snd) $ polMons f  
                  of
                  []      -> zdegs
                  js: jss -> foldl (zipWith max) js jss


polPermuteVars :: AddGroup a => [Natural] -> Pol a -> Pol a
              -- Substitution for polynomial variables [x1..xn]
              -- given by permutation at [1..n].
              -- Monomial list reorderes, but the variable list remains.
polPermuteVars js f =
                let (o, mons) = (pPPO f, polMons f)
                in  reordPol o $ ct f 
                    [(b, Vec $ applyPermut js ks) | (b, Vec ks) <- mons]





{- reserve  *****************************************************
--R[x1,x2,...,xn] -> (R[x1])[x2,...,xn,   n > 1,  cp = lexComp.
liftPolCoef :: (CommutativeRing a) => Pol a -> Pol (Pol a)
-- the comparison  cp' for [x2..xn]  is chosen so that
--   cp' ns ms = cp (0:ns) (0:ms)  for the comparison cp for [x1..xn].
liftPolCoef  f@(Pol mons c cp vars) = 
  if(genLength vars) < 2  then
        error "(liftPolCoef f):  more than one variable needed \n"
  else  let   cp' (Vec ns) (Vec ms) =  cp (Vec (0:ns)) (Vec (0:ms))
          v1 = head vars;   varTail = tail vars
    in   Pol  (map lift (partByPPTails mons))  
                                 (cToPol c lexComp v1) cp' varTail
      where lift  (ks,mons) =  ( Pol mons c lexComp [v1],  Vec ks )
             -- Convert  mons  into groups (ksi,mons_i), monomials
             -- with the same  tail(pp) = ksi  go to one group. 
          -- The order inside  mons_i  is the same as it was in mons.
             -- Each mons_i  is a list of pairs  (c,ks1),  ks1  is
             -- the power "in x1".
      partByPPTails  mons =  partT (map breakPP mons)
      breakPP (c, (Vec (k:ks))) =  (c,k,ks)
      partT  [(c,k1,ks)]      = [ (ks, [(c,k1)]) ]
      partT  ((c,k1,ks):mons) = (ks, (c,k1):(pt mons)) : (partT mons)
        where  pt []               =  []
        pt ((c,k1',ks'):ms) = if ks'==ks then  (c, Vec [k1']): (pt ms)
                              else               pt ms
                 -- convert mons_i group into monomial over  a[x1]
--  for  Pol (a,b)  -------
toPairOfPol :: (AddMonoid a, AddMonoid b) => 
                                        Pol (a,b) -> (Pol a,Pol b)
toPairOfPol  (Pol []  ) =  (Pol [], Pol [])
toPairOfPol  (Pol mons) =  let  (a,b) = lc (Pol mons)
    za    = zeroS a;    zb    = zeroS b
  in  pcp  za zb mons      where
        pcp _  _  []            =  (Pol [], Pol [])
        pcp za zb (((a,b),p):f) =  
          let  (Pol ms1, Pol ms2) = pcp za zb f  
            (ms1',ms2')        =  case  (a==za,b==zb)  of 
                        (True ,True ) ->  ( ms1      , ms2       )
                        (False,True ) ->  ( (a,p):ms1, ms2       )
                        (True ,False) ->  ( ms1      , (b,p):ms2 )
                        _             ->  ( (a,p):ms1, (b,p):ms2 )
          in (Pol ms1', Pol ms2')
********************************************************************
-}
