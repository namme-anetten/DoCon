------------------------------------------------------------------------
------------------------------------------------------------------------
--  The Algebraic Domain Constructor  DoCon,   version 2.12
--
--  Copyright  Serge Mechveliani,    2012
------------------------------------------------------------------------
------------------------------------------------------------------------




module RPol_   -- "Recursively" represented polynomials - r-polynomials.
               -- See Manual.
               -- All needed from here is  reexported by  Pol.

(RPol(..), RPol'(..), RPolVarComp, RPolVarsTerm, rpolRepr, rpolVComp, 
 rpolVTerm, rpolVPrefix, rpolVRanges, rvarsTermCp, rvarsTermPref, 
 rvarsTermRanges, rvarsVolum, showsRVarsTerm, rvarsOfRanges, rp'HeadVar, 
 rpolHeadVar, rp'Vars, rpolVars, cToRPol, varToRPol', varToRPol, 
 rHeadVarPol, rFromHeadVarPol, toRPol, toRPol', fromRPol, 
 substValsInRPol, rpol'ToSPPol', 
 add_, mul_ 
 -- , instances for RPol', RPol:  
 --                 Eq, Show, DShow, Functor, Dom, Cast, PolLike
)
where
import qualified Data.Map as Map (empty)

import Data.List (delete, union, genericIndex, genericReplicate)

import DPrelude (Length(..), DShow(..), Cast(..), -- classes
                 Comparison, Verbosity,  isOrderedBy, ct, sortBy, 
                                      tuple31, tuple32, tuple33, showsn)
import Categs   (Dom(..), Domains1)
import SetGroup (Set(..), AddSemigroup(..), MulSemigroup(..),
                 AddGroup(..),  zeroS, unity, neg
                )
import RingModule (Ring(..), CommutativeRing(), isOrderedRing)
import VecMatr    (Vector(..)                                )
import UPol_ (PolLike(..), UPol(..), PPOrdTerm, upolMons, cPMul, lexPPO)
import Pol_  (Pol(..), polMons, reordPol, headVarPol, cToPol)
import Pol__ (RPolVar, showsRPolVar, SPPol', showsSPPol'    )
import Pol1_ ()






------------------------------------------------------------------------
type RPolVarComp  = Comparison RPolVar
type RPolVarsTerm = (RPolVarComp, String, [(Integer, Integer)])

  -- (vcp, pref, ranges)  
  -- presents the variable ordering  vcp  and the variable set
  -- description for  [pref[i1..in] | ...] 
  --
  -- pref                is the prefix to print variable,
  -- ranges = [(l1,h1)..(ln,hn)] 
  --                        contains the range (lk,hk) for each 
  --                        variable index component:  lk <= ik <= hk

rvarsTermCp :: RPolVarsTerm -> RPolVarComp
rvarsTermCp =  tuple31

rvarsTermPref :: RPolVarsTerm -> String
rvarsTermPref =  tuple32

rvarsTermRanges :: RPolVarsTerm -> [(Integer, Integer)]
rvarsTermRanges =  tuple33

showsRVarsTerm :: Verbosity -> RPolVarsTerm -> String -> String 
showsRVarsTerm verb (_, pref, rgs) = 
                                   showString ("(<rpolComp>," ++ pref) .
                                   showsn verb rgs . showChar ')'

------------------------------------------------------------------------
data RPol a = RPol (RPol' a) a RPolVarsTerm (Domains1 a)

-- In  f =  RPol rpol' a vterm aDom,
-- a                      is the sample coefficient,
-- vterm = (cp,pref,rgs)  variable comparison and full variable
--                        set description,
-- aDom                   domain description for `a',
-- rpol' :: RPol' a       very representation.
--    
-- f  is viewed as the element of a[XX]
--                     XX = [pref(ind)| ind <- set_defined_by_rgs],
--
-- set_defined_by_rgs = [[i1..in] |  for each k ik<-[lk..hk]].


data RPol' a =  CRP a                                  -- constant r-pol
              | NRP RPolVar Integer (RPol' a) (RPol' a)  -- non-constant
              deriving (Eq, Show, Read)

-- CRP a            means Constant R-polynomial,
-- NRP v n cf tl    (Non-constant R-polynomial)
--   means  cf*v^n + tl, 
--          n > 0,   
--          0 /= cf ::RPol' a,  variables in cf are smaller than v,
--         tl :: RPol' a,       variables in tl are not greater than v,
--                              deg v tl < n.
-- See the example in Manual.


rpolRepr :: RPol a -> RPol' a
rpolRepr (RPol f _ _ _) = f

rpolVTerm :: RPol a -> RPolVarsTerm
rpolVTerm (RPol _ _ t _) = t

rpolVComp :: RPol a -> RPolVarComp
rpolVComp =  rvarsTermCp . rpolVTerm

rpolVPrefix :: RPol a -> String 
rpolVPrefix = rvarsTermPref . rpolVTerm

rpolVRanges :: RPol a -> [(Integer, Integer)]
rpolVRanges = rvarsTermRanges . rpolVTerm

rp'HeadVar :: RPol' a -> Maybe RPolVar
rp'HeadVar (NRP v _ _ _) = Just v
rp'HeadVar _             = Nothing

rpolHeadVar :: RPol a -> Maybe RPolVar
rpolHeadVar = rp'HeadVar . rpolRepr


------------------------------------------------------------------------
-- rp'Vars f, rpolVars f
-- yield only the variables v(i,j) on which f really depends.


rp'Vars :: Char -> RPol' a -> [RPolVar]
  --       mode    f
  --
  -- List variables, first - into depth, then to the right, 
  -- repetitions cancelled.
  -- mode = 'l'   means f is linear, in this case the computation is
  --              cheaper.

rp'Vars mode = vr  
  where  
  vr (CRP _)       = []
  vr (NRP v _ c t) = let {tvars = vr t;  cvars = vr c} 
                     in
                     if  mode == 'l'  then  v:tvars
                     else             v: (union cvars $ delete v tvars)


rpolVars :: Char -> RPol a -> [RPolVar]          
  --        mode    f   
  -- The result is ordered by comparison from f.
  -- mode = 'l'  means f is linear - in this case the computation is 
  --                                                            cheaper.
rpolVars mode (RPol f _ t _) =  
                          let {vs = rp'Vars mode f;  cp = rvarsTermCp t}
                          in
                          if  mode == 'o'  then  sortBy (flip cp) vs
                          else                   vs
   
------------------------------------------------------------------------
instance Dom RPol' 
  where  
  sample = sm   where  sm (CRP a)       = a
                       sm (NRP _ _ c _) = sm c

  dom f = let  vars = rp'Vars '_' f 
          in
          error $ ("dom  f@(RPol'..),"++) $
                  ("\nf  depends on the variables  "++) $ shows vars
                  "\n\ndom  is not defined for  (RPol' a) \n"


instance Dom RPol where sample (RPol _ a _ _) =  a
                        dom    (RPol _ _ _ d) =  d

instance Cast (RPol a) (RPol' a) 
  where
  cast _ (RPol _ c t d) f =  RPol f c t d

instance Cast (RPol' a) a  where  cast _ _ a = CRP a

instance Cast (RPol a) a  where 
                          cast _ (RPol _ c t d) a = RPol (CRP a) c t d


{- wait language extension to resolve overlap with Cast (RPol a) a
instance Cast (RPol a) RPolVar   where 
  cast _ (RPol _ c t d) v = case  (CRP $ zeroS c, CRP $ unity c)  
                            of(z,u) -> RPol (NRP v 1 u z) c t d
-}

------------------------------------------------------------------------
rvarsVolum :: [(Integer, Integer)] -> Integer
rvarsVolum []     =  error "rvarsVolum []\n"
rvarsVolum ranges =  product [h-l+1 | (l, h) <- ranges]

------------------------------------------------------------------------
rvarsOfRanges :: [(Integer, Integer)] -> [RPolVar]
  -- All r-vars in the given ranges listed in the 
  -- lexicographic-increasing order.
  -- EXAMPLE: 
  -- rvarsOfRanges [(0,2),(3,4)] = 
  --                           [[0,3],[0,4],[1,3],[1,4],[2,3],[2,4]]
  -- CAUTION:  you see, it may be very expensive.

rvarsOfRanges = inds
  where   
  inds []           = [[]]
  inds ((l, h): rs) = 
       if  l > h  then  
           error $ concat
           ["\nrvarsOfRanges ranges,\nranges = ", shows ((l, h): rs) 
            "\n:\nthe pair with  lower > higher  occurred in  ranges.\n"
           ]
       else  concat [map (j :) $ inds rs | j <- [l .. h]] 

------------------------------------------------------------------------
instance PolLike RPol'
  where
  pIsConst (CRP _) = True
  pIsConst _       = False

  pCoefs f = pc f []  where  pc (CRP a)         = (a:)
                             pc (NRP _ _ cf tl) = pc cf .pc tl
                             -- coefficients listed "first in depth"
  pTail (CRP a)       = CRP a
  pTail (NRP _ _ _ t) = t

  pFreeCoef (CRP a)        = a
  pFreeCoef (NRP _ _ _ tl) = pFreeCoef tl

  ldeg (CRP _      ) = 0                  -- deg in leading variable
  ldeg (NRP _ n _ _) = n                  

  deg = dg  where  dg (CRP _)       = 0                   -- sum of degs
                   dg (NRP _ n c t) = max (n+(dg c)) (dg t)

  degInVar _ n f = dg f
    where
    v                =  genericIndex (rp'Vars '_' f) (n-1) 
    dg (CRP _)       =  0
    dg (NRP u n c t) =  if  u == v then n  else  max (dg c) (dg t)

  pCDiv f a = dv f
    where
    dv (CRP b)       = fmap CRP $ divide_m b a
    dv (NRP v n c t) = case (dv c, dv t)  
                       of
                       (Just c', Just t') -> Just $ NRP v n c' t'
                       _                  -> Nothing

  varPs a f = [NRP v 1 (CRP a) $ CRP $ zeroS a | v <- rp'Vars '_' f]

  pMapCoef mode f g  | mode /= 'r'  = fmap f g
                     | otherwise    = m g
    where
    z = zeroS $ head $ pCoefs g
    m (CRP a)       = CRP $ f a
    m (NRP v n c t) = case m c
                      of
                      CRP b -> if b == z then  m t
                               else            NRP v n (CRP b) (m t)
                      c'    -> NRP v n c' (m t)

  pMapPP f = m  where
                m (CRP a)       = CRP a
                m (NRP v n c t) = NRP v (head $ f [n]) (m c) (m t)
                  -- CAUTION:
                  -- applying bad f may yield incorrect r-polynomial

  lpp     _   = error "\nlpp  for (RPol' _)  is not defined, so far.\n" 
  lm      _   = error "\nlm  for (RPol' _)  is not defined, so far.\n" 
  pCoef   _ _ = error "\npCoef _ _  for (RPol' _)  is not defined.\n" 
  pVars   _   = error "\npVars  for (RPol' _)  is not defined.\n" 
  pPPO    _   = error "\npPPO  for (RPol' _)  is not defined.\n" 
  pValue  _ _ = error 
                  "\npValue  for (RPol' _)  is not defined, so far.\n" 
  pDeriv  _ _ = error 
                    "\npDeriv  for (RPol' _)  is not defined, so far.\n" 
  pDivRem _ _ = 
             error "\npDivRem  for (RPol' _)  is not defined, so far.\n" 
  pFromVec _ _ = 
            error "\npFromVec  for (RPol' _)  is not defined, so far.\n" 
  pToVec _ _ = 
              error "\npToVec  for (RPol' _)  is not defined, so far.\n"

------------------------------------------------------------------------
instance Eq a => Eq (RPol a) where  f == g =  (rpolRepr f == rpolRepr g)

instance Functor RPol' 
  where  
  fmap f (CRP a)       = CRP (f a)
  fmap f (NRP v n c t) = NRP v n (fmap f c) (fmap f t)
    --
    -- When this  map f :: RPol a -> RPol b 
    -- yields the correct polynomial?
    -- When  f c  is non-zero for all the coefficient r-pols  c
    -- in the given r-pol g.


------------------------------------------------------------------------
instance PolLike RPol
  where  
  pIsConst  = pIsConst  . rpolRepr
  ldeg      = ldeg      . rpolRepr  
  deg       = deg       . rpolRepr
  pCoefs    = pCoefs    . rpolRepr
  pFreeCoef = pFreeCoef . rpolRepr
  pTail f   = ct f $ pTail $ rpolRepr f
  pCDiv f   = fmap (ct f) . pCDiv (rpolRepr f)

  degInVar for0 i =  degInVar for0 i . rpolRepr

  varPs  a  f@(RPol g _ t _) =  
                     let cp                              = rvarsTermCp t
                         cp' (NRP u _ _ _) (NRP v _ _ _) = cp u v
                     in  map (ct f) $ sortBy (flip cp') $ varPs a g

  pDivRem (RPol f a t _) g = (ct g q, ct g r)
               where
               (q, r) = divrem_ (zeroS a) (rvarsTermCp t) f $ rpolRepr g

  pMapCoef mode f g = ct g $ pMapCoef mode f $ rpolRepr g
  pMapPP f g        = ct g $ pMapPP f        $ rpolRepr g

  lpp _ = error "\nlpp (RPol ..):  is not defined, so far.\n" 
  lm  _ = error "\nlm (RPol ..):  is not defined, so far.\n" 
  pCoef _ _ = error "\npCoef (RPol ..) _:  is not defined, so far.\n" 
  pVars _ = error "\npVars (RPol ..):  is not defined.\n" 
  pPPO _ = error "\npPPO (RPol ..):  is not defined.\n" 
  pValue _ _ = error "\npValue (RPol ..) _:  is not defined, so far.\n" 
  pDeriv _ _ = error "\npDeriv _ (RPol ..):  is not defined, so far.\n" 
  pFromVec _ _ = error "\npFromVec (RPol ..) _:  is not defined.\n" 
  pToVec _ _ = error "\npToVec _ (RPol ..):  is not defined.\n" 


------------------------------------------------------------------------
cToRPol :: RPolVarsTerm -> Domains1 a -> a -> RPol a
cToRPol    t               dm            a =  RPol (CRP a) a t dm
    
varToRPol' :: AddSemigroup a => a -> RPolVar -> RPol' a
varToRPol'                      a    v = NRP v 1 (CRP a) $ CRP $ zeroS a

varToRPol :: AddSemigroup a => RPol a -> a -> RPolVar -> RPol a
                            -- sample
varToRPol f a v = ct f $ varToRPol' a v

------------------------------------------------------------------------
add_ :: 
    AddSemigroup a =>  a -> RPolVarComp -> RPol' a -> RPol' a -> RPol' a 
                    -- zero
add_ z cp f g = ad f g                 -- LOCAL.   Sum of r'-polynomials
  where
  ad (CRP a)         (CRP b)             = CRP $ add a b
  ad (NRP v n c t)   (CRP a)             = NRP v n c $ ad t $ CRP a
  ad (CRP a)         (NRP v n c t)       = NRP v n c $ ad t $ CRP a
  ad f@(NRP v n c t) g@(NRP v' n' c' t') =
    let
       {c1 = ad c c';  t1 = ad t t'}
    in
    case (cp v v', compare n n')
    of
    (GT, _ ) -> NRP v  n  c  $ ad t  g
    (LT, _ ) -> NRP v' n' c' $ ad t' f
    (_ , GT) -> NRP v  n  c  $ ad t  g
    (_ , LT) -> NRP v' n' c' $ ad t' f
    _        -> if c1 == CRP z  then  t1  else  NRP v n c1 t1

mul_ :: 
 CommutativeRing a =>  a -> RPolVarComp -> RPol' a -> RPol' a -> RPol' a
                    -- zero
mul_ z cp f g = mu f g          -- LOCAL.  Product of r'-polynomials
  where
  isZP (CRP a) =  a == z     -- "is zero RPol'"
  isZP _       =  False

  mu  (CRP a)         f                 = cPMul a f
  mu  f               (CRP a)           = cPMul a f
  mu  f@(NRP u n c t) g@(NRP v m c' t') =  
    let
       {cc = mu c c';  ft' = mu f t';  tg = mu t g}
    in
    case cp u v
    of
    GT -> let            -- g is coefficient-like respectively to u
              gc = mu g c    
          in  if  isZP gc  then  tg  else  NRP u n gc tg

    LT -> let  fc = mu f c'  in  if  isZP fc  then  ft'  
                                 else               NRP v m fc ft'
    _  -> let
                            -- for  f = u^n*c + t  and  g = u^m*c' + t',
                            --  f*g =  c*c'*u^(n+m)  + t*g  + c*u^n*t'
              uct' = mu (NRP u n c $ CRP z) t'
              tt   = add_ z cp tg uct'
          in  if  isZP cc  then  tt  else  NRP u (n+m) cc tt 

------------------------------------------------------------------------
divrem_ :: CommutativeRing a =>  
           a -> RPolVarComp -> RPol' a -> RPol' a -> (RPol' a, RPol' a) 
        -- zero cp             f          g           q        r

divrem_ z cp f g =  dv f g       -- LOCAL.  See pDivRem of class PolLike
  where
  (addp, mulp) = (add_ z cp, mul_ z cp)     -- +,*,-  for RPol'
  subp f g     = add_ z cp f $ fmap neg g   --
  zP           = CRP z                      -- zero RPol'
  isZP (CRP a) = a == z                     -- isZeroRPol'
  isZP _       = False

  dv  f                 (CRP b)             = divByC f b
  dv  (CRP a)           _                   = (zP, CRP a)
  dv  f@(NRP u n cf tl) g@(NRP v m cf' tl') = 
    let
      {(q, r) = dv cf g;  (q', r') = dv tl g;  (qc, rc) = dv cf cf';
        d     = n - m
      }
    in
    case (cp u v, compare n m)
    of
    (LT, _ ) -> (zP, f)
    (GT, _ ) ->                         -- f = u^n*cf + tl,  cf= q*g + r
                                        -- f - q*u^n*g = r*u^n  + tl
                if  isZP r  then (addp q' $ NRP u n q zP, r')
                else             (zP,                     f )

    (_ , LT) -> (zP, f)
    _        ->               -- f            = u^n*cf  + tl
                              -- g            = u^m*cf' + tl'
                              -- d            = n-m
                              -- cf           = qc*cf' + rc
                              -- f - qc*u^d*g = rc*u^n + tl - qc*u^d*tl'
       if  not $ isZP rc  then  (zP, f)
       else
       let qcu      = if d == 0 then  qc  else  NRP u d qc zP  -- qc*u^d
           (q1, r1) = dv (subp tl $ mulp qcu tl') g 
       in  (addp q1 qcu, r1)
             

  divByC f b =  if b == z then (zP, f) else  byC f 
    where
    byC  (CRP a) = case divide_m a b of Just q -> (CRP q, zP   )
                                        _      -> (zP,    CRP a)

    byC  f@(NRP v n cf tl) = 
                       let {(q, r) = byC cf;  (q', r') = byC tl}
                       in
                       if  isZP r  then  (addp q' $ NRP v n q zP, r')
                       else              (zP,                     f )

-----------------------------------------------------------------------
-- showsdomRPol_, showsRPolInfo_    are needed only for THIS module;
-- in further modules,   ..Set (RPol..)   suffices.

showsdomRPol_ :: Set a => Verbosity -> RPol a -> String -> String  
showsdomRPol_             verb         (RPol _ a t _) = 
  let
     {pref = rvarsTermPref t;  rgs = rvarsTermRanges t}
  in 
  showsDomOf verb a . showChar '[' . showString pref . showChar ' ' . 
  shows rgs

showsRPolInfo_ :: 
              Set a => Verbosity -> RPol a -> String -> String -> String
showsRPolInfo_         verb         f         fname =  

  showString (fname ++ " <-  ") . showsdomRPol_ verb f .
  showString ",\nfirst several variables:    " .  showsn verb vars . 
  showString ",\nfirst several coefficients:  " . showsn verb cs
  where
  vars = case  rp'Vars '_' $ rpolRepr f  of  u: v: w:_ -> [u, v, w]
                                             vs        -> vs
  cs = case pCoefs f of  a: b: c: _ -> [a, b, c]
                         cfs        -> cfs

-----------------------------------------------------------------------
rHeadVarPol :: Set a => Domains1 (RPol a) -> RPol a -> UPol (RPol a)
                        -- rdom              r         rU
  -- Convert non-constant r-polynomial  r  from  R  to
  -- univariate polynomial of R[u],  u  the leading variable of r.
  --
  -- CAUTION: coefficients of rU have the same variable set as  r.
  --
  -- rdom  can be set before, for example, via  up..Ring.

rHeadVarPol  rdom  r@(RPol f c t aDom) =  
  case (f, t) 
  of  
  (CRP a,         _         ) -> 
           error $ ("\nrHeadVarPol  rdom  r@(RPol..) :"++) $ 
                   ("\n\nConstant  r =  "++) $ shows a $ ("\n <-  "++) $
                   showsdomRPol_ 1 r "\n"

  (NRP u n cf tl, (_, pref, _)) ->
                                 UPol ((toR cf, n): (toH tl)) r var rdom
    where
    toR x = RPol x c t aDom
    var   = showsRPolVar pref u ""

    toH  (CRP a)             = [(toR (CRP a), 0)]
    toH  g@(NRP v m cf' tl') = if  v == u  then  (toR cf', m): (toH tl')
                               else              [(toR g, 0)]

------------------------------------------------------------------------
rFromHeadVarPol :: AddSemigroup a => RPolVar -> UPol (RPol a) -> RPol a
                                     -- v     
  -- Inverse to  rHeadVarPol.
  -- The leading variable is given in argument - in order not to 
  -- convert it from string nor search in ranges.

rFromHeadVarPol v (UPol mons r _ _) = ct r $ fromH mons
                where
                fromH []           = CRP$ zeroS $ sample r
                fromH ((b, n): ms) = case (n == 0, rpolRepr b)
                                     of
                                     (True, b') -> b'  
                                     (_,    b') -> NRP v n b' $ fromH ms

------------------------------------------------------------------------
fromRPol :: CommutativeRing a => PPOrdTerm -> RPol a -> Pol a
                                 -- ord       rf
  -- Convert  r-polynomial  rf  to polynomial  f,
  -- f is under the given pp ordering  ord.
  -- The variable set for f is described by  rpolVTerm rf:
  --
  -- vars = [prefix_i1'_.._in'| [i1..in] in ranges],  ik' = show ik.
  --
  -- The order in  vars  is put so that last index in [i1..in] 
  -- changes first.
  -- EXAMPLE: 
  -- if  rpolVTerm rf = (_, "u", [(0,2),(0,1)]),  then
  --
  -- fromRPol rf   yields f with the variable list
  --               ["u_0_0","u_0_1","u_1_0","u_1_1","u_2_0","u_2_1"].
  --
  -- CAUTION with efficiency:  
  -- you see, the variable index expansion to the (dense) power 
  -- product may be very expensive.

fromRPol  ord  f@(RPol f' a t dm) = 
  let
    msg = showString "\nfromRPol  ord  f@(RPol..),\n" . 
                                                  showsRPolInfo_ 1 f "f"
    wrongIndexMessg   = "\n\nr-variable index out of range.\n"
    un                = unity a
    (_, pref, ranges) = t
                                  -- target variable list  vars  is made 
                                  -- of all the indices under the ranges
    numOfInds = rvarsVolum ranges
    inds      = rvarsOfRanges ranges  
    vars      = [showsRPolVar pref ind "" | ind <- inds]
    --------------------------------------------------------------------
    -- Convert  n, index  to power product [0,..,0,n,0,..,0] 
    -- according to ranges.  These  n,index  come from  rf.

    toPP n js = let p = position js ranges
                in  
                (genericReplicate (p-1) 0) ++
                (n: (genericReplicate (numOfInds-p) 0))
      where
      position [j]    [(l, h)]        = 
                  if  j < l || j > h  then  error $ msg wrongIndexMessg
                  else                      j-l+1

      position (j: js)  rs@((l,h): rs') = 
               if            
                 j < l || j > h  then  error $ msg wrongIndexMessg
               else 
               let {p' = position js rs';  hs = map snd rs'}
               in
               if j == l then  p'  else  p'+(position ((j-1):hs) rs)

      position _      _              =
                           error $ msg "\n\nEach r-var index must be of\
                                       \ the same length as  ranges.\n"
    --------------------------------------------------------------------
    fromR (CRP a)        = cToPol ord vars dm a
    fromR (NRP v n c tl) = 
               let {c' = fromR c;  tl' = fromR tl;  pp = Vec $ toPP n v}
               in
               c'*(Pol [(un, pp)] a ord vars dm) + tl'
  in
  fromR f'


------------------------------------------------------------------------
toRPol' :: CommutativeRing a =>  Char -> [RPolVar] -> Pol a -> RPol' a
                              -- mode    rvars        f

  -- Convert polynomial  f <- a[x1..xn]  to  r-pol'  rf  
  -- respectively to the given bijective variable correspondence 
  -- rvars = [v1..vn] <--> [x1..xn] = pVars f
  -- - the variable order is preserved.
  --
  -- mode = 'l'           means the pp order in  f  is lexComp, in
  --                      this case the computation is more direct,
  --        other letter  will cost the initial reordering of f.

toRPol' mode rvars f@(Pol _ a _ vars _) =   
  (if  
      mode == 'l' then  toR rvars f
   else                 toR rvars $ reordPol (lexPPO n) f
  )
  where                      
  zr       = zeroS a
  n        = genLength vars
  toR vs f =                            -- here f is under lexComp
    case (polMons f, pIsConst f, vs) 
    of                                   
    ([]      , _   , _     ) -> CRP zr
    ((c,_): _, True, _     ) -> CRP c
    (mons    , _   , [v]   ) -> tor mons
            where
            tor []                 = CRP zr
            tor ((c, Vec [k]): ms) = if  k == 0  then  CRP c
                                     else       NRP v k (CRP c) (tor ms)
  
    ((c,_): _, _   , v: vs') -> tor $ upolMons $ headVarPol Map.empty f
          where
          tor []           = CRP $ zeroS c
          tor ((b, k): ms) = let d = toR vs' b
                             in   
                             if k == 0 then  d  else  NRP v k d $ tor ms

------------------------------------------------------------------------
toRPol :: CommutativeRing a => 
          Char -> RPolVarsTerm -> [RPolVar] -> Pol a -> RPol a
          --mode  vt              rvars        f        

  -- Convert polynomial  f <- a[x1..xn]  to  r-polynomial  rf  
  -- respectively to the given r-variable set description  vt  and
  -- the variable correspondence 
  --                       rvars = [v1..vn] <--> [x1..xn] = pVars f,
  --                       rvars  is the subset of  set(vt).
  --
  -- REQUIRED:  v1 > .. > vn  by the comparison from vt.
  --
  -- mode = 'l'           means the pp order in  f  is lexComp, in
  --                      this case the computation is more direct,
  --        other letter  will cost the initial reordering of f.

toRPol  mode  vt  rvars  f@(Pol _ a _ vars dm) = 
  let
     vcp = rvarsTermCp vt 
  in
  if  genLength rvars == genLength vars  &&
      isOrderedBy (flip vcp) rvars  then
                                    RPol (toRPol' mode rvars f) a vt dm
  else
  error $ concat 
  ["\ntoRPol ", mode: " rvarTerm rvars f,\n\n",
   "rvarTerm =  ",  showsRVarsTerm 1 vt "\n",
   "rvars =  ",     showsn 1 rvars "\n",
   "f =  ",         showsn 1 f "\n <-            ",  showsDomOf 1 f
   "\n\nrvars  must biject with  (pVars f)  \
   \and be ordered decreasingly by <rpolComp>.\n"]

------------------------------------------------------------------------
substValsInRPol :: 
          CommutativeRing a => Char -> [(RPolVar,a)] -> RPol a -> RPol a
                             -- mode   pairs            f

  -- Substitute  [(v1=a1)..(vn,an)]  into r-polynomial f.
  --
  -- Required:  v1 > .. > vn  in the comparison from f.
  -- mode = 'l'  
  --       means linear f, in this case the substitution is cheaper.
  --
  -- Example:   subst 'l' [(y,2),(z,4)] (x + 3*y + 1) =  x + 7

substValsInRPol  mode  pairs  r@(RPol f _ vt _) = 
  let
    vcp                      = rvarsTermCp vt
    addConst a (CRP b)       = CRP (a+b)
    addConst a (NRP v n c t) = NRP v n c $ addConst a t

    sb  []               f                     = f
    sb  _                (CRP a)               = CRP a 
    sb  ps@((u,a): ps')  f@(NRP v _ (CRP b) t) = 
                                         case  vcp u v
                                         of
                                         GT -> sb ps' f
                                         LT -> NRP v 1 (CRP b) (sb ps t)
                                         _  -> addConst (b*a) $ sb ps' t
  in
  case mode
  of
  'l' -> ct r $ sb pairs f
  _   -> error $ concat 
         ["\nsubstValsInRPol ", mode: " pairs r,",
          "\npairs  - of kind (rvar,value) =  ", shows pairs $
           showsRPolInfo_ 1 r "r"
           "\n\nOnly linear  r  (mode == 'l') can handle so far\n"]

------------------------------------------------------------------------
instance CommutativeRing a => Show  (RPol a) where 
                                             showsPrec _ = showsn 0
instance CommutativeRing a => DShow (RPol a)
  where
  dShows opt f =
            showsSPPol' opt zr unm ord pref . rpol'ToSPPol' $ rpolRepr f
            where 
            (pref, zr) = (rpolVPrefix f, zeroS $ sample f)
            unm        = Just $ unity zr
            ord        = isOrderedRing $ snd $ baseRing zr $ dom f    

------------------------------------------------------------------------
rpol'ToSPPol' :: AddGroup a => RPol' a -> SPPol' a
rpol'ToSPPol' f =  toS f []
  where
  z = zeroS $ head $ pCoefs f
  toS (CRP a)       = if  a == z  then  id  else  ((a, []) :)
  toS (NRP v n c t) =
           foldr (.) (toS t) [((b, (v, n): pp) :) | (b, pp) <- toS c []]



{- reserve *******************************************
instance (Convertible a b) => Convertible a (RPol' b)
  where  cvm a f = fmap CRP (cvm a (lc f))
instance Convertible a b => Convertible a (RPol b)
  where cvm a f = fmap (ct f) $ cvm a $ sample f
***********************************************
-}
