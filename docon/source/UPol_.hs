------------------------------------------------------------------------
------------------------------------------------------------------------
--  The Algebraic Domain Constructor  DoCon,   version 2.12
--
--  Copyright  Serge Mechveliani,    2012
------------------------------------------------------------------------
------------------------------------------------------------------------



 

module UPol_   -- Various useful items for Univariate Polynomial.
               -- All needed from here is reexported by  Pol.

(PolLike(..), UPol(..), PolVar, PPOrdTerm, PPOId, ppoId, 
 ppoComp, ppoWeights, lexPPO, Multiindex, Mon, upolMons, lmU,
 leastUPolMon, pHeadVar, lc, lc0, pCont, numOfPVars, varP, deg0, cPMul, 
 umonMul, mUPolMul, umonLcm, cToUPol, 
 monicUPols_overFin, upolPseudoRem, pmul,
 neg_, add_, times_, mul_, shows_         -- local

 -- , instance (PolLike p ...) => LeftModule a (p a),
 -- instances for UPol:  Eq, Dom, Cast, PolLike
)
where
import qualified Data.Map as Map (lookup, insert)

import Data.List (delete, genericDrop, genericReplicate)

import DPrelude 
       (Length(..), DShow(..), Cast(..), -- classes
        Natural, PropValue(..), InfUnn(..), Comparison, ShowOptions(..),
        allMaybes, tuple31, tuple32, tuple33, less_m, sum1, lookupProp, 
        zipRem, ct, ctr, showsn
       )
import Categs (CategoryName(..), Dom(..), Domain1(..), Domain2(..), 
               Domains1, OSet(..), Subring(..), Property_Subring(..), 
               Submodule(..), Property_Submodule(..), UMon
              )
import SetGroup (Set(..), AddSemigroup(..), MulSemigroup(..),
                 AddGroup(..), neg, zeroS, isZero, times, unity
                )
import RingModule (Ring(..),CommutativeRing(), GCDRing(..),
                   LeftModule(..), isOrderedRing, powersOfOne
                  )
import VecMatr (Vector(..)                   )
import PP_     (PowerProduct, PPComp, lexComp)





------------------------------------------------------------------------
type PPOrdTerm = (PPOId, PPComp, [[Integer]])

  -- This is for multivariate polynomial.
  -- The power product ordering description (term)    (id, cp, ws)
  -- consists of the  identifier  id,   comparison function  cp, 
  -- list  ws  of the integer weights.
  -- []  for  ws  means the weights are not given.
  --
  -- For the most purposes, it suffices to set it, for example,
  -- like this:  (("dlex",3), degLex, []).
  --
  -- `id' is set by the programmer (in addition to var list) in 
  -- order to identify the domain parameter for polynomial. 
  -- DoCon looks at `id' only when trying to find whether the two
  -- polynomials are under the same pp-ordering - this may be 
  -- useful, for example, for the conversion between domains.

type PPOId = (String, Natural)

ppoId      = tuple31   -- extracting parts of PPOrdTerm
ppoComp    = tuple32   --
ppoWeights = tuple33   --

lexPPO :: Natural -> PPOrdTerm
lexPPO i =  (("lex", i), lexComp, []) 

------------------------------------------------------------------------
class Dom p => PolLike p                   -- some common operations for 
  where                                    -- UPol,Pol,EPol,RPol,SymPol
  pIsConst :: CommutativeRing a => p a -> Bool

  deg    :: CommutativeRing a => p a -> Integer   -- total degree
  ldeg   :: CommutativeRing a => p a -> Integer   -- total degree of lpp
                                                  -- (depends on order)
  lpp    :: CommutativeRing a => p a -> PowerProduct       -- leading pp
  lm     :: CommutativeRing a => p a -> Mon a        -- leading monomial
  pTail  :: CommutativeRing a => p a -> p a   
  pCoefs :: p a -> [a]  
                      -- coefficients listed in same order as monomials;
                      -- for RPol, the order is "depth first"

  pFreeCoef :: CommutativeRing a => p a -> a
  pCoef     :: CommutativeRing a => p a -> [Integer] -> a   
                                 -- coefficient of a given power product
  pVars :: p a -> [PolVar]                    -- variable list
  pPPO  :: p a -> PPOrdTerm                   -- pp ordering description

  pMapCoef :: AddGroup a => Char -> (a -> a) -> p a -> p a     
                   --       mode    f 
                   -- map  f  to each coefficient.  mode = 'r' means
                   -- to detect (and delete) appeared zero monomials

  pMapPP :: AddGroup a => ([Integer] -> [Integer]) -> p a -> p a     
                       -- f 
                -- map f to each exponent. It does not reorder the 
                -- monomials, nor sums similars. Examples:
                -- pMapPP (\ [i]  -> [i+2]  ) (x+1)   = x^3+x^2  in Z[x]
                -- pMapPP (\ [i,j]-> [i+j,j]) (x*y+1) = x^2*y + 1 

  degInVar :: CommutativeRing a => Integer -> Natural -> p a -> Integer
                                -- for0       i          f 
                                             -- deg f  in variable No i,
                                             -- put it  for0  for zero f

  pCDiv :: CommutativeRing a => p a -> a -> Maybe (p a)  
                                              -- quotient by coefficient
  varPs :: CommutativeRing a => a -> p a -> [p a]       
                     --
                     -- Convert each variable from  f :: p a  multiplied
                     -- by the given non-zero coefficient  to  p a.
                     -- See it in  PolLike UPol  below.

  pValue :: CommutativeRing a => p a -> [a] -> a
              --
              -- Value at [a1..an],  extra  ai  are cut out.
              -- Example: for a[x], a[x,y]   x^2   -> [2]     -> 4   
              --                             x^2+y -> [2,0]   -> 4   
              --                             x^2+y -> [2,0,3] -> 4
              --                             x^2+y -> [2]     -> error..

  pDeriv :: CommutativeRing a => Multiindex Natural -> p a -> p a
            --
            -- Derivative by multiindex.
            -- Example: for variables = [x1,x2,x3,x4],
            --          pDeriv [(2,3),(4,2)] === (d/dx2)^3*(d/dx4)^2
     
  pDivRem :: CommutativeRing a => p a -> p a -> (p a, p a)
           --
           -- f -> g -> (quotient,remainder)
           -- For  a[x] and Field(a),  it has to satisfy the 
           -- Euclidean division property.
           -- In any case, it has to continue the Euclidean-like 
           -- reduction (applying  divide_m  to divide coefficients)
           -- while  lm(g)  divides  lm(currentRemainder).
           -- Example:  
           -- 5*x^2+1, 2*x -> ((2/5)*x, 1      )   for  a = Rational
           --                 (0      , 5*x^2+1)   for      Integer

  pFromVec :: CommutativeRing a => p a -> [a] -> p a
            --
            -- Convert (dense) vector to p. of given sample.
            -- So far, consider it ONLY for  UPol.
            -- Example:  2*x -> [0,1,0,2,3,0,0] -> x^5 +2*x^3 +3*x^2

  pToVec :: CommutativeRing a => Natural -> p a -> [a]
              --
              -- List of the given length of p. coefficients,
              -- gaps between the power products filled with zeroes.
              -- So far, consider it ONLY for  UPol.

  -- lpp f   for UPol is  Vec [deg f], for EPol  it is  snd $ eLpp f
  -- ldeg    for Pol is  totalDeg.lpp;
  --         for EPol -  totalDeg.snd.eLpp;
  -- lm      for UPol it means extended  lmU  - see below,
  --         for EPol it is          (c,p)  where  (c,(_,p)) = eLm f
  -- pPPO    is  lexPPO 1     for UPol,
  --         for EPol it is   pPPO .epolPol
  -- 
  -- c = pCoef f js:  
  --   for UPol  js = [j]  and  c = coefficient of degree  j  in  f,
  --   for Pol             c = coefficient of power product  Vec js,
  --   for EPol  js = j:ks  and  c = coefficient of  (j,Vec ks),
  --   for RPol, SymPol    - undefined.  
  -- In  pToVec n f = cs
  --   Let  m  be the monomial number in the dense form.
  --   If  n > m  then  n-m  zeroes are prepended to the result,
  --   otherwise,  m-n  higher monomials are cut out.
  --   Example:  7 (a*x^4 + b*x^2 + c)   -> [0,0,a,0,b,0,c]
  --             7 (a*x^9 + b*x^5 + c*x) -> [0,b,0,0,0,c,0]


lc :: (PolLike p, Set a) => p a -> a              -- leading coefficient
lc f =  case pCoefs f of 
                      a: _ -> a
                      _    -> error $ concat
                              ["\nlc 0, \n0 <- R", shows (pVars f)
                               ",\nR = ", showsDomOf 1 (sample f) ".\n"]

cPMul :: (PolLike p, Ring a) => a -> p a -> p a
cPMul a =  pMapCoef 'r' (mul a)                -- product by coefficient

pCont :: (GCDRing a, PolLike p) => p a -> a 
pCont =  gcD . pCoefs

pHeadVar :: (PolLike p, Set a) => p a -> PolVar 
pHeadVar f =  
  case pVars f  
  of
  v: _ -> v
  _    -> 
      error $ concat
      ["\npHeadVar f, \nf <- R", shows (pVars f)
       ",\nR = ", showsDomOf 1 (sample f) "\n:\nempty variable list.\n"]

numOfPVars :: PolLike p => p a -> Integer
numOfPVars =  genLength . pVars

varP :: (PolLike p, CommutativeRing a) => a -> p a -> p a    
varP a =  head . varPs a                    -- useful in univariate case 

lc0 :: (PolLike p, AddSemigroup (p a), Set a) => a -> p a -> a
lc0 zr f =  if isZero f then zr else lc f

deg0 :: (PolLike p, AddSemigroup (p a), CommutativeRing a) =>
        Char -> Integer -> p a -> Integer
deg0    mode    d          f =  case (isZero f, mode) of
                                                   (True, _  ) -> d
                                                   (_,    'l') -> ldeg f
                                                   _           -> deg f

------------------------------------------------------------------------
instance (Ring a, PolLike p, AddGroup (p a)) => LeftModule a (p a) 
  where
  cMul = cPMul 

  baseLeftModule (a, f) dm = 
    case  
        (Map.lookup LeftModule dm, Map.lookup Ring (dom f))  
    of
    (Just (D2Module t), _               ) -> (dm, t)
    (_,                 Nothing         ) ->
                       (dm, error $ concat
                            ["\nbaseLeftModule (a, f) dm,\n\
                             \a =  ",  showsn 1 a 
                             ",\nf <- P = R", shows (pVars f)
                             ",\nfor  P  over  R,\nR = ", showsDomOf 1 a
                             "\nRing not found for  R.\n"]
                       )
    (_,                 Just (D1Ring aR)) ->
        let
          propsA = subringProps aR
          hasZD  = lookupProp HasZeroDiv propsA
          props  = [(IsFreeModule,       Yes    ),
                    (IsPrimeSubmodule,   No     ),
                                           -- for it is the full module
                    (IsPrimarySubmodule, No     ), --
                    (IsMaxSubmodule    , No     ), --
                    (HasZeroDivModule,   hasZD  ),
                    (IsGradedModule,     No     )  -- so far
                   ]
          t = Submodule {moduleRank     = Infinity,
                         moduleGens     = Nothing,
                         moduleProps    = props,
                         moduleGenProps = [],
                         moduleConstrs  = [],
                         moduleOpers    = []}
        in
        (Map.insert LeftModule (D2Module t) dm, t)


------------------------------------------------------------------------
type Multiindex i = [(i, i)] 
type Mon a        = (a, PowerProduct)   -- multivariate monomial
type PolVar       = String

data UPol a = UPol [UMon a] a PolVar (Domains1 a)
  --
  -- Sparse Univariate polynomial  UPol mons c v aD :
  -- mons  are ordered decreasingly by deg,  zero monomials skipped,
  -- c     the sample coefficient,
  -- aD        domain description for  a.
  -- Example:  UPol [(1,4),(-2,2),(3,0)]  0 "t" dZ     expresses
  --                 t^4 - 2*t^2 + 3   of  Z[t].

upolMons :: UPol a -> [UMon a]
upolMons (UPol ms _ _ _) = ms

-- The  variable  is extracted by  pHeadVar. 


instance Eq a => Eq (UPol a) where
                             f == g =  (upolMons f) == (upolMons g)

lmU :: Set a => UPol a -> UMon a                 -- leading monomial
lmU f =  case upolMons f  
         of 
         m: _ -> m
         _    -> error $ concat ["\nlmU 0  in  R", shows (pVars f) 
                               ",\nR = ", showsDomOf 1 (sample f) ".\n"]

leastUPolMon :: Set a => UPol a -> UMon a 
leastUPolMon f =  
        case  upolMons f  
        of 
        [] -> error $ concat ["\nleastUPolMon 0  in  R", shows (pVars f)
                              ",\nR = ", showsDomOf 1 (sample f) ".\n"]
        ms -> last ms


instance Dom UPol where dom    (UPol _ _ _ d) = d
                        sample (UPol _ c _ _) = c


------------------------------------------------------------------------
instance AddGroup a => Cast (UPol a) (UMon a) 
                                           -- map monomial to polynomial
  where
  cast mode (UPol _ c v d) (a,p) =  UPol mons c v d
            where
             mons = if  mode == 'r' && isZero a  then []  else [(a, p)]

instance AddGroup a => Cast (UPol a) [UMon a] 
  where                                    
  cast mode (UPol _ c v d) mons =  UPol ms c v d    -- order NOT checked
       where                                         
       z  = zeroS c
       ms = if mode /= 'r' then  mons  else  filter ((/= z) . fst) mons

instance Ring a => Cast (UPol a) a
  where  
  cast mode (UPol _ _ v d) a =  case mode of 'r' -> cToUPol v d a
                                             _   -> UPol [(a, 0)] a v d


{- wait language extension ****
instance Ring a => Cast (UPol a) PolVar where
  cast _ (UPol _ a _ d) v = UPol [(unity a, 1)] a v d
                                                     -- in new variable
- this overlaps with  Cast (UPol a) a   by  a = PolVar  !
-}

-- Example.  For  f = UPol _ 1 "x" d  <-  P = Z[x] 
--
-- cast _ f 2               maps  2                  to P
-- cast _ f (2,3)           maps  monomial 2*x^3     to P
-- cast _ f [(2,3),(-1,1)]  maps  monomial list ...  to P
-----------------------------------------------------------------------


instance PolLike UPol
  where  
  pIsConst f = iszero_ f || (deg f) == 0
  deg        = snd . lmU
  ldeg       = snd . lmU
  lpp f      = Vec [deg f]

  pVars (UPol _ _ v _) = [v]

  pPPO _ = lexPPO 1
  pCoefs = map fst . upolMons

  pCoef f js = 
    let
      {z = zeroS $ sample f;  vs = pVars f}
    in
    case js
    of
    [j] -> case  dropWhile ((> j) . snd) $ upolMons f  
           of 
           (a, i): _ -> if i == j then  a  else  z
           _         -> z

    _   -> error $ concat ["\npCoef f ", shows js "  in R", shows vs 
                           ",\nR = ", showsDomOf 1 z ".\n"]

  degInVar for0 i f =  case (upolMons f, i) of ([],   _) -> for0
                                               (m: _, 1) -> snd m
                                               _         -> 0
  varPs a f = [ct f (a, 1 :: Integer)]

  pTail f = case upolMons f  
            of
            _: ms -> ct f ms 
            _     -> error $ concat ["\npTail 0  in  R", shows (pVars f)
                               ",\nR = ", showsDomOf 1 (sample f) ".\n"]

  pFreeCoef (UPol mons c _ _) =  if  null mons  then  zeroS c
                                 else 
                                 case last mons of (a, 0) -> a
                                                   _      -> zeroS c

  lm f = (a, Vec [j])  where (a, j) = lmU f         -- lmU is usable

  pCDiv f c = let (cs, exps) = unzip $ upolMons f  
              in
              case  allMaybes [divide_m a c | a <- cs]
              of
              Just qts -> Just $ ct f $ zip qts exps
              _        -> Nothing

  pMapCoef mode f g = cast mode g [(f a, i) | (a, i) <- upolMons g]

  pMapPP f g = ct g [(a, head $ f [n]) | (a, n) <- upolMons g]

  pValue f [] = 
               error $ concat ["\npValue f [],  f <- R", shows (pVars f)
                               ",\nR = ", showsDomOf 1 (sample f) "\n."]

  pValue f (a:_) = case unzip $ upolMons f
                   of      
                   ([], _ ) -> zeroS a
                   (cs, es) -> sum1 $ zipWith (*) cs $ powersOfOne es a

  pDeriv [(1, n)] f = deriv_ n f
  pDeriv mInd     f = 
                     error $ concat
                     ["\npDeriv ", shows mInd " f  in R", 
                      shows (pVars f) ",\nR = ", showsDomOf 1 (sample f)  
                      "\nFor UPol,  multiindex must be  [(1, n)].\n"]

  pFromVec f coefs = ctr f $ reverse $ 
                     zip (reverse coefs) [(0 :: Integer) ..]
  pToVec n f = 
    let 
      ms = upolMons f
      z  = zeroS $ sample f 
      dv n []           = genericReplicate n z
      dv n ((a, j): ms) = (genericReplicate (n-j-1) z) ++ (a: (dv j ms))
    in
    dv n $ dropWhile ((>= n) . snd) ms


  pDivRem  f@(UPol monsF c v _)  g =  
                                   
    case (ctr g $ zeroS c, upolMons g) 
    of
    (_,     []          ) -> 
               error $ concat ["\npDivRem f 0  in R", shows [v] 
                               ",\nR = ", showsDomOf 1 (sample f) ".\n"]

    (zeroP, (b, p): msg') -> d monsF zeroP
      where
      d []                 q = (q, zeroP)   
      d msf@((a,p1): msf') q =                           
        let
           dp = p1 - p
        in
        if dp < 0 then  (q, ct g msf)   
        else
        case divide_m a b  
        of
        Nothing -> (q, ct g msf)
        Just e  -> let mon      = (e, dp)        
                       [f', g'] = map (ct g) [msf',msg']
                       msfNew   = upolMons $ sub_  f' $ mUPolMul mon g'
                   in
                   d msfNew$ add_ q $ ct g mon

-----------------------------------------------------------------------
iszero_ :: UPol a -> Bool
iszero_ =  null . upolMons

neg_ :: AddGroup a => UPol a -> UPol a                       -- f -> -f
neg_ f =  ct f [(neg a, p)| (a, p) <- upolMons f]

add_, sub_ ::  AddGroup a => UPol a -> UPol a -> UPol a

add_ f = ct f . pa (upolMons f) . upolMons
  where
  z = zeroS $ sample f

  pa []       msG      = msG
  pa msF      []       = msF
  pa (m: msf) (n: msg) =
    let 
       {(a, p) = m;  (b, q) = n;  c = add a b}
    in  
    case compare p q  
    of
    GT -> m: (pa msf (n: msg))  
    LT -> n: (pa (m: msf) msg)
    _  -> if c == z then  pa msf msg  else  (c, p): (pa msf msg)

sub_ f = add_ f . neg_

------------------------------------------------------------------------
umonMul :: Ring a =>  a -> UMon a -> UMon a -> [UMon a]
                   -- zero
umonMul z (a, p) (b, q) = let c = a*b in  if c == z then  []  
                                          else            [(c, p+q)]

mUPolMul :: (Ring a) => UMon a -> UPol a -> UPol a
mUPolMul                (a, p)    f      =  
                                 ctr f [(a*b, e+p)| (b, e)<- upolMons f]

times_ :: Ring a => (a -> i -> a) -> UPol a -> i -> UPol a
times_              t                f         n =  
                                ctr f [(t a n, e)| (a, e) <- upolMons f]
  -- t = `times' for `a'

------------------------------------------------------------------------
mul_ :: CommutativeRing a => UPol a -> UPol a -> UPol a
mul_                         f         g      =         
                          ct f $ pmul zr cp id (upolMons f) (upolMons g)
            where
            {zr = zeroS $ sample f;  cp = compare :: Comparison Integer}
                                                                   
pmul ::          
 (CommutativeRing a, AddSemigroup exp) =>                                    
 a-> Comparison exp-> ((a, exp) -> (a, exp))-> [(a, exp)]-> [(a, exp)]->
                                                            [(a, exp)]
pmul z  cp            mapMon                  f             g =
  --
  -- multiplies pol-like-s under the transformation of monomials 
  -- mapMon applied to the monomials of the product.  
  -- mapM = id  is the usual multiplication.  For skipping 
  -- (univariate) mononials the multiples of  x^n  use
  -- mapMon (a,m) = if  m < n  then  (a,n)  else  (zeroS a, 0),
  -- and so on.
  -- CAUSION for implementor:  mapMon  may break the ordering.
  if  
    null $ tuple33 $ zipRem f g  then  pm f g    -- put longer ahead
  else                                 pm g f
    where
    pm f g = pm' [ [(d, p') | 
                    (a, p) <- f, 
                    let {(d, p') = mapMon (c, add p q);  c = a*b},
                    c /= z, d /= z
                   ] 
                   | (b, q) <- g
                 ]
    pm' []  = []        
    pm' [f] = f
    pm' fs  = pm' $ mergeNeighbours fs

    mergeNeighbours (f: g: fs) = (mergeZ f g): (mergeNeighbours fs)
    mergeNeighbours fs         = fs

    mergeZ []          g           = g
    mergeZ f           []          = f
    mergeZ ((a, p): f) ((b, q): g) = 
                         case (cp p q, add a b) 
                         of
                         (GT, _) -> (a, p): (mergeZ f ((b, q): g))
                         (LT, _) -> (b, q): (mergeZ ((a, p): f) g)
                         (_,  c) -> if c == z then  mergeZ f g
                                    else            (c, p): (mergeZ f g)

------------------------------------------------------------------------
umonLcm :: GCDRing a => UMon a -> UMon a -> UMon a

  -- Lcm  of monomials over a  gcd-ring.
  -- For the Field case, it is better to compute this "in place", as
  -- (unity a, ppLcm ...)

umonLcm (a, p) (b, q) = (a*(b/(gcD [a, b])),  lcm p q)


------------------------------------------------------------------------
cToUPol :: Ring a => PolVar -> Domains1 a -> a -> UPol a

-- Coefficient --> polynomial.
-- Apply it to create a  sample polynomial.  See manual.

cToUPol v aDom a = if  a == zeroS a  then  UPol []       a v aDom
                   else                    UPol [(a, 0)] a v aDom


------------------------------------------------------------------------
monicUPols_overFin :: CommutativeRing a => UPol a -> [[UPol a]]

-- Given  f  from  a[x],  deg f > 0,  `a' a Finite ring,
-- build the infinite listing - partition  [gs(d),gs(d+1)..] 
-- for the set  {g <- a[x] |  deg g >= d, lc g = 1},
--
-- were  d = deg f,   gs(n) = [g | deg g = n, lc g = 1]
-- Example.
-- For  a = Z/(3),  
--      2*x   -> [[x,x+1,x+2],[x^2,x^2+1..x^2+2x+2],[x^3..] .. ],
--      2*x^2 -> [            [x^2,x^2+1..x^2+2x+2],[x^3..] .. ].

monicUPols_overFin f =
  let
    (a,  [v], dR)     = (sample f, pVars f, dom f)
    (zr, un,  aX)     = (zeroS a, unity a, snd $ baseSet a dR)
    Just listR        = osetList aX
    but0R             = delete zr listR
    polGroups n allps = 
            [UPol ((un, n): g) a v dR | g <- allps]:
            (polGroups (succ n) (allps ++ [(a, n): g | 
                                               a <- but0R, g <- allps]))
    msg = showString "\nmonicUPols_overFin f,\nf <- R" . shows [v] . 
          showString ",\nR = " . showsDomOf 1 (sample f)
  in
  case (pIsConst f, osetList aX, deg f)
  of
  (True, _,       _) -> error $ msg "\n\ndeg f > 0  needed.\n"
  (_,    Nothing, _) -> 
         error $ msg "\nListing not found for the coefficient domain.\n"

  (_,    _,       d) -> 
        genericDrop (pred d) $ polGroups 1 ([]: [[(a, 0)] | a <- but0R])


------------------------------------------------------------------------
deriv_ :: CommutativeRing a => Integer -> UPol a -> UPol a

        -- LOCAL.
        -- derivative of n-th order of univariate polynomial:  (d/dx)^n
deriv_ 0 f = f
deriv_ n f = ctr f $ map monDeriv mons
       where
       mons = upolMons f
       z    = zeroS $ sample f
       monDeriv (a, j) = if j < n then (z, 0)
                         else    (times a $ product [(j-n+1) .. j], j-n)


------------------------------------------------------------------------
upolPseudoRem :: CommutativeRing a => UPol a -> UPol a -> UPol a

-- Pseudodivision in  R[x]. 
-- See D.Knuth ([Kn],vol 2,section 4.6.1).
-- For non-zero  f,g,  there exist  k,q,r  such that 
--                  (lc(g)^k)*f = q*g + r,   k <= deg(f)-deg(g)+1, 
--                  and either  r = 0  or  deg r < deg g.
-- upolPseudoRem  returns only  r. 
-- It does not use the coefficient division,  and it should be cheaper
-- than   pDivRem (lc(g)^(n-m+1)*f) g.

upolPseudoRem f g 
 
  | iszero_ g = error $ concat
                ["\nupolPseudoRem f 0   in R", shows (pVars f)
                 ",\nR = ", showsDomOf 1 (sample f) ".\n"]

  | iszero_ f = ctr f $ zeroS $ sample f
  | otherwise = rem f
    where
    rem h = if iszero_ h then  h
            else
            let {n = deg h;  mon' = (lc h, n-m)}
            in
            if n < m then  h
            else    rem $ sub_ (cPMul b $ pTail h) $ mUPolMul mon' gTail
                                   
    (b, m, gTail) = (lc g, deg g, pTail g)


------------------------------------------------------------------------
shows_ :: Ring a => ShowOptions -> UPol a -> String -> String

-- Write univariate polynomial to string.
--
-- Prepends the polynomial image to the initial string  s.
-- If  a  is an Ordered ring,  then the mode  `ord'   is set which 
-- writes  ..- m  instead of ..+(-m)  for the negative coefficient
-- monomials.
-- If  a  has unity  then  unity coefficient images  are skipped.

shows_ opt (UPol mons c v dom) =   
  (case 
       (zeroS c, unity_m c, Map.lookup Ring dom)  
   of
   (zr, unM, Just (D1Ring rR)) -> ss zr unM $ isOrderedRing rR
   _                           ->
           error $ concat ["\nshows_ f,  f <- R", shows [v] ",\nR = ", 
                           showsDomOf 1 c "\n\nRing not found in R.\n"]
  )
  where
  ss zr unM ordered =
   let  
     -- wrex :: PolVar -> Integer -> String -> String    writes exponent
     wrex _ 0 = id
     wrex v 1 = (v ++)
     wrex v p = (v ++) . showChar '^' . shows p
     -------------------------------------------------------------------
     wMon (c, p) =  
        case (unM, wrex v p "") 
        of
        (_,       []  ) -> dShows opt c
        (Nothing, pStr) -> dShows opt c . showChar '*' . (pStr ++)
        (Just u , pStr) -> if c == u then (pStr ++)
                           else  dShows opt c . showChar '*' . (pStr ++)
     -------------------------------------------------------------------
     wr mons = 
        case (ordered, mons) 
        of
        (_,   []          ) -> showChar '0' 
        (_,   [m]         ) -> wMon m
        (Yes, m: (c,p): ms) ->
                          if  less_m c zr  then 
                                wMon m . (" - "++) . wr ((neg c, p): ms)
                          else  wMon m . (" + "++) . wr ((c, p)    : ms)

        (_,   m: ms       ) -> wMon m . (" + "++) . wr ms
   in
   showChar '(' . wr mons . showChar ')'
