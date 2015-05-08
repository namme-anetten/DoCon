------------------------------------------------------------------------
------------------------------------------------------------------------
--  The Algebraic Domain Constructor  DoCon,   version 2.12
--
--  Copyright  Serge Mechveliani,    2012
------------------------------------------------------------------------
------------------------------------------------------------------------





module Ring_

  -- `Chinese' ideal representation, 
  -- some other useful items for Ring.
  --
  -- All needed from here is  reexported by  RingModule, Z.


  (eucGCDE, powersOfOne, logInt, diffRatios,
   isoRing, isoGCDRingTerm, isoEucRingTerm, isoFactrRingTerm, 
   isoLinSolvRingTerm,  isoDomain1, isoDomains1,  eucIdeal
   -- ,instances for Integer:
   -- Fractional, Ring, CommutativeRing, OrderedRing, GCDRing
  )

where   
import qualified Data.Map as Map (empty, lookup, insert, map)

import Data.List  (transpose)
import Data.Ratio (numerator, denominator)
import DPrelude (Length(..), -- class 
                 PropValue(..), Z, Natural,  fmapfmap, showsWithDom)
import Categs  
import SetGroup
import Ring0_




------------------------------------------------------------------------
eucGCDE :: EuclideanRing a => [a] -> (a, [a])

     -- Extended GCD:  xs-> (d, qs),  d = gcd[x1..xn] = q1*x1 +..+ qn*xn
eucGCDE xs = 
  case xs 
  of
  []  -> error "eucGCDE []\n"
  x:_ ->
    let
      (zr, un)   = (zeroS x, unity x)      
      gc (x: xs) =                      -- reduce to  gcd2
        case (xs, x == zr)  
        of
        ([],    _   ) -> (x,[un])
        (_,     True) -> case gc xs of (d, qs) -> (d, zr:qs)
        (y: ys, _   ) -> let (d,u,v)    = gcd2 (un, zr, x) (zr, un, y)
                             (d', q:qs) = gc (d:ys)
                         in
                         if null ys then (d,  [u, v]          )
                         else            (d', (u*q): (v*q): qs)
                                               
      gcd2 (u1, u2, u3) (v1, v2, v3) =  
                    -- It starts with  (un,zr,x) (zr,un,y),  x /= zr.
                    -- Euclidean GCD is applied to u3,v3, operations on
                    -- u1,u2,v1,v2 perform parallelwise to ones of u3,v3
              
                    if v3 == zr then (u3, u1, u2)
                    else
                    case divRem '_' u3 v3  
                    of  
                    (q, r) -> gcd2 (v1, v2, v3) (u1-q*v1, u2-q*v2, r)
    in
    gc xs



------------------------------------------------------------------------
powersOfOne :: Ring a => [Z] -> a -> [a]

  -- Generic Horner scheme to compute the power list:
  --                                      [j1..jn] x -> [x^j1..x^jn]
  -- j1 > j2 > .. > jk.
  -- Here  x  is from the ring with unity, and  x^0 = 1,  0^n = 0.

powersOfOne js x =
  let
    (z,   u ) = (zeroS x, unity x)
    (js', j0) = span (/= 0) js
    p0        = if null j0 then [] else [u]

    powers []         = []       -- here js > 0, x /= zr,un
    powers [j]        = [x^j]
    powers (i: j: js) = case  powers (j: js)  of
                                             p: ps -> (p*x^(i-j)): p: ps
  in
  if  x == z || x == u  then  (map (const x) js') ++ p0
  else                        (powers js')        ++ p0



------------------------------------------------------------------------
logInt :: OrderedRing a => a -> a -> Natural

-- logInt b a
-- is the integer part of logarithm of  a  by base  b,   a, b > 1.
--
-- Where it is correct?  At least, for  Z, Fraction Z.
--
-- Examples:  logInt 3 29 == logInt (3:/2) (29:/8) == 3,
--            logInt 29 3 == 0.

logInt b a = case unity b of

  u -> if  a <= u || b <= u  then
                    error $ ("logInt "++) $ shows b $ (' ':) $ shows a $
                             ":\narguments > 1  required\n"
       else  lg 0 u
                    where
                    lg l p = case compare p a of EQ -> l
                                                 GT -> pred l
                                                 _  -> lg (succ l) (p*b)
-- specialize logInt :: Z -> Z -> Z #-


------------------------------------------------------------------------
diffRatios :: 
          (AddGroup a, AddGroup b) => (b -> a -> b) -> [(a, b)] -> [[b]]
                                      -- qt            pairs   
  -- The interpolation tool.
  -- Given the table [(x0,y0)..(xn,yn)] for the function  y = f(x)
  -- : a -> b,  xi do not repeat,  the division operation  qt,
  -- build the difference ratio lists  [drs_1,drs_2..drs_n],
  -- drs_k  the list of difference ratios of order  k.
  -- Example scheme:
  -- diffRatios (/) [(x0,y0),(x1,y1),(x2,y2),(x3,y3)] =
  -- 
  -- [ [(y1-y0)/(x1-x0), (y2-y1)/(x2-x1), (y3-y2)/(x3-x2)],
  --    -- denote dr01   dr12             dr23 
  --   [(dr12-dr01)/(x2-x0), (dr23-dr12)/(x3-x1)],
  --    -- dr012             dr123
  --   [(dr123-dr012)/(x3-x0)]
  -- ]

diffRatios qt ps = 
  (case  
       (ps, unzip ps)  
   of
   (_: _: _, (xs, ys)) -> dr (tail xs) xs $ zipWith sub (tail ys) ys
   _                   ->
          error $ ("diffRatios <division> pairs,"++) $
                  ("\npairs = "++) $ shows ps $ "\n\nlength pairs < 2\n"
  )
  where
  dr []      _  _  = []
  dr shifted xs ds =   
             let dxs = zipWith sub shifted xs   -- [x(i)-x(i-k) |...]
                 dRs = zipWith qt  ds      dxs  -- [d(i)/dx(i)  |...]
             in
             dRs: (dr (tail shifted) xs (zipWith sub (tail dRs) dRs))


------------------------------------------------------------------------
isoRing :: (a -> b) -> (b -> a) -> Subring a -> Subring b
isoRing    f           fInv        rA        =
  Subring 
         {subringChar    = ch, 
          subringGens    = gens', 
          subringProps   = props, 
          subringConstrs = [],
          subringOpers   = map isomOp opers
         }
    where
    (ch, gens, props, opers) = (subringChar rA,  subringGens rA,
                                subringProps rA, subringOpers rA
                               )
    gens' = case gens of Nothing -> Nothing
                         Just gs -> Just $ map f gs

    isomOp (WithPrimeField, wp) = case frobenius wp of

      (fr, frInv) -> 
           (WithPrimeField,
            WithPrimeField' 
             {frobenius = (f . fr . fInv, fmapfmap f . frInv . fInv),
              dimOverPrime         = dimOverPrime wp,
              primeFieldToZ        = primeFieldToZ wp . fInv,
              primeFieldToRational = primeFieldToRational wp . fInv,
              primitiveOverPrime   = 
                    (map f pows, toOver_b minp, toOver_b . toPol . fInv)
             }
           ) 
           where  (pows, minp, toPol) = primitiveOverPrime wp
                  toOver_b            = map (\ (a, e) -> (f a, e))

     -- OLD***** isomOp (Grading, Grading' cp weight forms) =
     --           (Grading, Grading' cp weight' forms')
     --  where weight'= weight.fInv; forms' = map f.forms.fInv
            

------------------------------------------------------------------------
isoGCDRingTerm :: (a -> b) -> (b -> a) -> GCDRingTerm a -> GCDRingTerm b
isoGCDRingTerm    _f          _fInv       r =
                             GCDRingTerm {gcdRingProps = gcdRingProps r}


isoFactrRingTerm :: 
              (a -> b) -> (b -> a) -> FactrRingTerm a -> FactrRingTerm b
isoFactrRingTerm _f      _fInv        r =
                       FactrRingTerm {factrRingProps = factrRingProps r}

isoLinSolvRingTerm :: 
          (a -> b) -> (b -> a) -> LinSolvRingTerm a -> LinSolvRingTerm b
isoLinSolvRingTerm _f _fInv r =
                 LinSolvRingTerm {linSolvRingProps = linSolvRingProps r}

isoEucRingTerm :: (a -> b) -> (b -> a) -> EucRingTerm a -> EucRingTerm b
isoEucRingTerm    _           _           r =
                             EucRingTerm {eucRingProps = eucRingProps r}


------------------------------------------------------------------------
instance Functor PIRChinIdeal 
  where
  fmap f i =  
        case (pirCIBase i, pirCICover i, pirCIOrtIdemps i, pirCIFactz i)
        of
        (a, cs, ids, ft) ->  
                PIRChinIdeal {pirCIBase      = f a,
                              pirCICover     = map f cs,
                              pirCIOrtIdemps = map f ids,
                              pirCIFactz     = [(f p, e) | (p, e) <- ft]
                             }


------------------------------------------------------------------------
eucIdeal :: 
          (FactorizationRing a,EuclideanRing a) =>
          String -> a -> [a] -> [a] -> Factorization a -> PIRChinIdeal a  
          --mode    base cover  ids    factz
                                                      
  {-
   Defining ideal in Euclidean ring.
   Easy way to build the ideal description from incomplete parts.
   The parts are listed as in the PIRChinIdeal data fields.
   eucIdeal  completes the ideal term.
   CONDITIONS:  
   in the most complex case,  it needs a c-Euclidean ring with the
   factorization algorithm.  
   In this case, it is presumed that the given  `cover'  are the 
   canonical remainders modulo  b,  and this function returns the
   orthogonal idempotents  ids'  as the canonical remainders too 
   (if the mode contains 'e'). 

   mode = bMode++eMode++fMode   must be a Substring of  "bef";
   'b' <- mode  means to update the pirCICover  of the ideal term,
                otherwise - to leave it as it is ; 
   'e','f'      correspond to the parts  pirCIOrtIdemps, pirCIFactz.
   See manual.
   METHOD.
   The main part is to obtain the Lagrange idempotents  es  from  
   bs = `cover': 
   applying eucGCDE, find for each  j /= k,  j <- [1..w],
   d(j,k) = djk <- (bj),  dkj <- (bk),  such that  djk + dkj = 1
   Then put for idempotents  
                ek = product [d(j,k)| j<-[1..w], j/=k],  k <- [1..w]
  -}

eucIdeal mode b bs es ft =  
  let
    --------------------------------------------------------------------
                                            -- what about canAssoc ? ***
    -- see condition test in the end

    (_, eR)               = baseEucRing b Map.empty
    cEuc                  = isCEucRing eR
    canonicRem x          = snd $ divRem 'c' x b
    un                    = unity b
    [bMode, eMode, fMode] = [elem l mode | l <- "bef"]
    bsNew =  
      if not bMode || not (null bs) then  bs
      else
      let ft'  = if  not (null ft)  then  ft  
                 else                     mapFactorization $ factor b
          ft'' = [p^k | (p, k) <- ft']
      in
      if  cEuc == Yes && (genLength ft'') > 1  then  map canonicRem ft''
      else  ft''

    mapFactorization ps = if cEuc == Yes && (genLength ps > 1) then
                                       [(canonicRem p, j) | (p, j)<- ps]
                          else  ps

    ftNew = if  not fMode || not (null ft)  then  ft
            else
            if  null bs  then  mapFactorization $ factor b
            else               mapFactorization $ concat $ map factor bs
    --------------------------------------------------------------------
    msg = showString "\neucIdeal_ft mode b bs es ft  for" . 
                                               showsWithDom 1 b "b" "R"
    esNew =  
      if  not eMode || not (null es)  then  es
      else 
      if cEuc /= Yes then
          error $ msg "\nForming es':  a c-Euclidean ring R required.\n"
      else  bsToEs bsNew

    -- ek = product [d(j,k)| j<-[1..w], j/=k],  k <- [1..w]:

    bsToEs [_] = [un]  -- prime b
    bsToEs bs  = map (canonicRem . product) $ transpose$ full $ bsToD bs
                         --
                         -- bsToD bs = [[(d12,d21)   ..   (d1w,dw1)]
                         --                   [(d23,d32)..(d2w,dw2)]
                         --             ...
                         --                       [(d(w-1)w,dw(w-1)]
                         --            ]     
    bsToD []       = error $ msg "\nbsToD [] \n"
    bsToD [_]      = error $ msg "\nbsToD [_]\n"
    bsToD [b1, b2] = [[makePair b1 b2]]
    bsToD (b1: bs) = (map (makePair b1) bs): (bsToD bs)

    makePair b1 b2 =  
      let  
        (g, [d, d']) = eucGCDE [b1, b2] 
      in
      case inv_m g  
      of
      Just g' -> (canonicRem (d*g'*b1), canonicRem (d'*g'*b2))
                                    --
                                    -- b1,b2 are reciprocally prime,
                                    -- and  d*g'*b1 + d'*g'*b2 = 1 
      _       -> error$ msg "\n(bj)+(bk) /= (1)  for some  j/=k \n"


    -- full (bsToD bs) = [[1  , d12, d13  ...   d1w]
    --                    [d21, 1  , d23  ...   d2w]
    --                    ...
    --                    [dw1, dw2, ...        1  ]
    --                   ]     
 
    full [[(d, d')]] = [[un, d], [d', un]]
    full (ps:pss)    = (un:ds): (zipWith (:) d's (full pss))
                                                 where
                                                 (ds, d's) = unzip ps 
    --------------------------------------------------------------------
  in
  if  length mode < 4  then
              PIRChinIdeal {pirCIBase      = b,      pirCICover = bsNew,
                            pirCIOrtIdemps = esNew,  pirCIFactz = ftNew
                           }
  else        error $ msg "\nmode  must be a substring of \"bef\" \n"



------------------------------------------------------------------------
isoDomain1 :: (a -> b) -> (b -> a) -> Domain1 a -> Domain1 b
isoDomain1    f           f'          dom =
  case dom
  of
  D1Set      t  -> D1Set      $ isoOSet            f f' t
  D1Smg      t  -> D1Smg      $ isoSemigroup       f f' t
  D1Group    t  -> D1Group    $ isoGroup           f f' t
  D1Ring     t  -> D1Ring     $ isoRing            f f' t
  D1GCDR     t  -> D1GCDR     $ isoGCDRingTerm     f f' t
  D1FactrR   t  -> D1FactrR   $ isoFactrRingTerm   f f' t
  D1LinSolvR t  -> D1LinSolvR $ isoLinSolvRingTerm f f' t
  D1EucR     t  -> D1EucR     $ isoEucRingTerm     f f' t
  -- D1Ideal ...

isoDomains1 :: (a -> b) -> (b -> a) -> Domains1 a -> Domains1 b
isoDomains1    f           f'       =  Map.map (isoDomain1 f f')




------------------------------------------------------------------------
------------------------------------------------------------------------
instance Fractional Integer   
  where
  (/) = divide                              -- these two yield (error..) 
                                            -- when d does not divide  n
  fromRational r = (numerator r)/(denominator r)


instance Ring Integer  
  where
  fromi_m  _ = Just

  baseRing _ dm = 
    case Map.lookup Ring dm 
    of
    Just (D1Ring r) -> (dm, r)
    _               -> (Map.insert Ring (D1Ring r) dm, r)
         where
         r = Subring {subringChar  = Just 0, subringGens    = Just [1],
                      subringProps = props,  subringConstrs = [],
                      subringOpers = []
                     }
         props = [(IsField      , No     ), (PIR        , Yes),
                  (HasZeroDiv   , No     ), (HasNilp    , No ), 
                  (IsPrimaryRing, Yes    ), (Factorial  , Yes), 
                  (IsOrderedRing, Yes    ), (IsRealField, No ),
                  (IsGradedRing , Unknown)]


instance CommutativeRing Integer  
instance OrderedRing     Integer  

instance GCDRing Integer  
  where
  canAssoc x = if  x < 0  then  -x  else  x
  canInv   x = if  x < 0  then  -1  else  1

  gcD []     = error "gcD [] \n"
  gcD [x]    = x
  gcD (x:xs) = gcd x (gcD xs)

  hasSquare _ = 
       error "\nhasSquare (n :: Integer)  is not implemented, so far.\n\
             \It can be replaced with  any ((> 1) . snd) $ factor n.\n"
  toSquareFree _ = error "\ntoSquareFree (n :: Integer)  is not impleme\
                         \nted, so far.\nApply  factor n  instead.\n"
  baseGCDRing _ dm = 
            case Map.lookup GCDRing dm 
            of
            Just (D1GCDR t) -> (dm, t)
            _               -> (Map.insert GCDRing (D1GCDR t) dm, t) 
              where
              t = GCDRingTerm 
                  {gcdRingProps = [(WithCanAssoc, Yes), (WithGCD, Yes)]}
