------------------------------------------------------------------------
------------------------------------------------------------------------
--  The Algebraic Domain Constructor  DoCon,   version 2.12
--
--  Copyright  Serge Mechveliani,    2012
------------------------------------------------------------------------
------------------------------------------------------------------------




{-   Residue ring ResidueE   R/(b)  for a  c-Euclidean ring R,  
     R not a field,  b /= 0.
So, ResidueE requires for R:
                       (Euclidean, Yes), (DivRemCan, Yes), (IsField, No)
- see  Manual.`euc',`ring.prop'.
Here the non-trivial instances are defined for  R/(b)  for the 
categories from  Set  up to  LinSolvRing.
The instances  GCDRing, FactorizationRing, EuclideanRing, Field
are presented trivially - only for the case of a prime b.
------------------------------------------------------------------------
SPECIAL cases.
--------------
* R = Integer
  - the instances up to Ring done specially.
  Also some category instances for ResidueE R  analyze the case when
  R is isomorphic to Integer.
  They do this by extracting the generator list  gensA  from the 
  additive group and testing whether it is a singleton  Just [_].   
  In this case (Lemma), the map  
                       i: Integer -> R,   n |-> n*un,   un = unityOf_R,
  is an isomorphism of additive groups.
* Case R = k[x],  k a field,  is programmed separately in  RsePol_.
-}




module ResEuc_   -- all needed from here is reexported by  Residue
where
-- instances for  ResidueE:
--   Show,DShow,Set,AddSemigroup,AddMonoid,AddGroup,MulSemigroup,
--   MulMonoid,Ring,CommutativeRing,LinSolvRing,GCDRing,
--   FactorizationRing,EuclideanRing,Field,
--
-- specialization for  ResidueE Integer:   instances 
--  Set, AddSemigroup, AddGroup, MulSemigroup, Ring

import System.Random (Random(..))    -- non-dtandard, non-GHC

import qualified Data.Map as Map (lookup, insert)

import Data.Maybe (fromJust)

import DPrelude 
       (DShow(..), -- class
        InfUnn(..), PropValue(..), Expression(..),  ct, ctr, 
        allMaybes, not3, boolToPropV, mapmap, showsn, showsWithDom
       )
import Categs
import SetGroup 
import Ring0_   
import Ring_    (eucGCDE)
import Ring1_   (remEuc)
import ResEuc0_ (Residue(..), isCorrectRse)
import ResEuc1_ (rseBaseSet, rseBaseAddSemigroup,
                 rseBaseMulSemigroup, rseBaseAddGroup, rseBaseRing
                )
import qualified ResEuc1_ (ifCEuc_rse_)






------------------------------------------------------------------------
ifPrime_ :: PIRChinIdeal a -> b -> (String-> String) -> (b, c) -> (b, c)
ifPrime_   iI                dom  msg                   v =  
  case 
      isFactorizOfPrime $ pirCIFactz iI
  of
  No -> (dom, error $ msg "\n\nPrime iI needed\n")
  _  -> v

------------------------------------------------------------------------
instance DShow a => Show  (ResidueE a) where  showsPrec _ = showsn 0
instance DShow a => DShow (ResidueE a) where 
                                       dShows opt = dShows opt . resRepr

instance (EuclideanRing a, Random a) => Random (ResidueE a)  
  where
  randomR (l, h) g = (ctr l a, g')  where 
                              (a, g') = randomR (resRepr l, resRepr h) g
  random _ = 
           error "\nrandom  for (ResidueE _):  use  randomR  instead.\n"


instance EuclideanRing a => Set (ResidueE a)  
  where
  baseSet    = rseBaseSet 
  compare_m  = compareTrivially 
  showsDomOf = rseShowsd_
  fromExpr   = rseFromExpr_

rseShowsd_ verb r = showChar '(' . showsDomOf verb b . showString "/<" . 
                    showsn verb b . showString ">)" 
                                       where b = pirCIBase $ resPIdeal r

rseFromExpr_ r e =  rd e

  {- old:   case  fromExpr (resRepr r) e  of
            ([x], "" ) -> ([ctr r x], "")
            (_  , msg) -> ([], "fromExpr (Rse sample _ _) e:  could"
                             ++" not read  e  as sample. \n" ++msg)
  -}
  -- The aim of the below definition is to enable applying, say,
  --  
  -- smParse _ " (x+1)/(x^2) + 2*x "    for  Rational[x]/(x^3-2)
  --
  -- (rather than   (smParse _ "x+1")/(smParse _ "x^2") + ...  )
  where
  rd (E (L "-") []   [e2]) = p "-u" ([],"") (rd e2)
  rd (E (L "-") [e1] [e2]) = p "-"  (rd e1) (rd e2)
  rd (E (L "+") [e1] [e2]) = p "+"  (rd e1) (rd e2)
  rd (E (L "*") [e1] [e2]) = p "*"  (rd e1) (rd e2)
  rd (E (L "/") [e1] [e2]) = p "/"  (rd e1) (rd e2)
  rd (E (L "^") [e1] [e2]) = pw (rd e1) $ fromExpr (1 :: Integer) e2
  rd e                     = case fromExpr (resRepr r) e
                             of
                             ([x], "") -> ([ct r x], "")
                             (_,   ms) -> ([], msg (msg' ++ ms))

  msg = showString "\nfromExpr r e,\nr = " . showsn 1 r . 
        showString "\n <- D/I =  " . showsDomOf 1 r
  msg' = "\n\nCould not read  e  by the sample  r.\n\n"

  p "-u" _         ([f], "") = ([negRes f],   "")
  p "-"  ([f], "") ([g], "") = ([subRes f g], "")
  p "+"  ([f], "") ([g], "") = ([addRes f g], "")
  p "*"  ([f], "") ([g], "") = ([mulRes f g], "")
  p "/"  ([f], "") ([g], "") = 
                   case rseDivm_ f g 
                   of
                   Just q -> ([q], "")
                   _      -> ([],  msg "\n\nFailed to divide with `/'.")

  p _    ([_], "") pair      = pair
  p _    pair      _         = pair

  pw ([f], "" ) ([n], "" ) = ([powerRes f n], "" )
  pw ([_], "" ) (_,   msg) = ([],             msg)
  pw (_,   msg) ([_], "" ) = ([],             msg)

  -- we do not use here  MulSemigroup (Residue a) ----------------------
  -- because of a particular GHC treating of OI
  --
  unityRes r = ctr r $ unity $ resRepr r 
  negRes r   = ctr r $ neg $ resRepr r
  addRes r   = ctr r . add (resRepr r) . resRepr 
  subRes r   = ctr r . sub (resRepr r) . resRepr
  mulRes r   = ctr r . mul (resRepr r) . resRepr 
  divRes r   = fromJust . rseDivm_ r
  invRes r   = divRes (unityRes r) r

  powerRes r n | n == 1    = r
               | n == 0    = unityRes r 
               | n < 0     = powerRes (invRes r) (-n) 
               | otherwise = let h = powerRes r (quot n 2)
                             in
                             if even n then  h `mulRes` h
                             else            (h `mulRes` h) `mulRes` r
  ----------------------------------------------------------------------



------------------------------------------------------------------------
instance 
     (EuclideanRing a,  Set (ResidueE a)  ) => AddSemigroup (ResidueE a) 
                        -- overlaps in ghc
  where
  baseAddSemigroup = rseBaseAddSemigroup
  zero_m r = Just $ ct  r $ zeroS $ resRepr r

  neg_m r = ifCEuc r "A" (("neg_m r," ++) . showsWithDom 1 r "r" "A") $
            Just $ ctr r $ neg $ resRepr r
                             -- ifCEuc  tests the correctness condition,
                             --         the rest part forms the result
  add r1 r2 = 
          ifCEuc r1 "A" (("add r1 r2,"++) . showsWithDom 1 r1 "r1" "") $
          ctr r1 $ add (resRepr r1) (resRepr r2)
  sub_m r = 
           ifCEuc r "A" (("sub_m r1 r2,"++) . showsWithDom 1 r "r1" "A") 
           Just . ctr r . sub (resRepr r) . resRepr

------------------------------------------------------------------------
ifCEuc :: Dom r => r a -> String -> (String -> String) -> b -> b
ifCEuc             x      name      msg                   v =
  case
      Map.lookup EuclideanRing (dom x)
  of
  Just (D1EucR t) -> 
              case  isCEucRing t  
              of
              Yes -> v
              _   -> error $ msg
                     ('\n': (name ++ "  must be a c-Euclidean Ring.\n"))
  _ -> error $ msg $ ("\nEucRingTerm not found in  "++) (name ++ "\n")


------------------------------------------------------------------------
instance 
  (EuclideanRing a, AddSemigroup (ResidueE a)) => AddMonoid (ResidueE a)
                    -- overlaps in ghc
         
instance 
   (EuclideanRing a, AddSemigroup (ResidueE a)) => AddGroup (ResidueE a)  
                     -- overlaps in ghc
  where 
  baseAddGroup = rseBaseAddGroup

instance 
     (EuclideanRing a,  Set (ResidueE a)  ) => MulSemigroup (ResidueE a)
                        -- overlaps in ghc
  where
  baseMulSemigroup = rseBaseMulSemigroup 
  unity_m r = 
         ifCEuc r "A" (("\nunity_m r," ++) . showsWithDom 1 r "r" "A") $
         Just $ ctr r $ unity $ resRepr r

  mul r = ifCEuc r "A" (("mul r1 r2," ++) . showsWithDom 1 r "r1" "A") .
          ctr r . mul (resRepr r) . resRepr 

  divide_m r = ifCEuc r "A" (("divide_m r1 r2," ++) . 
                            showsWithDom 1 r "r1" "A") . rseDivm_ r
  divide_m2 _ = error 
                   "\ndivide_m2 (Rse ..) _:   use  divide_m  instead.\n"
  root _ _    = error "\nroot _ (Rse ..):\nit is not defined for \
                      \Euclidean residues so far, sorry.\n"
 
  -- inv_m, power_m   are the default ones.


rseDivm_ rx ry =               -- LOCAL.  Re-used for  a = k[x].
                               -- Division in R/(b) by extended GCD. 
  let
    b           = pirCIBase $ resPIdeal rx
    rmd mode x  = remEuc mode x b 
    (d, [u, _]) = eucGCDE [resRepr ry, b]   -- d = gcd(y,b) = u*y+v*b
  in
  case divide_m (resRepr rx) d  
  of
  Nothing -> Nothing
  Just q  -> let {q' = rmd '_' q;  u' = rmd '_' u}
             in  Just $ ct rx $ rmd 'c' (q'*u')

------------------------------------------------------------------------
instance 
  (EuclideanRing a, MulSemigroup (ResidueE a)) => MulMonoid (ResidueE a)
                    -- overlaps in ghc

instance (EuclideanRing a,
          AddSemigroup (ResidueE a), MulSemigroup (ResidueE a) 
         )                                            -- overlaps in ghc
         => Num (ResidueE a) 
  where      
  negate = neg
  (+)    = add
  (-)    = sub  
  (*)    = mul
  signum _ = error "\nsignum (Rse ..):  it is senseless there.\n"
  abs    _ = error "\nabs (Rse ..):  it is senseless there.\n"
  fromInteger _ = error "\nfromInteger  to (ResidueE _):  use  fromi.\n"


instance (EuclideanRing a,
          Num (ResidueE a), MulSemigroup (ResidueE a) -- overlaps in ghc
         ) 
         => Fractional (ResidueE a)
  where   
  (/) = divide
  fromRational _ = error "fromRational  to (ResidueE _):\n\
                          \use  fromi  combined with  divide_m.\n"

instance (EuclideanRing a,
          AddGroup (ResidueE a), MulSemigroup (ResidueE a) 
         )                                            -- overlaps in ghc
         => Ring (ResidueE a)
  where
  baseRing    = rseBaseRing
  fromi_m r n = ifCEuc r "A" (("fromi_m r " ++) . shows n . 
                showChar ',' . showsWithDom 1 r "r" "A") $ 
                fmap (ctr r) $ fromi_m (resRepr r) n


instance 
   (EuclideanRing a, Ring (ResidueE a) ) => CommutativeRing (ResidueE a)
                     -- overlaps in ghc
                        

------------------------------------------------------------------------
instance 
        (EuclideanRing a, Ring (ResidueE a)) => LinSolvRing (ResidueE a)
                          -- ovrlaps in ghc
  where
  -- See  Manual 'linr', `euc'.
  --                 
  -- Concerning  moduloBasis, gxBasis, syzygyGens.
  --
  -- The specifics of the representation of a ring  a/I 
  -- (see Manual-'gx'), in the case of Euclidean `a' is that  I = (b),  
  -- and that gxBasis in `a' and in a/I is either [] or [g].
  -- Again, as for the generic  a/I  ring,  moduloBasis  does not depend 
  -- on the mode: it does the canonic reduction and needs intermediate 
  -- implicit gxBasis application.

  gxBasis [] = ([], [])
  gxBasis rs =  
    let 
      r           = head rs
      b           = pirCIBase $ resPIdeal r
      ([g],[row]) = gxBasis ((map resRepr rs)++[b])
    in
    ifCEuc 
      r "A" (("gxBasis rs," ++) . showsWithDom 1 r "head rs" "A") $
      if  
         divides b g  then ([], [])
      else                 ([ctr r g], [map (ctr r) $ init row])

  moduloBasis _    [] r = (r, [])
  moduloBasis mode rs r =
    let
      (b, xs)  = (pirCIBase $ resPIdeal r, map resRepr rs)
      (rm, qs) = moduloBasis "c" (xs ++ [b]) $ resRepr r
    in 
    ifCEuc r "A" (("moduloBasis " ++) . (mode ++) . (" rs r," ++) . 
                  showsWithDom 1 r "r" "A"
                 )                    (ctr r rm, map (ctr r) $ init qs)

  syzygyGens mode [] = error $ concat ["\nsyzygyGens ", mode, " [].\n"]
  syzygyGens mode rs =  
    let 
      r        = head rs  
      b        = pirCIBase $ resPIdeal r
      zr       = zeroS b
      canRem x = remEuc 'c' x b
      rels'    = syzygyGens "" (b: (map resRepr rs))
      rls'     = mapmap canRem rels'
      rels''   = filter (not . all (== zr)) (map tail rls')
    in 
    ifCEuc r "A" (("syzygyGens " ++) . (mode ++) . (" rs," ++) . 
                  showsWithDom 1 r "head rs" "A"
                 ) $                            mapmap (ct r) rels''

  baseLinSolvRing r dm =  
    case (Map.lookup LinSolvRing dm, dom r) 
    of
    (Just (D1LinSolvR t), _ ) -> (dm, t)
    (_,                   aD) -> ResEuc1_.ifCEuc_rse_ aD dm msg (dm', t)
      where
      msg = showString "\nbaseLinSolvRing r dom'," . 
                                 showsWithDom 1 r "r" "" . showChar '\n'
      dm' = Map.insert LinSolvRing (D1LinSolvR t) dm
      t   = LinSolvRingTerm 
            {linSolvRingProps =
                [(ModuloBasisDetaching, Yes), (ModuloBasisCanonic, Yes),
                 (WithSyzygyGens,       Yes), (IsGxRing,           Yes)]
            }


------------------------------------------------------------------------
instance (EuclideanRing a, Ring (ResidueE a) ) => GCDRing (ResidueE a)   
                           -- overlaps in ghc
  where
  -- The below definitions of  canInv, canAssoc, gcD  for  R/(b)
  -- have the correctness condition:
  --                      b  is prime   (that is R/(b) is a field).
  --  
  -- Therefore they are defined trivially.

  canInv   x = if  isZero x  then  unity x  else  x
  canAssoc x = if  isZero x  then  x        else  unity x

  gcD []      = error "\ngcD []  for  (ResidueE _).\n"
  gcD (x: xs) = let  z = zeroS x  
                in   if  all (== z) (x: xs)  then  z  else  unity z

  hasSquare _ = error "\nhasSquare (Rse ..):  it is not \
                      \defined for residue ring.\n"
  toSquareFree _ = error "\ntoSquareFree (Rse ..):  it is not \
                         \defined for residue ring.\n"
    
  -- baseGCDRing tests partially  c-Euclidean, primality  of `a'.
  -- In the case of `No',  dom  is un-changed  and  GCDRingTerm
  -- turns to (error..).

  baseGCDRing  r@(Rse _ iI aD) dm =  
    case
        Map.lookup GCDRing dm  
    of
    Just (D1GCDR t) -> (dm, t)
    _               -> ResEuc1_.ifCEuc_rse_ aD dm msg $ 
                                            ifPrime_ iI dm msg (dom', t)
      where
      msg = showString "\nbaseGCDRing r dom',\nr = " . showsn 1 r . 
            showString "\n <- D/I =  " . showsDomOf 1 r . showChar '\n'

      dom' = Map.insert GCDRing (D1GCDR t) dm
      t    = GCDRingTerm 
             {gcdRingProps = [(WithCanAssoc, Yes), (WithGCD, Yes)]}


------------------------------------------------------------------------
instance 
 (EuclideanRing a, Ring (ResidueE a) ) => FactorizationRing (ResidueE a)  
                   -- overlaps in ghc
  where
  -- factor, isPrime, primes   presume  *** R/(b) is a field *** 
  --                                               (that is b is prime).
  -- Therefore they are defined trivially.

  factor x = [(x, 1)]
  primes _ = error "\nprimes (Rse ..):  it is not defined\
                   \ for residues, so far.\n"

  baseFactrRing  r@(Rse _ iI aDom) dom =  
    case 
        Map.lookup FactorizationRing dom
    of
    Just (D1FactrR t) -> (dom, t)
    _                 -> ResEuc1_.ifCEuc_rse_ aDom dom msg $ 
                                           ifPrime_ iI dom msg (dom', t)
      where
      msg = showString "\nbaseFactrRing r dom',\nr = " . showsn 1 r . 
             showString "\n <- D/I =  " . showsDomOf 1 r . showChar '\n'

      dom' = Map.insert FactorizationRing (D1FactrR t) dom
      t    = FactrRingTerm 
             {factrRingProps = [(WithIsPrime, Yes), (WithFactor, Yes),
                                (WithPrimeList, Yes)]
             }

------------------------------------------------------------------------
instance 
     (EuclideanRing a, Ring (ResidueE a) ) => EuclideanRing (ResidueE a)
                       -- overlaps in ghc
  where
  -- eucNorm,divRem  presume  *** R/(b) is a field *** 
  --                                         (that is b is prime).
  -- Therefore they are defined trivially.

  eucNorm x = 
           if  isZero x  then 
                  error ("\neucNorm 0\nfor  " ++ (showsDomOf 1 x ".\n"))
           else   0      

  divRem mode x y =
    let
       z = zeroS y
    in
    case (x == z, y == z)  
    of 
    (_,    True) -> error $ concat ["\ndivRem ", mode: " x 0,",
                                    showsWithDom 1 x "x" "" ".\n"]
    (True, _   ) -> (z,   z)
    _            -> (x/y, z)


  baseEucRing  r@(Rse _ iI aDom) dom = 
    case  
        Map.lookup EuclideanRing dom  
    of
    Just (D1EucR t) -> (dom, t)
    _               -> ResEuc1_.ifCEuc_rse_ aDom dom msg $ 
                                           ifPrime_ iI dom msg (dom', t)
      where
      msg  = showString "\nbaseEucRing r rdom," . 
                                 showsWithDom 1 r "r" "" . showChar '\n'
      dom' = Map.insert EuclideanRing (D1EucR t) dom
      t    = EucRingTerm 
             {eucRingProps = [(Euclidean, Yes), (DivRemCan, Yes),
                                                (DivRemMin,Yes)]}

------------------------------------------------------------------------
instance (EuclideanRing a, Ring (ResidueE a) ) => Field (ResidueE a)   
                           -- overlaps in ghc
  --
  -- presumed:  *** Prime(resPIdeal r) = Yes ***




------------------------------------------------------------------------
------------------------------------------------------------------------
-- Special instances for  ResidueE Integer

instance Set (ResidueE Integer)    -- specializes  baseSet
  where
  compare_m  = compareTrivially    -- so far
  showsDomOf = rseShowsd_
  fromExpr   = rseFromExpr_

  baseSet r dm =  
    case 
        (Map.lookup Set dm, pirCIBase $ resPIdeal r)  
    of
    (Just (D1Set o), _) -> (dm, o)
    (_,              b) -> (Map.insert Set (D1Set o) dm, o)
      where
      o = 
        let bel 'r' r = (pirCIBase (resPIdeal r)) == b && isCorrectRse r
            bel _   _ = True
            props' = [(Finite      , Yes), (IsBaseSet     , Yes),
                      (FullType    , No ), (OrderIsTrivial, Yes), 
                      (OrderIsTotal, No ), (OrderIsNoether, Yes), 
                      (OrderIsArtin, Yes)
                     ]               
            list = map (ct r) [0 .. (pred b)]
        in
        OSet {osetSample  = r,          
              membership  = bel, 
              osetCard    = Fin b,    
              osetPointed = Just (Just r),
              osetList    = Just list,
              osetBounds  = (Nothing, Nothing, Nothing, Nothing),
              osetProps   = props',      
              osetConstrs = [], 
              osetOpers   = []}


------------------------------------------------------------------------
instance AddSemigroup (ResidueE Integer) -- specializes baseAddSemigroup
  where
  zero_m r = Just $ ct r (0 :: Integer)
  neg_m  r = Just $ ctr r $ neg $ resRepr r   
    --
    -- it differs from the generic case in that the correctness
    -- test for the ring Integer is not necessary
    --
  add   r = ctr r . add (resRepr r) . resRepr        
  sub_m r = Just . ctr r . sub (resRepr r) . resRepr  

  times_m r n = let {r' = resRepr r;  b = pirCIBase $ resPIdeal r}
                in  Just $ ctr r (r'*(remEuc 'c' n b))

  baseAddSemigroup r dm = 
    case 
        Map.lookup AddSemigroup dm  
    of
    Just (D1Smg s) -> (dm, s)
    _              -> (Map.insert AddSemigroup (D1Smg s) dm, s)
      where
      s = Subsemigroup {subsmgType    = Add,
                        subsmgUnity   = Just $ zero_m r,
                        subsmgGens    = Just [unity r],
                        subsmgProps   = props,
                        subsmgConstrs = [],     
                        subsmgOpers   = []  
                       }                                       
      props = [(Commutative,       Yes), (IsGroup,               Yes),
               (IsMaxSubsemigroup, No ), (IsOrderedSubsemigroup, No ),
               (IsCyclicSemigroup, Yes)]



instance AddGroup (ResidueE Integer)
  where
  baseAddGroup r dm =
    case
        (Map.lookup AddGroup dm, pirCIFactz $ resPIdeal r)  
    of
    (Just (D1Group g), _ ) -> (dm, g)
    (_,                ft) -> (Map.insert AddGroup (D1Group g) dm, g)
      where
      g = Subgroup {subgrType    = Add, 
                    subgrGens    = Just [unity r], 
                    subgrCanonic = Just $ const $ zeroS r,
                    subgrProps   = props,
                    subgrConstrs = [],      
                    subgrOpers   = []
                   }                           
      props = [(IsNormalSubgroup,  Yes), (IsMaxSubgroup, No    ),
               (IsCyclicGroup,     Yes), (IsPrimeGroup,  prime'),
               (IsOrderedSubgroup, No ) 
              ]
      prime' = case ft of []       -> Unknown
                          [(_, 1)] -> Yes
                          _        -> No    
                                -- Z/(b) is a prime group <=> b is prime


------------------------------------------------------------------------
instance MulSemigroup (ResidueE Integer)  
  where                                  -- is aims mostly at increasing
                                         -- of division performance 
  baseMulSemigroup = rseBaseMulSemigroup
  unity_m r        = Just $ ct r (1 :: Integer)
  mul     r        = ctr r . mul (resRepr r) . resRepr

  -- power_m, inv_m  is the default one

  divide_m r1 r2 =                 -- applies special extended gcd for Z
                                   -- and representation
    let                            -- Z/(b) =iso= Z/(b1) +..+ Z/(bn)
      iI          = resPIdeal r1
      (b, bs, es) = (pirCIBase iI, pirCICover iI, pirCIOrtIdemps iI)
      add1 x y    = mod (x+y) b   -- (x+y) modulo b
                                               
      div1 b x y = let (v, d) = gcdE_mod_b b 0 1 b y 
                   in                              -- (x/y) modulo b
                                  -- 0 < d= gcd(b,y) <= y < b 
                                  -- 0 < v < b, v*y === d (modulo b)
                   case quotRem x d 
                   of 
                   (q, 0) -> Just $ rem (v*q) b
                   _      -> Nothing
              
      gcdE_mod_b b v1 v2 e f =          -- -> (v,d), d = gcd(e,f)...
           --
           -- As if the column [e,f] brought to the staircase form 
           -- with the accumulation of transformation matrix 
           -- (initially=unityMatrix).  Only u1,u2 are skipped here:
           --                   [u1,v1] * [e] = [d]
           --                   [u2,v2]   [f]   [0]
           -- 0 < d <= y < b.  v = v1  in the end.
         
        if f == 0 then (v1, e)              -- 0 < e <= b
        else
        let (q, r) = quotRem e f          -- 0 < q <e,  0 <= r < f
            v'     = v1 - (rem (q*v2) b)
            v''    = if  v' < 0  then  v'+b  else  v'
        in
        gcdE_mod_b b v2 v'' f r
      ------------------------------------------------------------------
    in    
    case map resRepr [r1, r2]
    of
    [0, _] -> zero_m r1
    [_, 0] -> Nothing
    [x, y] -> 
        if  not (isCorrectRse r1 && isCorrectRse r2)  then  
            error $ concat 
            ["\ndivide_m r1 r2,\nr1 = ", showsn 1 r1 $ 
             showsWithDom 1 r2 "r2" ""
                     "\nWrongly represented residue among operands.\n"]
        else
        if  null bs || null es  then  fmap (ct r1) $ div1 b x y
        else
        let -- Chinese-remainder method:
            -- divide the residue projections  x'i by y'i
            -- in  Z/(bi)  and restore the result via the Lagrange 
            --                                           idempotents ei.
            (x's, y's) = (map (rem x) bs, map (rem y) bs)
            q's        = zipWith3 (\ x' y' b -> div1 b x' y') x's y's bs
        in
        fmap (\ qs -> ct r1 $ foldl1 add1 $ 
                                    zipWith (\ q e -> mod (q*e) b) qs es
             ) $ allMaybes q's

  divide_m2 _ _ = error "\ndivide_m2  for  ResidueE Integer:  use  \
                                                  \divide_m  instead.\n"
  root _ _ = error "\nroot _  for  ResidueE Integer:\n\
                   \it is not defined, so far.\n"

  {- finish this. Needs Chinese method ****
  root 1   x = Just (Just n)
  root deg x = case  (deg<1, n==0 || n==1, n<0, even deg)  of
                          error "(root degree n):  degree < 1 \n"
                              (case  root deg (-n)
  -}

  -- inv_m  is the default one.



------------------------------------------------------------------------
instance Ring (ResidueE Integer)                 -- specializes baseRing
  where
  fromi_m r = fmap (ctr r) . fromi_m (resRepr r)
 
  baseRing r dm = 
    case (Map.lookup Ring dm, resPIdeal r)  
    of
    (Just (D1Ring rg), _ ) -> (dm, rg)
    (_,                iI) -> br (pirCIBase iI) (pirCIFactz iI)  
      where
      br b ft = if b < 2 then  
                      error $ concat 
                           ["\nbaseRing r rdom,", showsWithDom 1r "r" ""
                                                      "\nbase(I) < 2\n"]
                else  (Map.insert Ring (D1Ring rg) dm, rg)
        where
        rg =
          let
            unR   = unity r
            props =
             [(IsField,       bPrime), (HasZeroDiv   , not3 bPrime),
              (HasNilp,       hasNl ), (IsPrimaryRing, bPrimary   ),
              (Factorial,     bPrime), (PIR,           Yes        ),
              (IsOrderedRing, No    ), (IsRealField,   No         ),
              (IsGradedRing,  No    ) -- ?
             ]
            (bPrime, bPrimary) = case ft of 
                                         []       -> (Unknown, Unknown)
                                         [(_, 1)] -> (Yes,     Yes    )
                                         [_]      -> (No,      Yes    )
                                         _        -> (No,      No     )

            hasNl = if null ft then  Unknown
                    else           boolToPropV $ any (/= 1) $ map snd ft
            opers = 
              if  bPrime /= Yes  then []  else [(WithPrimeField, wp)]
                where
                wp = WithPrimeField' 
                     {frobenius            = (id, Just . Just),
                                                 -- ^p = id in Z/(p)
                      dimOverPrime         = Fin 1,
                      primeFieldToZ        = resRepr,
                      primeFieldToRational = undefined,
                      primitiveOverPrime   = 
                        ([unR], [(unR, 1), (-unR, 0)], \ r -> [(r, 0)])}
                         -- x-1               
          in
          Subring {subringChar    = Just b,
                   subringGens    = Just [unR],
                   subringProps   = props,
                   subringConstrs = [],
                   subringOpers   = opers}

