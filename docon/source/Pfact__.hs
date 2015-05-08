------------------------------------------------------------------------
------------------------------------------------------------------------
--  The Algebraic Domain Constructor  DoCon,   version 2.12
--
--  Copyright  Serge Mechveliani,    2012
------------------------------------------------------------------------
------------------------------------------------------------------------




module Pfact__  -- Continuation of  Pfact_.
                -- All needed from here is reexported by Pol.

(RseUPol, RseUPolRse, toFromCanFinField, factorUPol_finField
 -- , instance of  FactorizationRing  for  k[x],  k  a finite field
)
where
import qualified Data.Map as Map (empty, lookup, insert)

import Data.Maybe (isJust)
import Data.List  (genericTake, transpose) 

import DPrelude (Length(..), -- class
                 PropValue(..), InfUnn(..),  
                 and3, delBy, ct, ctr, showsWithDom)
import Categs 
       (Dom(..), CategoryName(..), Domain1(..), ResidueE(..), 
        Subring(..), FactrRingTerm(..), Property_FactrRing(..), 
        Operation_Subring(..), OpName_Subring(..), Factorization
       )
import SetGroup (Set(..), times, power, unity, zeroS, isZero)
import RingModule
import Z     (dZ)
import UPol_ (PolLike(..), UPol(..), varP, upolMons, cToUPol, cPMul, 
                                                     monicUPols_overFin)
import Pol2_    ()
import Pgcd_    ()
import ResEuc0_ (Residue(..))
import LinAlg   (solveLinear_euc)
import Pfact_   (upolSqFree_finField)




------------------------------------------------------------------------
type RseUPol a    = ResidueE (UPol a)
type RseUPolRse a = RseUPol (ResidueE a)

toFromCanFinField ::
    Field a =>
    a -> Subring a -> (a -> RseUPolRse Integer, RseUPolRse Integer -> a)
 -- unity  aR          toCanonic                fromCanonic
-- Build canonical representation of finite field `a' as a pair of
-- isomorphisms     a <--> K = Zp[x]/(f),  p a prime integer,  
-- f irreducible over  Zp = Z/(p),  lc f = 1.
-- Denotation:  PF a prime field inside `a'.

toFromCanFinField a1 aR = 

  (case (not (isJust $ subringChar aR) || p <= 0, wp_mb, f') 
   of
   (True, _,       _ ) ->
                 error $ msg "Characteristic > 0 must be found for K.\n"
   (_,    Nothing, _ ) -> 
                    error $ msg "WithPrimeField term not found for K.\n"
   (_,    _,       []) -> 
                error $ msg "Minimal polynomial for x' over prime field\
                                           \ not found to generate K.\n"
   _                   -> (toCanonic, fromCanonic)
  )
  where
  msg = showString "\ntoFromCanFiniteField k1 K," . 
                                               showsWithDom 1 a1 "k1" ""
  (Just p, opers) = (subringChar aR, subringOpers aR)
  wp_mb           = lookup WithPrimeField opers 
  Just wp         = wp_mb
  pfToZ           = primeFieldToZ wp    -- a -> Integer restricted to PF
  (x'Powers, f', toInX) = primitiveOverPrime wp
                                  -- x' = head x'Powers  generates `a' 
                                  -- over PF,  f' the minimal polynomial
  pI     = eucIdeal "" p [p] [1] [(p, 1)] 
  pZ1    = Rse 1 pI dZ                        -- 1 of Zp
  pZ     = upField pZ1 Map.empty     
  x1     = cToUPol "x" pZ pZ1                 -- 1 of  X = Zp[x]
  dX     = upEucFactrRing x1 Map.empty               
  pfToPZ = ct pZ1 . pfToZ                     -- PF -> Zp 
  f      = ct x1 [(pfToPZ a, e)| (a, e) <- f']
  fI     = eucIdeal "" f [f] [x1] [(f, 1)] 
  k1     = Rse x1 fI dX                       -- 1 of K = Zp[x]/(f)    
  toCanonic a = ct k1 $ ct x1 [(pfToPZ a, e)| (a, e) <- toInX a]

  fromCanonic r =           -- for representative  sum [ni*x^i...], find
                            -- sum [ni*x'^i ...]  in `a' using the ready 
                            --                              powers of x'
      sumPowers (zip [0 ..] (a1: x'Powers)) $
                                          reverse $ upolMons $ resRepr r
        where
        sumPowers _  []              = zeroS a1
        sumPowers ps ((rz, i): mons) = (times xp j)+(sumPowers ps' mons)
                              where
                              j            = resRepr rz
                              (_, xp): ps' = dropWhile ((/= i) . fst) ps
               

------------------------------------------------------------------------
factorOverPrime :: Field k => UPol k -> Factorization (UPol k)
{- 
Factoring polynomial  f <- k[x]
over a prime finite field  k  of  p  elements:
                                           f --> [(f1,n1)..(fs,ns)],
fi  irreducible factors of  f.
Denotations:  X = k[x],  D = X/(f) a residue algebra,  e unity of D.
METHOD.
Berlekamp procedure: see [Me3,'ap.1'].
upolSqFree_finField  reduces to the square free  f.
Then, apply Berlekamp method  factor' f:
1. xPowers 
   = [1,x .. x^(r-1)]  the basis for linear space  D
2. mM = matrix for  h-> h^p - h  in D in the basis  xPowers
3. Kernel basis  
   kerB  of  M;  kerB' = [v <- kerB | v is not collinear to e]
   If  null kerB'  then  f  is irreducible.  Otherwise, go to 4.
4. gcd-s with kernel:
   convert each  v <- kerB'  to polynomial  h  and form  
   gs(h) = [g = gcd f (h+a)| x <- k, 0 < deg g < r];
   join gs(h) into list  gss  of groups of non-trivial factors of f.
5. splitFactors:
   starting with  fs = [f],  gss,  fs  the current list of 
   reciprocally prime factors of  f,  split  fs  by finding gcd with 
   the members of members of  gss  - until the full number  dimKer  of
   factors is obtained.
-}


factorOverPrime f =  
  if
    isZero f  then  error ("\nfactorOverPrime 0  in\n" ++ 
                                                 (showsDomOf 1 f ".\n"))
  else  concat $ map fts $ upolSqFree_finField f
  where
  (zr, dK    ) = (zeroS $ sample f, dom f)
  (_,  rK    ) = baseRing zr dK
  (un, Just p) = (unity zr, subringChar rK)
  fts (h, m)   = [(g, m) | g <- factorSeparable h]
    where
    factorSeparable f =  
                  splitFactors f dimKer ([f], 1) $ map nonTrivGCDs kerB'
      where
      pToRevVec r    = reverse .pToVec r
      pFromRevVec xs = pFromVec f $ reverse xs
      (r, x1, x)     = (deg f, unity f, varP un f)   
      kPols          = map (times x1) [0 .. (pred p)]  -- 0..p-1  in X
      (dX, fI) = (upEucRing f Map.empty, eucIdeal "" f [] [] [])
      d1       = Rse x1 fI dX                -- 1 of D
      xPowers  = x1: (map (x*) xPowers)      -- x^j, j = 0,..
      xPows       = genericTake r xPowers
      basImagePol = 
             [(resRepr $ power hD p) - h | h <- xPows, let hD = ct d1 h]
                                          -- form matrix for (^p)-E in D
                                          --
      mM   = transpose $ map (pToRevVec r) basImagePol 
      kerB = snd $ solveLinear_euc mM $ map (const zr) xPows
                                                          -- Ker B basis
      dimKer = genLength kerB
      kerB'  = delBy eColl kerB    -- remove collinear to e vector
      eColl  = all (== zr) . tail
      nonTrivGCDs v = filter nonTrivDeg [gcD [f, h+a] | a <- kPols]
                             where
                             h          = pFromRevVec v
                             nonTrivDeg = not . (`elem` [0, r]) . deg

-----------------------------------------------------------------------
splitFactors f dimKer = splitfs     -- also used in factorUPol_finField
  where
  splitfs (fs, n) gss = 
    case 
        (n == dimKer, gss) 
    of
    (True, _       ) -> fs
    (_,    gs: gss') -> splitfs (splitWithGroup (fs, n) gs) gss'
    _                -> 
      error $ concat 
      ["\nfactorUPol_finField f  ... reduced to (factorSeparable f1),",
       showsWithDom 1 f "f1" ""                         
                  ":\nNumber of factors < dim (Ker ((^p)-E))  - why?\n"
      ]        
  splitWithGroup (fs, n) gs = 
                 case (n == dimKer, gs)  
                 of
                 (True, _     ) -> (fs, n)
                 (_,    g: gs') -> splitWithGroup (split1 (fs, n) g) gs'
                 _              -> (fs, n)

  split1 (fs, n) g = 
    case 
        (n == dimKer, fs) 
    of
    (True, _     ) -> (fs,  n)
    (_,    []    ) -> ([g], 1)
    (_,    f: fs') ->
      let h                    = gcD [f, g]
          (f', g', fsn)        = (f/h, g/h, (fs', pred n))
          ((hs, m), (hs', m')) = (split1 fsn g, split1 fsn g')
      in
      case  map (== (deg h)) [0, deg g, deg f]
      of
      [True, _,    _   ] -> (f: hs, succ m)    -- f,g reciprocally prime
      [_,    True, True] -> (f: fs', n)                         -- f = g
      [_,    True, _   ] -> (f': g: fs', succ n) -- g divides f properly
      [_,    _,    True] -> (f: hs', succ m')    -- f divides g properly
      _                  -> (h: f': hs', m'+2)    -- non-trivial gcd f g 

------------------------------------------------------------------------
factorUPol_finField :: Field k => UPol k -> Factorization (UPol k)

  -- To factor  f  over a generic finite field  k,  
  -- look first into  dimOverPrimeField k.  
  -- If it is 1, apply  factorOverPrime.  Otherwise, set the 
  -- isomorphisms  toFromCanFinField  between  k  and canonic finite
  -- field  C = Zp[t]/(g),  map f to C[x],  factor over  C,  map the
  -- factorization back to  k[x].
  -- toFromCanFinField  needs in its turn, the primitive generator t
  -- for  k  over the prime field, accompanied with attributes. 
  -- Factorization over  C  is done by the generalized Berlekamp 
  -- method - see below  factorOverCanonic.

factorUPol_finField f = 
  let 
    (dK, v, un)  = (dom f, head $ pVars f, unity $ sample f)
    rK           = snd $ baseRing un dK
    (toC, fromC) = toFromCanFinField un rK
    dC        = isoDomains1 toC fromC dK
    toOverC g = UPol [(toC a, e)| (a, e)<- upolMons g] (toC un) v dC
                                                        -- k[x] <-> C[x]
    fromOverC g = ct f [(fromC b, e)| (b, e) <- upolMons g] 
  in
  case dimOverPrimeField rK
  of
  Fin 1 -> factorOverPrime f
  Fin _ -> [(fromOverC p, i) | (p, i)<- factorOverCanonic$ toOverC f]
  _     -> error ("\nfactorUPol_finField f," ++
                  (showsWithDom 1 f "f" "K[x]"
                   "dimOverPrimeField  has to be (Fin _) for K.\n"))

------------------------------------------------------------------------
factorOverCanonic ::
  UPol (RseUPolRse Integer) -> Factorization (UPol (RseUPolRse Integer))

  -- Factor  f <- k1[x]  for the canonic finite field  k1 = k[t]/I,
  -- I = (g),  g  irreducible over  k = Integer/(p).
  -- METHOD:
  -- generalized Berlekamp procedure: see [Me3,'ap.1'].
  -- See first  factorOverPrime.
  -- The difference to the case of a prime field is that  
  -- ker ((^p)-E)  is found by using the linear basis  [t^i*x^j|...]
  -- for  D = k1[x]/(f)   over  K.
  -- Denotation:  X = k1[x].

factorOverCanonic f =   
            if  isZero f  then  error $ msg "\nNon-zero  f  needed\n"
            else                concat $ map fts $ upolSqFree_finField f
  where
  msg = showString "\nfactorUPol_finField " . showsWithDom 1 f "f" ""

  fts (h, m) = [(g, m) | g <- factorSeparable h]
    where
    factorSeparable f = 
                  splitFactors f dimKer ([f], 1) $ map nonTrivGCDs kerB'
      where
      (dK1, unK1)     = (dom f, unity $ sample f)
      rK1             = snd $ baseRing unK1 dK1
      (Just p, opers) = (subringChar rK1, subringOpers rK1)
      Just wp         = lookup WithPrimeField opers
      ((frob, _), iI) = (frobenius wp, resPIdeal unK1)
      g          = pirCIBase iI                       -- g <- k[t]
      (m, r, un) = (deg g, deg f, unity $ sample g) 
      (zr, x1)   = (zeroS un, unity f)    
      (dX, fI)   = (upEucRing f Map.empty, eucIdeal "" f [] [] [])
      d1      = Rse x1 fI dX                  -- 1 of D = X/(f)
      (x, t') = (varP unK1 f, varP un g)  
      t       = ctr unK1 t'          
      kPols   = map (times x1) [0 .. (pred p)]     -- k in X
      tPowers = unK1: (map (t *) tPowers)
      xPowers = x1  : (map (x *) xPowers)         
      tPows   = genericTake m tPowers         -- 1..t^(m-1) in k1
      xPows   = genericTake r xPowers         -- 1..x^(r-1) in X
      ijs     = [(i, j) | j <- [0 .. (pred r)], i <- [0 .. (pred m)]]
                               -- for conversion X <-> vector over k
                           -- (Sum(ci*t^i))*x^j -> [(ci, (i,j)) | i<-..]
                           --                       serves the same need
      monToCijs (r, j) =
                      [(c'', (i, j)) | (c'', i) <- upolMons $ resRepr r]
      ------------------------------------------------------------------
      toVecK =  mv ijs . reverse . concat . map monToCijs . upolMons
          --
          -- Make vector over  k  from polynomial over over  k1 
          -- extracting coefficients and filling absent power
          -- positions with zeroes.  ijs acts like dense polynomial.
          where
          mv ijs       []               = map (const zr) ijs
          mv (ij: ijs) ((a, ij'): ij's) = 
                       if 
                          ij == ij'  then  a : (mv ijs ij's            )
                       else                zr: (mv ijs ((a, ij') :ij's))

                    -- Inverse to  toVecK.  It uses that ijs corresponds
                    --       to [aij*t^i*x^j ..]  ordered in certain way
      fromVecK xs =                  
               let mons' = filter ((/= zr) . fst) $ zip xs ijs
                   pairs = [((a, i), j) | (a, (i, j)) <- mons']
               in  
               ct f $ reverse $ monsOverK1 pairs
                    where    
                    monsOverK1 []                 = []
                    monsOverK1 ((monK, j): pairs) =  
                             let (ps, ps') = span ((== j) . snd) pairs
                                 monsK    = reverse (monK: (map fst ps))
                                 coefK1   = ct unK1 $ ct g monsK
                             in  (coefK1, j): (monsOverK1 ps')
      ------------------------------------------------------------------
                                           -- matrix for h^p-h in D over
                                           -- k,  h = (t^i*x^j mod f) .. 
      mM = transpose $ map toVecK
                                [(cPMul (frob t') x'p) - (cPMul t' x') |
                                 x' <- xPows, t' <- tPows, 
                                 let x'p = resRepr $ power (ct d1 x') p
                                ]
      kerB   = snd $ solveLinear_euc mM $ map (const zr) ijs
      dimKer = genLength kerB
      kerB'  = delBy eColl kerB    -- remove collinear to e vector
      eColl  = all (== zr) .tail
      nonTrivGCDs v = filter nonTrivDeg [gcD [f, h+a] | a <- kPols]
             where
             {h = fromVecK v;  nonTrivDeg = not . (`elem` [0, r]) . deg}


------------------------------------------------------------------------
instance Field a => FactorizationRing (UPol a)
  where
  -- For  Finite Field `a' only  - so far.
  -- In future, this condition will relax to  `Factorization a =>'
  -- SO FAR, -------------------------------------------------------
  -- DoCon performs the  polynomial factorization  and  primality
  -- test in  R[x1..xn]  only when 
  --                               n < 3  and  R  is a finite field.
  ------------------------------------------------------------------

  primes = primes_   
         --                        _ -> primes(1)++primes(2)++ ...,
         -- primes(i) = [g<- a[x]| g is prime, lc g = 1, deg g = i]
         -- See the local  primes_  below.

  factor f = (case Map.lookup Ring (dom f)
              of
              Just (D1Ring rC) -> ft (isField rC) (subringChar rC)
                                                  (dimOverPrimeField rC)
              _                -> error msg
             )
    where
    msg = "\nfactor f," ++ (showsWithDom 1 f "f" "K[x]"
          "Domain term of K must contain a Finite field description.\n")

    ft Yes (Just ch) (Fin _) = if ch > 0 then  factorUPol_finField f
                               else            error msg
    ft _   _         _       = error msg

  baseFactrRing f dm =
    (case
         (Map.lookup FactorizationRing dm, Map.lookup Ring (dom f))
     of
     (Just (D1FactrR r), _               ) -> (dm, r)
     (_,                 Just (D1Ring rC)) ->
                ftr (isField rC) (subringChar rC) (dimOverPrimeField rC)

     _                                     -> (dm, error msg)
    )
    where
    msg = "baseFactrRing f _," ++ (showsWithDom 1 f "f" "K[x]"
          "Domain term of K must contain a Finite field description.\n")

    ftr No    _        _        = (dm, error msg)
    ftr _     Nothing  _        = (dm, error msg)
    ftr _     (Just 0) _        = (dm, error msg)
    ftr _     _        Infinity = (dm, error msg)
    ftr isFld _        dimP     = 
                       (Map.insert FactorizationRing (D1FactrR r) dm, r)
         where
         r = FactrRingTerm {factrRingProps = [(WithFactor,    cond),
                                              (WithIsPrime,   cond), 
                                              (WithPrimeList, cond)]}
         cond          = and3 isFld (isFin dimP) 
         isFin (Fin _) = Yes
         isFin _       = Unknown
  

primes_ f = concat $ map (filter isPrime) $ monicUPols_overFin $
                                           varP (unity $ sample f) f





{- for future ******************************************************

-- Specialization of  UPol b  similar to the previous,
-- only  b  is represented as  ResidueI (UPol a)
-- TO BE CORRECTED:
instance Field a => FactorizationRing (UPol (ResidueI (UPol a))) where
  fctrRingAttributes (UPol _ c _ _ dK) = 
    let rC = baseRing c
      props' = [(WithIsPrime  , wIsP),  (WithFactor, wF),
                (WithPrimeList, No  ) -- SO FAR   ]
      wIsP = wF  -- SO FAR
      wF   = case  (vars, and3 (isField rC) (isFiniteRing rC))  of
               ([_],   Yes) -> Yes   (_:_:_, _  ) -> No
               (_    , No ) -> No   _            -> Unknown
    in  FctrRingAttributes {fctrRingProps = props'}
  primes f =  error "no  (primes f)  so far for a polynomial\n"
  factor  f@(Pol _ c cp vars) = let  (Rsi h iI)           = c
      (Pol _ c' cp' vars') = h    -- <- a[t]
      univariate_f = (genLength vars )==1
      univariate_h = (genLength vars')==1
      (rC',rC)     = (baseRing c', baseRing c)
      str = "(factor f)  for f<-(R[t..]/I)[x..]: "
    in  if  ( not univariate_f  ||  (isField rC)/=Yes 
          ||  (isFiniteRing rC)/=Yes  )
      then  error( "(factor (Pol..)):  only an univariate polyn"++
                   "omial over a finite field can handle so far\n")
    else case  (subringChar rC, isPrimeIfField rC, univariate_h) of
        (Just q, Yes, _   ) -> factorOverPrimeFinField_1_ q f
        (Just q, _  , True) -> let g = case  idealGens iI  
                of  Just [x] -> x;  _   ->
                  error (str++"\n R must be a finite prime\n "++
                        "field;  generators of kind [g] must"++
                        "be provided in I term\n")
                -- to use factorOverFinField_1_,  the coefficients
                -- of f must embed from  K = R[t]/g  represented 
                -- as              ResidueI (Pol a)  to K 
                -- represented as  ResidueE (Pol a) 
              gI      = eucIdeal "" g [g] [unity g] [(g,1)]
              toRse hr= Rse (fromRsi hr) gI              
              toRsi hr= Rsi (fromRse hr) iI   --back
              toOverRse (Pol mons c cp vs) = let  (cs,es)  = unzip mons
                                       (c':cs') = map toRse (c:cs)
                                  in   Pol (zip cs' es) c' cp vs
              toOverRsi (Pol mons c cp vs) =                --back
                                  let  (cs,es)  = unzip mons
                                       (c':cs') = map toRsi (c:cs)
                                  in   Pol (zip cs' es) c' cp vs
              factorsToOverRsi = map (\ (f,i)->(toOverRsi f,i)) --back
              fRse = toOverRse f  
            in  (case (isField rC',isFiniteRing rC',isPrimeIfField rC')
             of (Yes,Yes,Yes) -> factorsToOverRsi
                                    (factorOverFinField_1_ q fRse)
               _ -> error (str++"\nR must be a finite prime field\n")
            )
          _ ->
           error (str++"\n R must be a finite prime field, \n"++
                  "basis(I) must be [g] for an irreducible g,"++
                  "\n[t..] must be [t] \n")
-}
