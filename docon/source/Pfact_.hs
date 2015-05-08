------------------------------------------------------------------------
------------------------------------------------------------------------
--  The Algebraic Domain Constructor  DoCon,   version 2.12
--
--  Copyright  Serge Mechveliani,    2012
------------------------------------------------------------------------
------------------------------------------------------------------------



module Pfact_ (upolSqFree_char0_, upolSqFree_finField) 

-- Starting polynomial factorization.
-- Case  k[x], k a finite field.
-- Implementation support for the instance  FactorizationRing a[x]
-- All needed from here is  reexported by  Pol.
where
import DPrelude   (InfUnn(..), ct, showsWithDom) 
import Categs     (Dom(..), Subring(..), Factorization)
import SetGroup   (isZero)
import RingModule (Ring(..), GCDRing(..), Field(), multiplicity,
                                                   dimOverPrimeField)
import UPol_ (PolLike(..), UPol(..), lc, pCont, upolMons)
import Pgcd_ ()
import Pol1_ ()




------------------------------------------------------------------------
upolSqFree_char0_ :: GCDRing a => UPol a -> Factorization (UPol a)
  -- LOCAL.
  -- Square free decomposition of              f <- a[x]
  -- over a GCD-ring `a' of characteristic 0:  f -> [(f1,1)..(fm,m)]
  -- Here
  --   canAssoc(f/(content f)) =  f1^1*..*fm^m,
  --   canAssoc  means division by the canonical invertible factor
  --             (in the field case, by lc(f)),
  --   each  fi  is square free  &  gcd(fi,fj) = 1  for i/=j,
  -- constant  fi  are skipped, in particular,  []  is returned for 
  -- the constant  f.

upolSqFree_char0_ f = 
  if
    isZero f  then  []
  else              [(canAssoc f, i)| (f, i) <- sqFree $ canAssoc f1]
  where
  f1 = case pCDiv f $ pCont f
       of
       Just q -> q
       _      -> error ("\nupolSqFree_char0_ f," ++
                        (showsWithDom 1 f "f" "" 
                                "\npCDiv f (pCont f) = Nothing  - ?\n"))
  sqFree f = 
         case deg f  
         of               -- here f is non-zero
         0 -> []
         1 -> [(f, 1)]
         _ -> let  f'= pDeriv [(1, 1)] f   -- df/dx
                   g = gcD [f, f']
              in  
              if deg g == 0 then  [(f, 1)]
              else                incrMultiplicities (f/g) (sqFree g)
              where   
                        -- below  h = f1*..*fm,  
                        -- `pairs' contains some of  (f(ik),jk),  jk > 0
              incrMultiplicities h pairs = 
                 case  
                     (deg h, pairs)
                 of
                 (0, _          ) -> pairs
                 (_, []         ) -> [(h, 1)]
                 (_, (fi, j): ps) ->
                            (fi, succ j): (incrMultiplicities (h/fi) ps)


------------------------------------------------------------------------
upolSqFree_finField :: Field k1 => UPol k1 -> Factorization (UPol k1)
  -- LOCAL.
  -- Square freeing in  k1[x],  k1  any finite field. 
  -- Denotations:  p   = char k1,   k  a prime field inside  k1,
  --               dim = dim_k k1.
  -- METHOD.
  -- See [Me3,'ap.sq1'].  Briefly: apply  f'= d/dx f,  gcd f f' ...
  -- If f' = 0 then the exponents are the multiples of  p,
  -- each coefficient  c  is  c'^p,  and  f = g^p.
  -- c'  is found by repeating (^p) isomorphism in  k1:
  -- recall that  (^(p^dim)) = id  in  k1.

upolSqFree_finField f =  
  (case  
       (isZero f, pCDiv f $ lc f)
   of
   (True, _      ) -> []  
   (_,    Just f1) -> [(canAssoc g, j) | (g, j) <- sf f1]
   _               -> 
             error $ msg $
             showsWithDom 1 f "f" "" "\npCDiv f (lc f) = Nothing  - ?\n"
  )
  where
  msg               = showString "\nupolSqFree_finField f,"
  rK1               = snd $ baseRing (sample f) (dom f)
  (Just p, Fin dim) = (subringChar rK1, dimOverPrimeField rK1)
  sf f =
    let (cs, es)      = unzip $ upolMons f
        (quots, rems) = unzip [quotRem n p | n <- es]
    in
    case (deg f, p < 2)
    of               
    (0, _   ) -> []
    (1, _   ) -> [(f, 1)]
    (_, True) -> error $ msg $ showString "\n...sf f1," $
                      showsWithDom 1 f "f1" "" "\nchar k1 < 2  - why?\n"
    _         -> 
        if  all (== 0) rems    -- f = h1(x^p)
        then          
            let cRoots = if  dim < 2  then  cs
                          else              map (root_p p) cs
                mons'  = zip cRoots quots  -- h1 = Sum (ci'*x^(i/p))
                h1     = ct f mons'
            in  [(fi, ki*p) | (fi, ki) <- sf h1]
        else
        let {f' = pDeriv [(1, 1)] f;  gc = gcD [f, f']}
        in  
        if deg gc == 0 then [(f, 1)]  else  sf' (f/gc) $ sf gc

  sf' h pairs = 
    case (deg h, pairs) 
    of 
    (0, _          ) -> pairs
    (_, []         ) -> [(h, 1)]
    (_, (fi, i): ps) -> let {h1 = gcD [h, fi];  ffi = fi/h1}
                        in
                        if  deg h1 == 0  then  (fi, i): (sf' h ps)
                        else
                        let (k, hh) = multiplicity h1 h  -- hh= h/(h1^k)
                            tl      = (h1, k+i): (sf' hh ps)
                        in
                        if deg ffi == 0 then  tl  else  (ffi, i): tl
  
------------------------------------------------------------------------
root_p :: Field k1 => Integer -> k1 -> k1  
                                        -- For a finite field of char p.
root_p p b = r b (b^p)                  -- k1--> k1, b -> b':  b'^p = b
                      where
                      r b' bp = if bp == b then  b'  else  r bp (bp^p)



{- not ready *************************************
polSqFree_finField :: (Field k1) => Pol k1 -> Factorization (Pol k1)
  -- generalizes  upolSqFree_finField  to  n  variables
polSqFree_finField  f@(Pol mons a o vars dK1) =  
  let  n                 = genLength vars
    (lexn, rK1)       = (lexPPO n, snd $ baseRing a dK1)
    (Just p, Fin dim) = (subringChar rK1, dimOverPrimeField rK1)
    fl                = reordPol lexn $ canAssoc f
    ----------------------------------------------------------------
                             -- it starts with non-constant monic f,
    sf f =                   -- in  lexPPO order,  n > 1
      if  pIsConst f  then  [] else
        let  n        = genLength $ polVars f
             (cs,pps) = unzip $ polMons f
        in  case  dropWhile (all (divides p) . vecRepr) pps  of
          []         ->                       -- f = h1(x1^p...xn^p)
            let cRoots = if dim < 2 then cs  else  map (root_p p) cs
                mons'  = zip cRoots
                          [Vec [quot j p | j <- js] | Vec js <- pps]
                h1   = ct f mons'  in  [(fi, ki*p) | (fi,ki) <- sf h1]
          (Vec js):_ -> 
            let m = succ $ genLength $ takeWhile (divides q) js 
                                                    -- df/dx(m) /= 0
            in if  m == 1  
              then     let  fU = headVarPol dr f
                  fr = removeHeadVar f;   dr = upGCDRing fr eFM
                  c  = pCont fU;    v  = head $ pVars f
                  fUq  = fromJust $ pCDiv fU c
                  fUq' = pDeriv [(1,1)] fUq
                  gc   = gcD [fUq,fUq']       
                             --Chinese method needed for efficiency!
                  fsq =  gather
                      (polSqFree_FinField $ fromHeadVarPol gc)
                      (polSqFree_FinField $ fromHeadVarPol (fUq/gc)) 
                in gather [(prependHeadVar v g, i) | 
                                   (g,i) <- polSqFree_FinField c] fsq 
    ----------------------------------------------------------------
  in case  (p < 2, pIsConst f, n)  of
    (True, _   , _) -> error $ msg $ ("\n...sf f1,"++) $
                    showsWithDom f "f1" "" "\nchar k1 < 2  - why?\n"
    (_   , True, _) -> []
    (_   , _   , 1) -> [(reordPol o $ fromUPol g, i) |
                             (g,i) <- upolSqFree_finField $ toUPol f]
    _               -> [(reordPol o g, i) | (g,i) <- sf fl] 
  **************************************
-}

