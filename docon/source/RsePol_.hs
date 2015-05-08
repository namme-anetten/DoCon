------------------------------------------------------------------------
------------------------------------------------------------------------
--  The Algebraic Domain Constructor  DoCon,   version 2.12
--
--  Copyright  Serge Mechveliani,    2012
------------------------------------------------------------------------
------------------------------------------------------------------------






module RsePol_        -- Continuation for  RsePol0_. 
                      -- All needed from here is reexported by  Residue.
  (module RsePol0_,
   maxDimMonSubAlgInRseUPolRseUPol   
   -- , Ring  instance
  )
where
import qualified Data.Map as Map (empty, lookup, insert)
 
import Data.List (genericTake)

import DPrelude (Natural, PropValue(..), InfUnn(..),  fmapfmap, ct, ctr, 
                                                           showsWithDom)
import Categs 
import SetGroup
import RingModule (Ring(..), GCDRing(..), Field(), 
                                       isField, upEucFactrRing, upField)
import VecMatr (mainMtDiag)
import UPol_ (PolLike(..), UPol(..), upolMons, lc0, varP, cToUPol, 
                                              cPMul, monicUPols_overFin)
import ResEuc0_ (Residue(..))
import ResEuc1_ (rseBaseRing)
import RsePol0_    
import Pfact__ (RseUPol, toFromCanFinField    )
import VecMatr (rowMatrMul                    )
import LinAlg  (reduceVec_euc, toStairMatr_euc)





------------------------------------------------------------------------
instance Field a => Ring (ResidueE (UPol a))
                                            -- old: , GCDRing (UPol a)..   
  where
  fromi_m r = fmap (ct r) . fromi_m (resRepr r)
 
  baseRing  r@(Rse f iI _)  dm = 
    case  
        (Map.lookup Ring dm, pirCIBase iI, sample f, dom f)
    of
    (Just (D1Ring rg), _, _, _ ) -> (dm, rg)
    (_,                g, a, aD) ->
      (case
           (Map.lookup Ring aD, rseBaseRing r dm, zeroS a, unity a)
       of
       (Just (D1Ring aR), (dm',rR'), zr, un) ->
                             br (deg g) zr un aR dm' rR' (pirCIFactz iI)
       _ -> (dm, error $ msg msg1)
      )
      -- Denotations:  R = a[x]/(g),
      -- first R' builds for A/(g) as for generic Euclidean A
      where
      msg = showString "\nbaseRing r rdom," . 
                           showsWithDom 1 r "r" "a[_]/I" . showChar '\n'
      msg1 = "\nRing not found in  a.\n"
      msgFrChar  = "WithPrimeField ... Frobenus map:\n" ++
                   "non-zero characteristic needed.\n"
      msgPrimFin = "WithPrimeField ... PrimitiveOverPrime:\n" ++
                   "so far, only the case  Finite(a)  can do.\n"

      br degG zr un aR dm' rR' factrz =  
        case 
            isField aR 
        of
        No       -> (dm, error $ msg $ msgField "a")
        aIsfield -> (Map.insert Ring (D1Ring rg) dm', rg)
          where
          rg = Subring {subringChar    = ch,  
                        subringGens    = gens',
                        subringProps   = subringProps rR', 
                        subringConstrs = [],
                        subringOpers   = opers'}
           where
           (r0, r1, ch) = (zeroS r, unity r, subringChar aR)
           x        = varP un f              -- x  in A,
           xr       = ctr r x                --    in R
           xrPowers = xr: (map (xr *) xrPowers)
           xrPows   = genericTake (pred degG) xrPowers
           aToR  = ct r . ct f                    -- a\{0} -> R
           gens' = case (aIsfield, subringGens aR) 
                   of                     -- if `as' generates aR', then
                                          -- [a*x | a <- as] generates R
                   (Yes, Just as) -> Just [ct r $ cPMul a x | a <- as]
                   _              -> Nothing
           -------------------------------------------------------------
           -- For  opers',  DoCon  is so far interested in the
           -- WithPrimeField  construction:
           -- prime field  PF  inside `a',  representation of
           -- rR = a[xr]/(g)  as  PF[y]/(g') ...

           opers' = 
             (case (aIsfield, lookup WithPrimeField$ subringOpers aR)
              of
              (Yes, Just wp) -> [(WithPrimeField, wp' wp)]
              _              -> []
             )
             where                       -- Lengthy thing! Sorry.
             wp' wp = WithPrimeField' 
                      {frobenius            = fr',
                       dimOverPrime         = dimOP',
                       primeFieldToZ        = toz',
                       primeFieldToRational = tor',
                       primitiveOverPrime   = primOP'}
               where
               dimOP  = dimOverPrime wp
               dimOP' = case dimOP of Fin d -> Fin (d*degG)
                                      v     -> v
               toz' = primeFieldToZ wp        . lc0 zr . resRepr
               tor' = primeFieldToRational wp . lc0 zr . resRepr

               fr' = 
                 case (ch, frobenius wp) 
                 of
                 (Nothing, _         ) -> error $ msg msgFrChar
                 (Just 0, _          ) -> error $ msg msgFrChar
                 (Just p, (pp, ppInv)) -> (pp', ppInv')
                    where
                    pp' = if degG == 1 then   
                                   ct r . ctr f . pp . lc0 zr . resRepr
                          else    horner . reverse . upolMons . resRepr

                    xp = ctr r $ ct f (un, p)   -- x^p in R
                        
                    horner []           = r0
                    horner ((c, e): ms) = 
                             let {c' = aToR $ pp c;  xpe = power xp e}
                             in
                             xpe*(c'+(horner [(b, d-e) | (b, d) <- ms]))

                    ppInv' r = 
                      case (r == r0 || r == r1, degG, dimOP)  
                      of
                      (True, _, _       ) -> Just $ Just r
                      (_,    1, _       ) -> fmapfmap (ct r . ctr f) $ 
                                             ppInv $ lc0 zr $ resRepr r
                      (_,    _, UnknownV) -> Nothing
                      (_,    _, Infinity) -> Nothing
                      _                   ->
                        -- If g is given as square free, dimOP  is 
                        -- finite, then (^p) can be inversed in  R by
                        -- repeating (^p).  For in this case  R  is a
                        -- direct sum of fields K(i) and in each K(i), 
                        -- (^p) generates the automorphism group of
                        -- order  dim(K(i),PF).
                        -- (more generic way is possible: solving linear
                        --                            system over PF...)
                        if not $ isSquareFreeFactrz factrz  then 
                                                            Nothing
                        else  inve r (pp' r)
                          where  
                          inve r' rp = if rp == r then Just $ Just r'
                                       else            inve rp (pp' rp)

                              -- forming primitive generator (y, gg) for
                              -- PF--R  starting from (t,h) for PF--`a'
                              --                  and (xr,g) for `a'--R.

               (tPows, tMinP, inT) = primitiveOverPrime wp
               primOP' = 
                 case (tPows, degG, tMinP, dimOP) 
                 of
                 ([], _, _ , _       ) -> ([], [], const []) 
                                                          -- t not found
                 (_,  1, _ , _       ) ->    -- case R isomorphic to `a'
                          (map aToR tPows,
                           [(aToR a, e) | (a, e) <- tMinP],
                           \ r' -> [(aToR a, e) | 
                                    (a, e) <- inT $ lc0 zr $ resRepr r']
                          )
                 (_,  _, [], _       ) -> ([], [], const []) 
                                             -- here we do only the case
                                             -- of finite `a' - SO FAR
                 (_,  _, _,  UnknownV) -> error $ msg msgPrimFin 
                 (_,  _, _,  Infinity) -> error $ msg msgPrimFin
                 (_,  _, _,  Fin 1   ) ->        -- case  a = PF:  xr is
                      (xrPows,                   -- the neened primitive
                       [(aToR a, e) | (a, e) <- upolMons g],
                       \r -> [(aToR a, e)| (a, e)<- upolMons$ resRepr r]
                      )
                 _ -> if n < dimR then 
                               ([], [], error "no primitive element.\n")
                      else     (map fromC $ tail y'Pows,  minY,  inY)
                   --
                   -- Generic finite(a) case. Map `a' to canonic field
                   -- K = Zp[t]/(h'),  R to  C = X'/(g'),  X' = K[x], 
                   -- find primitive for  Zp -- C,  and map back to  R
                                                              -- a <-> K
                   where
                   (toK, fromK) = toFromCanFinField un aR 
                   unK       = toK un
                   dK        = upField unK Map.empty
                   x'1       = cToUPol "x" dK unK    -- 1 of X'
                   dX'       = upEucFactrRing x'1 Map.empty
                   toOverK h = UPol [(toK a, e) | (a, e) <- upolMons h]
                                    unK "x" dK          -- 
                   fromOverK h =                        -- a[x] <-> K[x]
                              ct f [(fromK a, e) | (a, e) <- upolMons h]
                   g'I   = fmap toOverK iI
                   c1    = Rse x'1 g'I dX'
                   toC   = ct c1 . toOverK   . resRepr   -- R <-> 
                   fromC = ct r  . fromOverK . resRepr   --      C
                   overZpToOverR mons =
                             [(times r1 $ resRepr a, e) | (a, e)<- mons]
                                                        -- Zp[y] -> R[y]
                   (n, (y'Pows, _, _, inY')) =
                                      maxDimMonSubAlgInRseUPolRseUPol c1
                   y' = head $ tail y'Pows 
                                         -- find minimalPolynomial(y,PF)
                   minYTl   = overZpToOverR $ inY' (y'*(last y'Pows))
                   minY     = (r1, n): [(-a, e) | (a, e) <- minYTl]
                   inY      = overZpToOverR . inY' . toC
                   Fin dimR = dimOP'


------------------------------------------------------------------------
maxDimMonSubAlgInRseUPolRseUPol ::
             --OI **
   (Field k, GCDRing (UPol k)) =>
   RseUPol (RseUPol k) ->                                   -- xg1
                         (Natural,                          -- n
                          ([RseUPol (RseUPol k)],           -- yPows
                           [[k]],                           -- mS
                           [[k]],                           -- mT
                           RseUPol (RseUPol k) -> [UMon k]  -- inY
                          )
                         )
-- For a finite field K,  K-algebra  XG = (K[t]/(h))[x]/(g),
-- given by its sample unity element  xg1,  lc g = lc h = 1,
-- find any element  y  in XG that generates the sub-algebra over  K  of
-- hightest possible dimension  n.
-- yPows = [y^i | i <- [0..n-1]  is the linear basis over K of
--                                                        subAlgebra(y).
-- mT  is the matrix transforming  mY  to staircase form  mS:
--     mT*mY = mS,
--     mY  is  yPows  written in basis [t^i*x^j|..] of XG over  K.
-- inY  expresses each element of  subAlgebra(y)  as polynomial in  y
--                                  over  K  (yields list of monomials).
-- mT, mS  help to define  toY.
-- Denotations:  T= K[t], TH= K[t]/(h), X = TH[x], XG = TH[x]/(g).
-- Property:
-- if  XG  is generated by some primitive over  K  element 
-- (this holds, for example, when  h is irreducible over K  and  g 
-- is irreducible over TH), then
--                XG = K(y),  mT = inverse mY,  inY is valid on all XG.
-- METHOD.
-- So far, it is rather stupid: generate by  monicUPols_overFin x all
-- monic polynomials f over TH,  deg f <- [1..(deg g)-1].
-- For each  r = (f mod g)  find "first" linear dependence over K for
-- 1, r, r^2 ..., and so, minimal polynomial of  r  over  K  and
-- n = dim(r) = dim (subAlgebra(r), K).  Choose r  of maximal  n.
-- It holds  n <= dimXG = (deg h)*(deg g).  Therefore, if  n  reaches 
-- dimXG,  the search stops.
-- When finding subAlgebra(r),  the current power list  rPows  and the 
-- current  mT  to transform to staircase form  mS  are maintained. When 
-- there appears zero new line to join  mS,  it means that  rPows, mS  
-- are the bases for  subAlgebra(r).  
-- COST:
-- on average, not very large. Because the primitive elements occur 
-- quite often. They are expected to meet among rather small degrees.
 
maxDimMonSubAlgInRseUPolRseUPol xg1 = 
              maxSA (monicSubAlgebra 1 (ctr xg1 x) [xg1] [x1V] [[un]]) $
              monicUPols_overFin x
  where
  (x1, g)     = (resRepr xg1, pirCIBase $ resPIdeal xg1)
  (th1, degG) = (unity $ sample x1, deg g)
  (t1, h)   = (resRepr th1, pirCIBase $ resPIdeal th1)
  (x, degH) = (varP th1 x1, deg h)
  dimXG     = degH*degG
  (zr, un)  = (zeroS $ sample t1, unity $ sample t1)  -- 0, 1 of K

  ijs = [(i, j) | j <- [0 .. (pred degG)], i <- [0 .. (pred degH)]]
                                   -- for conversion X <-> vector over K.
                              -- (Sum(ci*t^i))*x^j -> [(ci,(i,j))| i<-..]
                              --                         serves same need
  monToCijs (r, j) = [(c, (i, j))| (c, i) <- upolMons $ resRepr r]

  toVecK = mv ijs . reverse . concat . map monToCijs . upolMons
                  -- Make vector over  K  from polynomial over  TH
                  -- extracting coefficients and filling absent power
                  -- positions with zeroes.  ijs models dense polynomial.
       where
       mv ijs       []               = map (const zr) ijs
       mv (ij: ijs) ((a, ij'): ij's) =
                         if ij == ij' then a : (mv ijs ij's            )
                         else              zr: (mv ijs ((a, ij') :ij's))
  x1V = toVecK x1
  ----------------------------------------------------------------------
  monicSubAlgebra n r rPows mS mT =     -- mT x matr(rPows) = mS
      let                               -- mS is staircase. 
        r'  = r*(head rPows)            -- Add powers of r reduced by mS
        v'  = toVecK $ resRepr r'
        row = un: (map (const zr) $ head mT)
        mT1 = row: (map (zr:) mT)        -- mT1*matr(r': rPows) = v': mS
        (mS', mT', _) = toStairMatr_euc "" (v': mS) mT1
      in
      if n == dimXG || all (== zr) (last mS')  then  (n, (rPows, mS, mT))
      else                 monicSubAlgebra (succ n) r (r': rPows) mS' mT' 
  -----------------------------------------------------------------------
  maxSA (n, tripl) (fs: fss) =    -- Elements  r(f)  in  XG   are
    (case                         -- represented by polynomials f from X.
         (n == dimXG, fs)         -- Search  r  with maximal
     of                           --            dim Lin(powersOf r, K).
     (True, _     ) -> (n, toE tripl)
     (_,    []    ) -> maxSA (n, tripl) fss
     (_,    f: fs') ->
               if  deg f == degG  then  (n, toE tripl)
               else
               case  monicSubAlgebra 1 (ct xg1 f) [xg1] [x1V] [[un]]
               of
               (m, trp) -> if n < m then  maxSA (m, trp  ) (fs': fss)
                           else           maxSA (n, tripl) (fs': fss)
    )
    where
    toE (ps, mS, mT) = (reverse ps, mS', reverse mT', inY)
        where
        -- Try to bring  mS  further, to diagonal or maybe, to unity
        -- matrix. If  isField XG  then  mS' is unity.
        -- It also reverses the basis to  [1..y^(n-1)]  and adds the map
        --                                                          inY.
        (mS1, mT1, _) = toStairMatr_euc "u" mS mT
        (mS', mT')    = unzip $ zipWith3 mulIfJust 
                                    (map inv_m $ mainMtDiag mS1) mS1 mT1
        mulIfJust (Just a) rowS rowT = (map (a *) rowS, map (a *) rowT)
        mulIfJust _        rowS rowT = (rowS, rowT)
        inY r = let as = toVecK $ resRepr r
                    bs = if n == dimXG then  as 
                         else             snd $ reduceVec_euc '_' mS' as
                in   
                upolMons $ pFromVec h $ rowMatrMul bs mT'
