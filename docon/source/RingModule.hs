------------------------------------------------------------------------
------------------------------------------------------------------------
--  The Algebraic Domain Constructor  DoCon,   version 2.12
--
--  Copyright  Serge Mechveliani,    2012
------------------------------------------------------------------------
------------------------------------------------------------------------





module RingModule

  -- Ring...GCDRing...Field, LeftModule, LinSolvLModule  categories.
  --
  -- This head module implements functions for Submodule,
  -- reexports some items from  Ring*_*

  (LeftModule(..), LinSolvLModule(..),
   isGxModule, isoModule, isoLinSolvModule,isoDomain22,isoDomains22,
   numOfNPrimesOverFin,
     -- instance Ring a          => LeftModule a a,
     -- instance Ring a          => LeftModule a (Vector a),
     -- instance EuclideanRing a => LinSolvLModule a (Vector a),

   -- from Ring0_:
     Ring(..), CommutativeRing(), OrderedRing(), GCDRing(..), 
   FactorizationRing(..), LinSolvRing(..), EuclideanRing(..), 
   Field(), RealField(), OrderedField(), 
     isFactorizOfPrime, isFactorizOfPrimary,
     property_Subring_list, fromi, char, props_Subring_zero,
   zeroSubring, dimOverPrimeField, isField, isPrimeIfField, 
     isOrderedRing, rankFromIdeal, isMaxIdeal, isPrimeIdeal, 
     isPrimaryIdeal, 
   genFactorizationsFromIdeal, zeroIdeal, unityIdeal,
     isGCDRing, isRingWithFactor, isGxRing, isEucRing, isCEucRing,
     upRing, upGCDRing, upFactorizationRing, upLinSolvRing, 
   upEucRing, upGCDLinSolvRing, upFactrLinSolvRing, 
   upEucFactrRing, upField, 

   -- from Ring_:
   eucGCDE, powersOfOne, logInt, diffRatios,  
   isoRing, isoGCDRingTerm, isoFactrRingTerm, 
   isoLinSolvRingTerm, isoEucRingTerm,  PIRChinIdeal(..), eucIdeal,
   isoDomain1, isoDomains1,

   -- from Ring1_:
   quotEuc, remEuc, multiplicity, isPowerOfNonInv, 
   gxBasisInEuc, moduloBasisInEuc, syzygyGensInEuc,
   moduloBasis_test, gxBasis_test, syzygyGens_test, gcd_test
  )

where
import qualified Data.Map as Map (empty, lookup, insert, map)

import Data.Maybe (fromJust)
import Data.List  (transpose)

import DPrelude (Length(..), -- class 
                 Natural, Z, PropValue(..), InfUnn(..), 
                 lookupProp, sum1, sublists, showsWithDom)
import Categs 
import SetGroup (AddGroup(..), MulSemigroup(..), zeroS, unity, inv,
                                                 factrzDif, unfactor)
import Ring0_   
import Ring_
import Ring1_
import VecMatr (vecSize, scalarMt, rowMatrMul)
import LinAlg  (reduceVec_euc, toStairMatr_euc, solveLinear_euc)





------------------------------------------------------------------------
class (Ring r, AddGroup a) => LeftModule r a
  where
  cMul           :: r -> a -> a                 -- module multiplication
  baseLeftModule :: 
                 (r, a) -> Domains2 r a -> (Domains2 r a, Submodule r a)
                 -- sa 


------------------------------------------------------------------------
class (LinSolvRing r, LeftModule r a) => LinSolvLModule r a
  where
  baseLinSolvLModule :: 
         (r, a) -> Domains2 r a -> (Domains2 r a, LinSolvModuleTerm r a)
                          --
                          -- all these operations have a sample argument
  canAssocM    :: r -> a -> a                      
  canInvM      :: r -> a -> r                      
  gxBasisM     :: r -> [a] -> ([a], [[r]])          
  moduloBasisM :: r -> String -> [a] -> a -> (a, [r])
  syzygyGensM  :: r -> String -> [a] -> [[r]] 


isGxModule :: LinSolvModuleTerm r a -> PropValue
isGxModule (LinSolvModuleTerm ps) =  lookupProp IsGxModule ps


isoModule :: (a -> b) -> (b -> a) -> Submodule r a -> Submodule r b
isoModule    f           _           mM            =
  let
    gens' = case moduleGens mM of Nothing -> Nothing
                                  Just gs -> Just $ map f gs
  in
  Submodule {moduleRank     = moduleRank mM,
             moduleGens     = gens',
             moduleProps    = moduleProps mM,
             moduleGenProps = moduleGenProps mM,
             moduleConstrs  = [],  -- so far
             moduleOpers    = []   --
            }

isoLinSolvModule :: (a -> b) -> (b -> a) -> LinSolvModuleTerm r a ->
                                            LinSolvModuleTerm r b
isoLinSolvModule _ _ mM = LinSolvModuleTerm 
                            {linSolvModuleProps = linSolvModuleProps mM}

------------------------------------------------------------------------
isoDomain22 :: (a -> b) -> (b -> a) -> Domain2 c a -> Domain2 c b
isoDomain22    f           f'          dom         =
  case  dom
  of
  D2Module   t -> D2Module   $ isoModule        f f' t
  D2LinSolvM t -> D2LinSolvM $ isoLinSolvModule f f' t


isoDomains22 :: (a -> b) -> (b -> a) -> Domains2 c a -> Domains2 c b
isoDomains22    f           f'       =  Map.map (isoDomain22 f f')


------------------------------------------------------------------------
instance Ring a => LeftModule a a  
  where  
  cMul = mul

  baseLeftModule (a, _) dom = 
    case Map.lookup LeftModule dom 
    of
    Just (D2Module t) -> (dom, t)
    _                 -> (Map.insert LeftModule (D2Module t) dom, t)
      where
      t = Submodule {moduleRank     = Fin 1,
                     moduleGens     = Just [unity a],
                     moduleProps    = props,
                     moduleGenProps = genProps,
                     moduleConstrs  = [],
                     moduleOpers    = []
                    }
      props  = [(IsFreeModule,       Yes  ), 
                (IsPrimeSubmodule,   No   ),
                                          -- because it is the full ring
                (IsPrimarySubmodule, No   ), --
                (IsMaxSubmodule,     No   ), --
                (HasZeroDivModule,   hasZD),
                (IsGradedModule,     No   )  -- so far
               ]
      genProps = [(IsFreeModuleBasis, Yes), (IsGxBasisM, Yes)]
      hasZD    = lookupProp HasZeroDiv propsA
      propsA   = subringProps$ snd $ baseRing a Map.empty


-- instance (AddGroup a) => LeftModule Integer a  where  
--                                                cMul = flip times
-- Haskell-2-pre  cannot solve this overlap with
-- instance Ring a => LeftModule a a  


------------------------------------------------------------------------
instance Ring a => LeftModule a (Vector a) 
  where  
  cMul a = fmap (a *) 

  baseLeftModule  (a, v@(Vec xs))  dom =
    case  
        (Map.lookup LeftModule dom, snd $ baseRing a Map.empty)
    of
    (Just (D2Module t), _ ) -> (dom, t)
    (_,                 aR) -> 
                             (Map.insert LeftModule (D2Module t) dom, t)
        where
        t = Submodule {moduleRank     = Fin $ vecSize v,
                       moduleGens     = gens,
                       moduleProps    = props,
                       moduleGenProps = genProps,
                       moduleConstrs  = [],
                       moduleOpers    = []
                      }
        genProps = [(IsFreeModuleBasis, Yes), (IsGxBasisM, Unknown)]

        props = [(IsFreeModule,       Yes  ), 
                 (IsPrimeSubmodule,   No   ),
                                       -- for it is the full module
                 (IsPrimarySubmodule, No   ), --
                 (IsMaxSubmodule    , No   ), --
                 (HasZeroDivModule,   hasZD),
                 (IsGradedModule,     No   )  -- so far
                ]
        hasZD  = lookupProp HasZeroDiv propsA
        propsA = subringProps aR
        gens   = Just $ map Vec $ scalarMt xs u z
        (z, u) = (zeroS a, unity a)


--------------------------------------------------------------------
-- For an Euclidean `a',  the  LinSolvLModule  structure 
-- on Vector a  bases on the Gauss reduction for the matrices over
-- `a'  - see  toStairMatr_euc.

instance EuclideanRing a => LinSolvLModule a (Vector a)
  where  
  canAssocM a (Vec xs) = Vec $ canas xs
    where                       
    zr = zeroS a
    canas []      = []
    canas (x: xs) = if x == zr then  x: (canas xs)
                    else             map (f *) (x: xs)
                                                   where  
                                                   f = inv $ canInv x
  canInvM a (Vec xs) = let z = zeroS a 
                       in
                       case dropWhile (== z) xs of  x: _ -> canInv x
                                                    _    -> unity a
  gxBasisM a vs =  
               let zr          = zeroS a
                   nonZeroV    = any (/= zr)
                   (mS, mT, _) = toStairMatr_euc ""  (map vecRepr vs) []
                   (rs, ts, _) = toStairMatr_euc "u" mS mT
                   gs          = map Vec $ takeWhile nonZeroV rs
                in (gs, map fst $ zip ts gs)

  syzygyGensM a mode vs = 
    case 
        (map vecRepr vs, zeroS a)  
    of
    ([],    _) -> error $ msg "\nvectors =  []  <- Vector R.\n"
    ([]: _, _) -> error $ msg "\nvectors =  (Vec []):_   <- Vector R \n"
    (xs: xss, z) -> snd $ solveLinear_euc (transpose (xs: xss)) $ 
                                                     map (const z) xs
    where  
    msg = showString ("\nsyzygyGensM sample " ++ (mode ++ " vectors")) .
          showsWithDom 1 a "sample" "R" 

  moduloBasisM a mode vs v =    -- mode = "" | "c" | "g" | "cg"
    let
      zr      = zeroS a
      cMode   = if  elem 'c' mode  then 'c' else '_'
      isGxB   = (genLength vs) < 2 || (elem 'g' mode)
      reduce  = reduceVec_euc cMode 
      v': vs' = map vecRepr (v: vs)
    in
    if  any (\ x -> not $ elem x "gc") mode  then
        error $ 
        showString ("\nmoduloBasisM sample " ++ (mode ++ " vs v,")) $
        showsWithDom 1 a "sample" "R" $
        showsWithDom 1 v "v" "Vector R"
                 "\nmode may be only \"\",  \"c\",  \"g\",  \"cg\" \n"
    else
    case (isGxB, gxBasisM a vs)
    of
    (True, _       ) -> (Vec r, qs)  where (r, qs) = reduce vs' v'
    (_,    (gs, mt)) -> case (gs, reduce (map vecRepr gs) v') 
                        of
                        ([], _      ) -> (v,     map (const zr) vs)
                        (_ , (r, qs)) -> (Vec r, rowMatrMul qs mt )

  baseLinSolvLModule (a, v) vdom =
    case 
        (Map.lookup LinSolvLModule vdom, baseGCDRing a Map.empty)
    of                   
    (Just (D2LinSolvM m), _       ) -> (vdom, m)
    (_,                   (dA, gR)) ->
        let
          eR           = snd $ baseEucRing a dA
          gProps       = gcdRingProps gR 
          eProps       = eucRingProps eR 
          wCnAs        = lookupProp WithCanAssoc gProps
          [isE, wCRem] =
                     [lookupProp p eProps | p <- [Euclidean, DivRemCan]]
          m = LinSolvModuleTerm
              {linSolvModuleProps = [(IsCanAssocModule,       wCnAs),
                                     (ModuloBasisDetaching_M, isE  ),
                                     (ModuloBasisCanonic_M,   wCRem),
                                     (WithSyzygyGens_M,       isE  ),
                                     (IsGxModule,             wCRem)]}
        in
        case isE 
        of
        No -> (vdom, 
               error $ 
                 showString "\nbaseLinSolvLModule (a, vec) vdom," $
                 showsWithDom 1 a "a"   "R"        $
                 showsWithDom 1 v "vec" "Vector R" $
                                  "\nisEucRing R  yielded  No\n"
              )
        _  -> (Map.insert LinSolvLModule (D2LinSolvM m) vdom, m)



------------------------------------------------------------------------
numOfNPrimesOverFin :: Natural -> Factorization Integer -> Integer
                       -- q       dFtn
-- Number  N  of prime, normed polynomials of degree  d  in Fq[x],
-- Fq  any finite field (of q = p^s  elements),
-- d  given by its factorization  dFtn  (with 1 <--> []).
-- METHOD.
-- We take this combinatorics from [La], chapter 7, exercises 1,2:
-- 
--         N = (sum [(moebius e)*q^(d/e) | e divides d]) / d
-- 
-- Naturally, e represents as a sublist el of prime factors in  d.
-- And moebius e  is non-zero only when el is free of repetitions.

numOfNPrimesOverFin q dFtn 
 
  | q < 2     = error $ showString "\nnumOfNPrimesOverFin " $ 
                        shows q $ showChar ' ' $ shows dFtn 
                        "\nq > 1 required, it is a field cardinality.\n"
  | null dFtn = q   -- number of x + a, a <- K
  | otherwise =
    let
      (dps, d) = (map fst dFtn, unfactor dFtn)
      eFtns    = 
             [zip xs $ repeat 1 :: Factorization Z | xs <- sublists dps]
                                            -- factorizations for all  e
      dQuot eFtn = {- d/e -} case  fromJust$ factrzDif dFtn eFtn  of
                                                        [] -> 1
                                                        f  -> unfactor f
      qPows   = map ((q^) . dQuot) eFtns
      moeb xs = if  even $ genLength xs  then  1  else  -1
      s       = sum1 $ zipWith (*) qPows$ map moeb eFtns
    in
    case  divide_m s d
    of
    Just s' -> s'
    _       -> error $ concat 
               ["\nnumOfNPrimesOverFin ", shows q "dFtn,\ndFtn = ", 
                shows dFtn "\n - MoebiusSum/d  failed.\nProbably, a \
                      \wrong factorization  dFtn  for  d  is given.\n"]
              
