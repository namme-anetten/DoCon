------------------------------------------------------------------------
------------------------------------------------------------------------
--  The Algebraic Domain Constructor  DoCon,   version 2.12
--
--  Copyright  Serge Mechveliani,    2012
------------------------------------------------------------------------
------------------------------------------------------------------------





module RsePol0_   -- All needed from here is  reexported by  Residue.
(
 msgField
 -- , Specialization of R/(g), R Euclidean, to R = k[x], k a Field:
 -- Field k => ResidueE (UPol k).
 -- Instances up to  AddGroup, MulSemigroup
)
where
import qualified Data.Map as Map (lookup, insert) 

import Data.List (delete)

import DPrelude (PropValue(..), InfUnn(..), Comparison, ct, ctr, 
                 lookupProp, showsWithDom)
import Categs 
import SetGroup
import RingModule (Field(), isField)
import UPol_      (PolLike(..), UPol(..), upolMons, varP, cPMul, 
                                          pmul, monicUPols_overFin)
import Pol2_      ()
import ResEuc0_   (Residue(..)        )
import ResEuc1_   (rseBaseMulSemigroup)
import qualified ResEuc_ (rseShowsd_, rseFromExpr_, rseDivm_)






------------------------------------------------------------------------
msgField str =  str ++ "  must be a Field.\n"                   -- LOCAL

instance Field a => Set (ResidueE (UPol a))
  where
  compare_m  = compareTrivially 
  showsDomOf = ResEuc_.rseShowsd_
  fromExpr   = ResEuc_.rseFromExpr_

  baseSet  r@(Rse f iI fD) dm =  
    case
        (Map.lookup Set dm, pirCIBase iI, sample f, dom f)  
    of
    (Just (D1Set o), _, _, _ ) -> (dm, o)  
    (_,              g, a, aD) ->
      (case
           (Map.lookup Set aD, Map.lookup Ring aD)
       of
       (Just (D1Set setA), Just (D1Ring rA)) ->
                                               rbs g a setA $ isField rA
       _                                     ->
                     (dm, error $ msg "\nSet or Ring not found in  R\n")
      )
    where
    msg = showString "\nbaseSet r rdom," . 
          showsWithDom 1 r "r" "R[_]/I" . showChar '\n'

    rbs _ _ _    No      = (dm, error $ msg $ msgField "R")
    rbs g a setA isfield = (Map.insert Set (D1Set o) dm, o)
      where
      o = OSet {osetSample  = r,         membership  = bel', 
                osetCard    = card',     osetPointed = Just $ Just r,
                osetList    = list',
                osetBounds  = (Nothing, Nothing, Nothing, Nothing),
                osetProps   = props',
                osetConstrs = [],      
                osetOpers   = []}
          where
          (z, u, degG) = (zeroS a, unity a, deg g)
          x     = varP u f
          belP  = membership $ snd $ baseSet f fD
          card' = case (isfield, osetCard setA)  
                  of 
                  (_,   UnknownV) -> UnknownV
                  (_,   Infinity) -> Infinity
                  (Yes, Fin n   ) -> Fin (n^degG)
                  _               -> UnknownV

          bel' md (Rse f _ _) = ldeg f < degG  &&  bl md f
                                                   where
                                                   bl 'r' = belP 'r'
                                                   bl _   = const True
          list' = 
              case (isfield, osetList setA) 
              of
              (Yes, Just as) ->
                  let but0         = delete z as
                      assocClass f = [cPMul a f | a <- but0]
                      constPols    = map (ctr f) as
                      assocGroups  = takeWhile ((< degG) . deg . head) $
                                                    monicUPols_overFin x
                      nonConstPols =
                            concat $ map assocClass $ concat assocGroups
                  in  Just $ map (ct r) $ (constPols ++ nonConstPols)

              _ -> Nothing

          props' = [(Finite,         isFiniteSet setA), 
                    (IsBaseSet,      Yes),   
                    (FullType,       No ), 
                    (OrderIsTrivial, Yes),  -- so far
                    (OrderIsTotal,   No ), 
                    (OrderIsNoether, Yes),  (OrderIsArtin, Yes)]


------------------------------------------------------------------------
instance Field a => AddSemigroup (ResidueE (UPol a))  
  where
  -- in this case, the additive operations in  k[x]/(g) 
  -- skip the reduction by g:

  zero_m r = Just $ ct r $ zeroS $ resRepr r

           -- add, neg_m .. imes_m  skip the reduction by base, because
           --                       these operations are linear over  k

  neg_m   r = Just $ ct r $   neg$ resRepr r
  add     r = ct r . add (resRepr r) . resRepr
  sub_m   r = Just . ct r . sub (resRepr r) . resRepr
  times_m r = Just . ct r . times (resRepr r)

  baseAddSemigroup  r@(Rse f iI _)  dm =  
    (case  
         (Map.lookup AddSemigroup dm, pirCIBase iI, dom f)
     of
     (Just (D1Smg s), _, _ ) -> (dm, s)
     (_,              g, aD) ->
       case  
           (Map.lookup AddSemigroup aD, Map.lookup AddGroup aD)
       of
       (Just (D1Smg sA), Just (D1Group gA)) -> 
                                      semig g sA gA $ Map.lookup Ring aD
       _                                    -> (dm, error $ msg msg1)
    )
    where
    msg = showString "\nbaseAddSemigroup r rdom," . 
          showsWithDom 1 r "r" "R[_]/I" . showChar '\n'
    msg1 = "\nAddSemigroup or AddGroup or Ring term not found in  R.\n"

    semig _ _  _  Nothing            = (dm, error $ msg msg1)
    semig g sA gA (Just (D1Ring rA)) = 
      case  
          isField rA 
      of
      No      -> (dm, error $ msg $ msgField "R")
      isfield -> (Map.insert AddSemigroup (D1Smg s) dm, s)
        where
        s = Subsemigroup 
            {subsmgType    = Add,   subsmgUnity = Just $ Just zeroRes,
             subsmgGens    = gens', subsmgProps = props',
             subsmgConstrs = [],    subsmgOpers = []}
            where
            (degG,  zeroRes) = (deg g,        zeroS r       )
            (gensA, sAProps) = (subgrGens gA, subsmgProps sA)
            props'= [(Commutative,           Yes),
                     (IsGroup,               Yes),
                     (IsMaxSubsemigroup,     No),
                     (IsOrderedSubsemigroup, Unknown),  -- so far
                     (IsCyclicSemigroup,     cyc')   
                    ]
            cyc' = case (isfield, degG)
                   of
                   (Yes, 1) -> lookupProp IsCyclicSemigroup sAProps
                   (Yes, _) -> No
                   _        -> Unknown
            gens' = 
                  case (isfield, gensA)  
                  of    -- if gA is generated by  as, then  a[x]/g  is
                        -- generated by [a*x^i| a<-as, i<-[0 .. degG-1]]

                  (Yes, Just as) -> Just [ct r $ ct f (b, i) |
                                          b <- as, i <- [0 .. (degG-1)]]
                  _              -> Nothing

        
------------------------------------------------------------------------
instance Field a => AddGroup (ResidueE (UPol a))
  where 
  baseAddGroup  r@(Rse f iI _) dm =  
    (case  
         (Map.lookup AddGroup dm, pirCIBase iI, dom f)  
     of
     (Just (D1Group g), _, _ ) -> (dm, g)
     (_,                g, aD) ->
       case 
           (Map.lookup Set aD, Map.lookup AddGroup aD, pirCIFactz iI)
       of
       (_,               Nothing,           _ ) ->
                                                  (dm, error $ msg msg1)
       (Just (D1Set sA), Just (D1Group gA), ft) -> 
                                      gr g sA gA ft $ Map.lookup Ring aD
    )
    where
    msg = showString "\nbaseAddGroup r rdom," . 
          showsWithDom 1 r "r" "R[_]/I" . showChar '\n'
    msg1 = "\nAddGroup or Ring not found in  R.\n"

    gr _ _  _  _  Nothing            = (dm, error $ msg msg1)
    gr g sA gA ft (Just (D1Ring rA)) = 
      case  
          isField rA  
      of
      No      -> (dm, error $ msg $ msgField "R")
      isfield -> (Map.insert AddGroup (D1Group gG) dm, gG)
        where
        gG = Subgroup 
             {subgrType    = Add,                 subgrGens  = gens', 
              subgrCanonic = Just $ const zrRes,  subgrProps = props',
              subgrConstrs = [],                  subgrOpers = []}
           where
           (zrRes,   degG    ) = (zeroS r,      deg g        )
           (gens_gA, props_gA) = (subgrGens gA, subgrProps gA)
           props' = [(IsNormalSubgroup,  Yes),
                     (IsMaxSubgroup,     No ), 
                     (IsOrderedSubgroup, Unknown),   -- so far            
                     (IsCyclicGroup,     cyc'),
                     (IsPrimeGroup,      prime')
                    ]
           cyc' = case (isfield, degG)  
                  of
                  (Yes, 1) -> lookupProp IsCyclicGroup props_gA
                  (Yes, _) -> No
                  _        -> Unknown

           -- a[x]/(g) is a prime group <==>
           --                               a  is finite and g is prime.
           -- For primality of  g  inspect the factorization in iI.
           --
           prime' = case (isFiniteSet sA, ft)  
                    of
                    (No,  _       ) -> No
                    (_,   []      ) -> Unknown  -- factorization skipped
                    (Yes, [(_, 1)]) -> Yes
                    (_,   [(_, 1)]) -> Unknown
                    _               -> No 
           gens' = 
                  case (isfield, gens_gA) 
                  of      -- if gA is generated by  as, then  a[x]/g  is
                          -- generated by [a*x^i| a<-as, i<-[0..degG-1]]

                  (Yes, Just as) -> Just [ct r $ ct f (b, i) |
                                          b <- as, i <- [0 .. (degG-1)]]
                  _              -> Nothing

------------------------------------------------------------------------
instance Field a => MulSemigroup (ResidueE (UPol a))
  where
  baseMulSemigroup = rseBaseMulSemigroup
  unity_m r        = Just $ ct r $ unity $ resRepr r
  divide_m         = ResEuc_.rseDivm_

  -- inv_m, power    are the default ones.

  mul r =          -- applies optimization for the case  Ideal = (a*x^n)
    (case upolMons $ pirCIBase $ resPIdeal r
     of
     [(_, n)] -> ct r . ct f . pmul z cp (rd n) mons . upolMons .
                                                       resRepr
     _        -> ctr r . mul f . resRepr
    ) where
      (f, cp)     = (resRepr r, compare :: Comparison Integer)
      (mons, z )  = (upolMons f, zeroS $ sample f)
      rd n (a, m) = if m < n then (a, m)  else (z, 0) 

  divide_m2 _ _ = error "\ndivide_m2  for ResidueE (UPol _):   use  \
                                                   \divide_m instead.\n"
  root _ _ = error "\nroot _  for ResidueE (UPol _):\
                   \  it is not defined, so far.\n"
