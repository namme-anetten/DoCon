module ResEuc1_  where

-- Auxiliary for  ResEuc_.hs   - see the comments there.
-- All needed from here is  reexported by  Residue.
 
import qualified Data.Map as Map (lookup, insert)

import Data.Maybe (fromJust)
import Data.List  (nub, find) 

import DPrelude (PropValue(..), InfUnn(..), ct, ctr, not3, boolToPropV, 
                                                                 showsn)
import Categs
import SetGroup  
import Ring0_   (isCEucRing)
import Ring1_   (remEuc)
import ResEuc0_ (Residue(..), isCorrectRse)






------------------------------------------------------------------------
ifCEuc_rse_ :: Domains1 a -> b -> (String -> String) -> (b, c) -> (b, c)
ifCEuc_rse_    aDom          dom  msg                   v =  
  case  
      Map.lookup EuclideanRing aDom
  of
  Nothing         ->
               (dom, error $ msg "\n\nEuclideanRing not found in  D.\n")
  Just (D1EucR t) -> 
           case isCEucRing t 
           of
           No -> (dom, error $ msg "\n\nc-Euclidean ring  D  needed.\n")
           _  -> v

------------------------------------------------------------------------
rseBaseSet r dm = 
  case  
      (Map.lookup Set dm, resPIdeal r, dom r)  
  of
  (Just (D1Set o), _ , _ ) -> (dm, o)
  (_,              iI, aD) ->
    (case 
         (pirCIBase iI, Map.lookup Set aD)
     of
     (_, Nothing          ) -> (dm, error $ msg1 msg)
     (b, Just (D1Set setA)) ->
                   ifCEuc_rse_ aD dm msg1 $ rbs b setA $ membership setA
    )
  where
  msg1 = showString "\nbaseSet r dom',\nr = " . showsn 1 r . 
         showString "\n <- D/I =  " . showsDomOf 1 r 
  msg = "\n\nSet or EuclideanRing  not found in  D.\n"

  rbs b setA bel = (Map.insert Set (D1Set o) dm, o)
    where
    o = OSet {osetSample  = r,           membership  = bel', 
              osetCard    = card',       osetPointed = Just $ Just r,
              osetList    = ll',
              osetBounds  = (Nothing, Nothing, Nothing, Nothing),
              osetProps   = props',
              osetConstrs = [],       osetOpers   = []}
        where
        canr x                 = remEuc 'c' x b
        bel' md r@(Rse x iJ _) =
                       isCorrectRse r  &&  (pirCIBase iJ) == b  &&  bl x
                       where
                       bl = if md == 'r' then  bel 'r'  else  const True

        card' = UnknownV   -- to be developed  ***
        ll'   = fmap (map (ct r) . nub . map canr) $ osetList setA
        props' = [(Finite,         fin'), (IsBaseSet, Yes),   
                  (FullType,       No  ), 
                  (OrderIsTrivial, Yes ),  -- so far
                  (OrderIsTotal,   No  ), 
                  (OrderIsNoether, Yes ), (OrderIsArtin, Yes)
                 ]               
        fin' = case card' of UnknownV -> Unknown
                             Infinity -> No
                             _        -> Yes


------------------------------------------------------------------------
rseBaseAddSemigroup r dm = 
 case 
     (Map.lookup AddSemigroup dm, resPIdeal r, dom r)  
 of
 (Just (D1Smg s), _ , _ ) -> (dm, s)
 (_,              iI, aD) ->
  let 
     b = pirCIBase iI
  in
  (case (Map.lookup AddSemigroup aD, Map.lookup AddGroup aD)
   of
   (Just (D1Smg sA), Just (D1Group gA)) -> 
                                  ifCEuc_rse_ aD dm msg1 $ semig b sA gA
   _                                    -> (dm, error $ msg1 msg)
  )   
  where
  msg1 = showString "\nbaseAddSemigroup r dom',\nr = " . showsn 1 r . 
         showString "\n <- D/I =  " . showsDomOf 1 r
  msg = "\n\nAddSemigroup or AddGroup not found in  D.\n"

  semig b sA gA = (Map.insert AddSemigroup (D1Smg s) dm', s)
    where
    (dm', rSet) = baseSet r dm
    s = Subsemigroup 
        {subsmgType    = Add,    subsmgUnity = Just $ Just zeroRes,
         subsmgGens    = gens',  subsmgProps = props',
         subsmgConstrs = [],     subsmgOpers = []}
        where
        zr               = zeroS b
        zeroRes          = ct r zr
        canr x           = remEuc 'c' x b
        (gensA, sAProps) = (subgrGens gA, subsmgProps sA)
        props' = [(Commutative,           Yes    ), (IsGroup, Yes),
                  (IsMaxSubsemigroup,     No     ),
                  (IsOrderedSubsemigroup, Unknown),  -- so far
                  (IsCyclicSemigroup,     cyc'   )   
                 ]
        cyc' = case  lookup IsCyclicSemigroup sAProps
               of
               Just Yes -> Yes    -- residue of cyclic is cyclic
               _        -> Unknown
                         -- we could use further isPrime (card(residue))
                         -- but isPrime is not compiled yet for Integer
                         -- at *this* point of program modules !
        gens' = 
          case (gensA, osetList rSet) 
          of                          -- many optimizations possible ***
          (Just xs, _        ) ->  
                  Just $ map (ct r) $ nub $ filter (/= zr) $ map canr xs
                               
          (_,       Just ress) -> 
                       Just $ map (ct r) $ gensModulo $ map resRepr ress
                                          where 
                                          gensModulo xs = xs   -- so far
          _                    -> Nothing


rseBaseMulSemigroup r dm = 
  case
      (Map.lookup MulSemigroup dm, resRepr r, dom r)  
  of
  (Just (D1Smg s), _, _ ) -> (dm, s)
  (_,              x, aD) -> ifCEuc_rse_ aD dm msg (dm', s)
    where
    msg = showString "\nbaseMulSemigroup r dom',\nr = " . showsn 1 r . 
          showString "\n <- D/I =  " . showsDomOf 1 r

    dm' = Map.insert MulSemigroup (D1Smg s) dm
    s   = let unR   = ctr r $ unity x
              props = [(Commutative,           Yes    ), (IsGroup, No),
                       (IsMaxSubsemigroup,     No     ),
                       (IsOrderedSubsemigroup, Unknown),  
                       (IsCyclicSemigroup,     No     )   
                                          -- because 0,1 <- subsemigroup
                      ]
          in  Subsemigroup {subsmgType    = Mul,   
                            subsmgUnity   = Just $ Just unR,
                            subsmgGens    = Nothing,  -- so far
                            subsmgProps   = props,
                            subsmgConstrs = [],    subsmgOpers = []}


------------------------------------------------------------------------
rseBaseAddGroup r dm =
  case
      (Map.lookup AddGroup dm, dom r, resPIdeal r)  
  of
  (Just (D1Group g), _ , _ ) -> (dm, g)
  (_,                aD, iI) ->
    (case 
         (Map.lookup AddGroup aD, pirCIBase iI, pirCIFactz iI)
     of
     (Nothing,           _, _ ) -> (dm, error $ msg1 msg)
     (Just (D1Group gA), b, ft) -> ifCEuc_rse_ aD dm msg1 $ gr gA b ft
    )
  where
  msg1 = showString "\nbaseAddGroup r dom',\nr = " . showsn 1 r . 
         showString "\n <- D/I =  " . showsDomOf 1 r
  msg = "\n\nAddGroup  not found in  D.\n"

  gr gA b ft = (Map.insert AddGroup (D1Group g) dm', g)
    where
    (dm', rSet) = baseSet r dm
    g = Subgroup {subgrType    = Add,     
                  subgrGens    = gens', 
                  subgrCanonic = Just $ const zeroR,
                                        -- for base subgroup is full one
                  subgrProps   = props',
                  subgrConstrs = [],    
                  subgrOpers   = []}
        where
        zr     = zeroS b
        zeroR  = ct r zr
        canr x = remEuc 'c' x b
        (gens_gA, props_gA) = (subgrGens gA, subgrProps gA)
        props' = [(IsNormalSubgroup,  Yes   ),
                  (IsMaxSubgroup,     No    ), 
                  (IsOrderedSubgroup, No    ),   -- so far            
                  (IsCyclicGroup,     cyc'  ),
                  (IsPrimeGroup,      prime')
                  ]
        cyc' = case lookup IsCyclicGroup props_gA of Just Yes -> Yes
                                                     _        -> Unknown
                                                              -- so far
        -- R/(b) is a prime group <==>   R/(b) is finite and b is prime.
        -- For primality of  b  inspect the factorization in iI.
        --
        prime' = case (isFiniteSet rSet, ft)  
                 of
                 (No,  _       ) -> No
                 (_,   []      ) -> Unknown  -- factorization skipped
                 (Yes, [(_, 1)]) -> Yes
                 (_,   [(_, 1)]) -> Unknown
                 _               -> No 
        gens' = 
          case (gens_gA, osetList rSet)  
          of                               -- optimizations possible ***
          (Just xs, _        ) -> 
                  Just $ map (ct r) $ nub $ filter (/= zr) $ map canr xs

          (_,       Just ress) -> 
                     Just $ map (ct r) $ gensModulo $ map resRepr $ ress
                                           where 
                                           gensModulo xs = xs  -- so far
          _                    -> Nothing


------------------------------------------------------------------------
rseBaseRing r@(Rse a iI aD) dm = 
  case
      (Map.lookup Ring dm, pirCIBase iI, pirCIFactz iI)
  of
  (Just (D1Ring rg), _, _ ) -> (dm, rg)
  (_,                b, ft) ->
    (case
         (Map.lookup AddGroup aD, Map.lookup Ring aD)
     of
     (Just (D1Group aG), Just (D1Ring aR)) ->
                                  ifCEuc_rse_ aD dm msg1 $ br b ft aG aR
     _                                     -> (dm, error $ msg1 msg)
    )
    where
    msg1 = showString "\nbaseRing r dom',\nr = " . showsn 1 r . 
           showString "\n <- D/I =  " . showsDomOf 1 r
    msg  = "\n\nAddGroup or Ring not found in  D.\n"

    br b ft aG aR = (Map.insert Ring (D1Ring rg) dm', rg)
      where
      (dm', rSet) = baseSet r dm 
      rg          = Subring {subringChar    = char', 
                             subringGens    = Nothing,   -- so far
                             subringProps   = props',
                             subringConstrs = [],   
                             subringOpers   = opers'}
          where
          (zr, un, un') = (zeroS a, unity a, unity r)
          canr x        = remEuc 'c' x b
          xG_gens       = subgrGens aG
          --------------------------------------------------------------
          char' = 
             case (xG_gens, subringChar aR) 
             of
             (Just [_], _      ) -> Just n   -- aR isomorphic to Integer
                                         where Fin n = osetCard rSet
             (_,        Nothing) -> Nothing
             (_,        Just 0 ) -> Nothing                -- so far
             (_,        Just _ ) -> Just $ c (1 :: Integer) $ canr un
               where
               c k sum = if sum == zr then  k    -- may be expensive
                         else               c (succ k) $ canr (sum + un)
                                                -- better solution ? ***
          props' = [(IsField,       bPrime     ), 
                    (HasZeroDiv,    not3 bPrime), 
                    (HasNilp,       hasNl      ),
                    (IsPrimaryRing, bPrimary   ),    
                    (Factorial,     bPrime     ), 
                    (PIR,           Yes        ),                     
                    (IsOrderedRing, Unknown    ),  -- so far
                    (IsRealField,   Unknown    ),  --
                    (IsGradedRing,  Unknown    )    
                   ]
          bPrime = case ft of []       -> Unknown
                              [(_, 1)] -> Yes
                              _        -> No    
          bPrimary = case ft of []  -> Unknown
                                [_] -> Yes
                                _   -> No    
          hasNl = if null ft then Unknown
                  else            boolToPropV $ any (/=1)$ map snd ft
          --------------------------------------------------------------
          -- In  opers',  DoCon is so far interested only in 
          -- finding when  R/(b)  contains a prime field, in 
          -- WithPrimeField  construct.
          -- If  R  is isomorphic to  Integer  then, Lemma:
          --           if  b  is prime then R/(b) is a prime field,
          --           otherwise  R/(b)  does not contain a field.
          -- Suppose now  R  is not isomorphic to  Inteter.
          -- If  dimOverPrime  yields a definite value for R, then 
          -- R  contains a prime field  k  inside.  And it must hold
          -- intersection(k,(b)) = {0}.  Hence R/(b) contains a copy of  
          -- k.
          -- But how do we find  dim( R/(b), k' )  ?
          -- Is it true that  R  is isomorphic to  k[x]  in this case? 
          -- So far, we skip this case, minding that at least,
          -- ResidueE k[x]  will handle it.

          opers' = (case (xG_gens, bPrime) of
                               (Just [_], Yes) -> [(WithPrimeField, wp)]
                               _               -> []
                   )
             where                   -- R isomorphic to Integer, b prime
             wp = WithPrimeField' 
                  {frobenius            = (id, Just .Just),
                   dimOverPrime         = Fin 1,
                   primeFieldToZ        = toz,
                   primeFieldToRational = undefined,
                   primitiveOverPrime   = 
                         ([un'], [(un', 1), (-un', 0)], \ r -> [(r, 0)])
                  }
             toz r = fromJust $ find ((== r) . times un') [0 ..]
                     -- This may be slow. There exist faster special
                     -- overlapping instances for ResidueE.
