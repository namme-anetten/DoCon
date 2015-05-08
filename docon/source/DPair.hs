--------------------------------------------------------------------
--------------------------------------------------------------------
--  The Algebraic Domain Constructor  DoCon,   version 2.12
--
--  Copyright  Serge Mechveliani,    2012
--------------------------------------------------------------------
--------------------------------------------------------------------





module DPair

  -- Category instances for Direct Product of two domains.
  (
   -- instances for (,):
   -- Set,AddSemigroup,AddMonoid,AddGroup,MulSemigroup,MulMonoid,
   -- MulGroup,Ring,CommutativeRing,LinSolvRing

   module DPair_
   -- directProduct_set, directProduct_semigroup,
   -- directProduct_group, directProduct_ring
  )
where
import qualified Data.Map as Map (empty, lookup, insert)

import Iparse_  (Expression(..)                ) 
import DPrelude (lookupProp, and3, showsWithDom)
import SetGroup    
import Categs (CategoryName(..), Domain1(..), 
               LinSolvRingTerm(..), Property_LinSolvRing(..))
import Ring0_
import VecMatr (rowMatrMul)
import DPair_



------------------------------------------------------------------------
maybePair (Just x) (Just y) = Just (x, y) 
maybePair _        _        = Nothing

------------------------------------------------------------------------
instance (Set a, Set b) => Set (a, b)         -- baseSet(a) x baseSet(b)
  where
  compare_m = compareTrivially

  showsDomOf verb (a, b) = 
                   showChar '(' . showsDomOf verb a . showString " x " . 
                   showsDomOf verb b . showChar ')'

  baseSet (x, y) dom =  
    case 
        (Map.lookup Set dom, baseSet x Map.empty, baseSet y Map.empty) 
    of
    (Just (D1Set o), _,      _      ) -> (dom, o)    
    (_,              (_, o), (_, o')) -> 
                                   (Map.insert Set (D1Set o'') dom, o'')
                                            where
                                            o'' = directProduct_set o o'
  fromExpr (x, y) (E (L ",") [e1] [e2]) =  
         case  
             (fromExpr x e1, fromExpr y e2)  
         of
         ( ([x'], "" ), ([y'], "" ) ) -> ( [(x', y')], "" )
         ( ([_ ], "" ), (_   , msg) ) -> 
                              ([], "fromExpr:  second of pair: " ++ msg)
         ( (_,    msg), _           ) -> 
                               ([], "fromExpr:  first of pair: " ++ msg)

  fromExpr _     _ = ([], "fromExpr:  (expr1, expr2) expected on input")


------------------------------------------------------------------------
instance (AddSemigroup a, AddSemigroup b) => AddSemigroup (a, b) 
  where
  add (x, y) (x1, y1) = (add x x1, add y y1)

  zero_m  (x, y)   = maybePair (zero_m x)     (zero_m y) 
  neg_m   (x, y)   = maybePair (neg_m  x)     (neg_m  y)  
  times_m (x, y) n = maybePair (times_m  x n) (times_m  y n)

  baseAddSemigroup (x, y) dom =  
    case  
        (Map.lookup AddSemigroup dom, baseAddSemigroup x Map.empty,
                                      baseAddSemigroup y Map.empty)
    of
    (Just (D1Smg s), _,       _      ) -> (dom, s)    
    (_,              (_, s1), (_, s2)) -> 
                              (Map.insert AddSemigroup (D1Smg s) dom, s)
                                   where
                                   s = directProduct_semigroup s1 s2

------------------------------------------------------------------------
instance (AddMonoid a, AddMonoid b) => AddMonoid (a, b)  

instance (AddGroup a, AddGroup b) => AddGroup (a, b)   
  where
  baseAddGroup (x,y) dom =  
    case  
     (Map.lookup AddGroup dom, baseSet x Map.empty, baseSet y Map.empty)
    of
    (Just (D1Group g), _         , _         ) -> (dom, g)    
    (_,                (dom1, s1), (dom2, s2)) -> 
                   let
                       (z1, z2) = (zeroS x, zeroS y)
                       (_, g1)  = baseAddGroup x dom1
                       (_, g2)  = baseAddGroup y dom2
                       g        = directProduct_group z1 s1 g1 z2 s2 g2
                   in  (Map.insert AddGroup (D1Group g) dom, g)


------------------------------------------------------------------------
instance (MulSemigroup a, MulSemigroup b) => MulSemigroup (a, b) 
  where
  mul (x, y) (x', y') = (mul x x', mul y y')

  unity_m (x, y) = maybePair (unity_m x) (unity_m y)
  inv_m   (x, y) = maybePair (inv_m x)   (inv_m y)
                                          
  divide_m (x, y) (x', y') =  maybePair (divide_m x x') (divide_m y y')

  divide_m2 _ _ = error "\ndivide_m2 (x, y) (x', y') :\n\
                        \it is not defined for Pair, so far.n" 

  power_m (x, y) n = maybePair (power_m  x n) (power_m  y n)

  root n (x, y) = 
               case (root n x, root n y) 
               of
               (Just (Just x'), Just (Just y')) -> Just (Just (x', y'))
               (Just Nothing,   _             ) -> Just Nothing
               (_,              Just Nothing  ) -> Just Nothing
               _                                -> Nothing

  baseMulSemigroup (x, y) dom =  
    case  
        (Map.lookup MulSemigroup dom, baseMulSemigroup x Map.empty,
                                      baseMulSemigroup y Map.empty)
    of
    (Just (D1Smg s), _      , _      ) -> (dom, s)    
    (_,              (_, s1), (_, s2)) -> 
                              (Map.insert MulSemigroup (D1Smg s) dom, s)
                                       where
                                       s = directProduct_semigroup s1 s2

------------------------------------------------------------------------
instance (MulMonoid a, MulMonoid b) => MulMonoid (a, b)

instance (MulGroup a, MulGroup b) => MulGroup (a, b) 
  where
  baseMulGroup (x, y) dom =  
    case  
        (Map.lookup MulGroup dom, baseSet x Map.empty,
                                  baseSet y Map.empty)
    of
    (Just (D1Group g), _         , _         ) -> (dom, g)    
    (_,                (dom1, s1), (dom2, s2)) -> 
                    let
                        (u1, u2) = (unity x, unity y) 
                        (_, g1)  = baseMulGroup x dom1
                        (_, g2)  = baseMulGroup y dom2
                        g        = directProduct_group u1 s1 g1 u2 s2 g2
                    in  (Map.insert MulGroup (D1Group g) dom, g)


------------------------------------------------------------------------
instance (Ring a, Ring b) => Num (a, b)  
  where
  negate (x, y)     = (neg x, neg y) 
  (x, y) + (x', y') = (add x x', add y y') 
  (x, y) - (x', y') = (sub x x', sub y y') 
  (x, y) * (x', y') = (mul x x', mul y y') 

  signum _ = error "\nsignum (_, _):  it is not defined for Pair.\n"
  abs    _ = error "\nabs (_, _):  it is not defined for Pair.\n"
  fromInteger _ = 
          error "\nfromInteger (_, _):  use  fromi, fromi_m  instead.\n"

instance (Ring a, Num a, Ring b, Num b) => Fractional (a, b)  
  where
  (x, y) / (x', y') = (divide x x', divide y y') 
  fromRational _ = error "\nfromRational:  instead use  fromi_m \
                         \ composed with  divide_m.\n"

instance (Ring a, Ring b) => Ring (a, b)  
  where
  fromi_m (x, y) n = maybePair (fromi_m x n) (fromi_m y n) 

  baseRing (x, y) dom =  
    case 
       (Map.lookup Ring dom, baseRing x Map.empty, baseRing y Map.empty)
    of
    (Just (D1Ring r), _      , _      ) -> (dom, r)    
    (_,               (_, r1), (_, r2)) -> 
                            let
                               (z1, z2) = (zeroS x, zeroS y) 
                               r        = directProduct_ring z1 r1 z2 r2
                            in (Map.insert Ring (D1Ring r) dom, r)


------------------------------------------------------------------------
instance (CommutativeRing a, CommutativeRing b) =>  
                                                  CommutativeRing (a, b)
          -- Here  Commutative==Yes
          -- is presumed for the base multiplicative semigroups of  a, b

instance (LinSolvRing a, LinSolvRing b) => LinSolvRing (a, b)
  where
  -- see  Manual-'gx'-Direct sum

  baseLinSolvRing (x,y) dom =
    case
        (Map.lookup LinSolvRing dom, baseLinSolvRing x Map.empty, 
                                     baseLinSolvRing y Map.empty)
    of
    (Just (D1LinSolvR t), _      , _      ) -> (dom,t)
    (_,                   (_, t1), (_, t2)) ->
        let
          aProps = linSolvRingProps t1
          bProps = linSolvRingProps t2
          names  = [ModuloBasisDetaching, ModuloBasisCanonic,
                    WithSyzygyGens,       IsGxRing
                   ]
          [aModDetach, aModC, aWithSyz, aGxR] =
                                      [lookupProp p aProps | p <- names]
          [bModDetach, bModC, bWithSyz, bGxR] =
                                     [lookupProp p bProps | p <- names]
          props = [(ModuloBasisDetaching, and3 aModDetach bModDetach),
                   (ModuloBasisCanonic  , and3 aModC      bModC     ),
                   (WithSyzygyGens      , and3 aWithSyz   bWithSyz  ),
                   (IsGxRing            , and3 aGxR       bGxR      )
                  ]
          t = LinSolvRingTerm {linSolvRingProps = props}
        in
        (Map.insert LinSolvRing (D1LinSolvR t) dom, t)

                                
  gxBasis []    = ([], [[]])    -- [(a,b)] -> ( [(a,b)], [[(a,b)]] )
  gxBasis pairs =         
    let
      (zrA, zrB)          = zeroS (head pairs)
      (as,  bs )          = unzip pairs 
      ((gs, mA),(hs, mB)) = (gxBasis as, gxBasis bs)
      g's                 = [(a, zrB) | a <- gs]
      h's                 = [(zrA, b) | b <- hs]

                   {- example:       mt        pairs       gBasis
                                  | * * *     (a1,b1)      (g1,0 )
                             rowsA' * * *     (a2,b2)      (g2,0 )
                                 --------  X  (a3,b3)  =   --
                             rowsB' * * *                  (0 ,h1)
                                  | * * *                  (0 ,h2)
                                  | * * *                  (0 ,h3)
                   -}
      (mA',mB') = (map liftVecA mA, map liftVecB mB)
      liftVecA  = map (\ a -> (a, zrB)) 
      liftVecB  = map (\ b -> (zrA, b)) 
    in
    (g's ++ h's, mA' ++ mB')

                                   
  moduloBasis mode pairs (a, b) =      -- String -> [a] -> a -> (a, [a])
    let
      cMode               = if elem 'c' mode  then "c"  else ""
      gMode               = if elem 'g' mode  then "g"  else ""
      zeroPair@(zrA, zrB) = zeroS (a, b)

      msg = showString ("moduloBasis " ++ (mode ++ " pairs pair,\n")) . 
            showsWithDom 1 (a, b) "pair" ""
    in
    case (elem mode ["", "c", "g", "cg", "gc"], gMode)
    of
    (False, _  ) -> error $ msg ("\nmode  may be only " ++
                                 " \"\",\"c\",\"g\",\"cg\",\"gc\"  \n")
    (_,     "" ) -> 
               let (gs, rows) = gxBasis pairs 
                   (r,q)      = moduloBasis (cMode ++ "g") gs (a, b)
               in         
               if all (== zeroPair) pairs  then
                                    ((a, b), map (const zeroPair) pairs)
               else                 (r,      rowMatrMul q rows         )

    (_,     "g") ->   
           -- pairs  is a gx-basis when both
           --                    filter (/=zrA) $ map fst pairs  and
           --                    filter (/=zrB) $ map snd pairs
           -- are gx-bases.
           -- But the quotient coefficients has to be set for the
           -- zeroes too.
           let  
             mode'     = cMode ++ "g"
             (as , bs ) = unzip pairs
             (as', bs') = (filter (/= zrA) as, filter (/= zrB) bs)
             (rA , qA') = moduloBasis mode' as' a
             (rB , qB') = moduloBasis mode' bs' b
             qA         = restore zrA as qA'
             qB         = restore zrB bs qB'

             restore zr xs      []      =  map (const zr) xs
             restore zr (x: xs) (q: qs) =
                            if x == zr then  zr: (restore zr xs (q: qs))
                            else             q : (restore zr xs qs     )

             restore _  _      _      = 
                      error $ msg ("\n... _restore zr [] (q: qs) :   "
                                   ++ "  qs  is longer than  xs  - ?\n")
           in   
           ((rA, rB), zip qA qB)


  syzygyGens mode []    = error ("\nsyzygyGens " ++ 
                                 (mode ++ " []    for (a, b).\n"))
  syzygyGens _    pairs =     
               let (zrA, zrB)     = zeroS $ head pairs
                   liftVecA       = map (\ x -> (x, zrB))
                   liftVecB       = map (\ x -> (zrA, x))
                   (as, bs)       = unzip pairs
                   (relsA, relsB) = (syzygyGens "" as, syzygyGens "" bs)
               in
               (map liftVecA relsA) ++ (map liftVecB relsB)
