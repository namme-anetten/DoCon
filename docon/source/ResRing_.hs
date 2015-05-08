------------------------------------------------------------------------
------------------------------------------------------------------------
--  The Algebraic Domain Constructor  DoCon,   version 2.12
--
--  Copyright  Serge Mechveliani,    2012
------------------------------------------------------------------------
------------------------------------------------------------------------



-- Residue (quotient) ring.
-- Category instances for the generic  Residue ring modulo ideal.
--
-- For the residues  Rsi x (iI, d) dm  :: ResidueI R,  R a base ring,
--
-- the instances  Set, ..., LinSolvRing  require also
--   (IsGxRing, Yes)  for  R  
--   and  iI  with the basis possessing  (IsGxBasis, Yes).
--
-- And the instances of  GCDRing,FactorizationRing,EuclideanRing,Field
--
-- are correct (and trivial) *only* for  R/I  being a field, that is
-- iI  possessing (IsMaxIdeal,Yes).



module ResRing_    -- All needed from here is reexported by  Residue.
(
 ResidueI(..), isCorrectRsi, 
 showsd_, fromexpr_
 -- , instances for ResidueI:  
 --                 Show, DShow, Dom, Residue, Cast, Set .. AddGroup .. 
 --                 MulMonoid, Num, Fractional
)  
where
import System.Random (Random(..))   -- non-standard, non-GHC

import qualified Data.Map as Map (lookup, insert)

import Data.List (nub)

import DPrelude (Length(..), DShow(..), Cast(..), -- classes
                 Expression(..), PropValue(..), InfUnn(..), 
                 ct, ctr, lookupProp, showsn, showsWithDom)
import Categs 
import SetGroup 
       (Set(..), AddSemigroup(..), MulSemigroup(..), AddMonoid(),
        MulMonoid(), AddGroup(..), zeroS, neg, sub, unity, divide, 
        isZero, times, isFiniteSet, compareTrivially, upAddGroup
       )
import RingModule (LinSolvRing(..), FactorizationRing(..))
import Z          ()
import ResEuc0_   (Residue(..), resIdeal)






------------------------------------------------------------------------
data ResidueI a =  Rsi a (Ideal a, Domains1 a) (Domains1 a) 

-- Restrictions similar to ResidueE.
-- See Manual.

instance Dom ResidueI where  dom (Rsi _ _ d) = d
                             sample          = resRepr

instance Residue ResidueI
  where
  resRepr   (Rsi x _ _) = x
  resIDom   (Rsi _ d _) = d
  resGDom   _           = error "\nresGDom (Rsi..).\n"
  resPIdeal _           = error "\nresPIdeal (Rsi..).\n"


msgNoBas = "\n\nBasis not found in ideal.\n"                 -- LOCAL
msgGxBas = "\n\ngx-basis needed for ideal.\n"                --
msgGH    =                                                   --
          "\n\nDomain for I has to contain AddGroup with canonic map.\n"

rsiMsg :: LinSolvRing a => String -> ResidueI a -> String -> String
rsiMsg                     str       r          = 
                        
              (str++) . (" r rdom, \n"++)   . ("r = "++) . shows r .
              ("\n <- D/I =  "++) . showsDomOf 1 r


reduceCanG :: LinSolvRing a => [a] -> a -> a                -- LOCAL
reduceCanG gs =  fst . moduloBasis "cg" gs

isCorrectRsi :: LinSolvRing a => ResidueI a -> Bool
isCorrectRsi (Rsi x (iI,_) _) =
  case
      (idealGens iI, idealGenProps iI) 
  of  
  (Nothing, _    ) -> False
  (Just gs, props) -> case lookup IsGxBasis props
                      of
                      Just Yes -> x == (reduceCanG gs x)
                      _        -> False

instance LinSolvRing a => Cast (ResidueI a) a
  where
  cast  mode  r@(Rsi _ (iI, dg) d)  a =
    case 
        (mode == 'r', idealGens iI) 
    of
    (False, _      ) -> Rsi a (iI, dg) d
    (_,     Just gs) -> Rsi (reduceCanG gs a) (iI, dg) d
    _                ->
      error $ concat ["\ncast mode r a,\nr =  ",  
                      showsn 1 r "\na = ", showsn 1 a "\nr <- ",  
                      showsDomOf 1 r "\na <- ", showsDomOf 1 a msgNoBas]


{- reserve *****************************
instance(Convertible a b,LinSolvRing b)=>Convertible a (ResidueI b)
  where  cvm a (Rsi b iD d) =     let (iI,_) = iD
    in  case  (cvm a b, idealGens iI, idealGenProps iI)  of
      (Nothing, _      , _ ) -> Nothing
      (_    , Nothing, _ ) -> error ("cvm a (Rsi _ iD _):  "++msgNoBas)
      (Just c , Just gs, ps) -> (case  lookup IsGxBasis ps
                   of Just Yes -> Just (Rsi (reduceCanG gs c) iD d)
                     _        -> Nothing      )
*******************************************
-}


------------------------------------------------------------------------
-- instances for the Quotient ring  R/I,   
-- R = baseRing x,   I  a NON-trivial  ideal in R.

instance (LinSolvRing a, Random a) => Random (ResidueI a)  
  where
  randomR (l, h) g = (ctr l a, g')  where
                              (a, g') = randomR (resRepr l, resRepr h) g

  random _ = error "\nrandom  to (ResidueI _):   use randomR instead.\n"


instance DShow a => Show  (ResidueI a) where showsPrec _ = showsn 0
instance DShow a => DShow (ResidueI a) where
                                       dShows opt = dShows opt . resRepr 

instance LinSolvRing a => Set (ResidueI a)   
  where
  compare_m  = compareTrivially   -- SO FAR
  showsDomOf = showsd_
  fromExpr   = fromexpr_

  baseSet  r@(Rsi x dI aD) dmr = 
    case  
        Map.lookup Set dmr  
    of
    Just (D1Set o) -> (dmr, o)
    _              ->
     (case  (idealGens iI, Map.lookup Set aD)
      of
      (Nothing, _                ) -> 
                              (dmr, error $ rsiMsg "baseSet" r msgNoBas)
      (_,       Nothing          ) -> 
                              (dmr, error $ rsiMsg "baseSet" r msgSetD )
      (Just gs, Just (D1Set setA)) -> rbs gs (idealGenProps iI) setA
     )
     where
     (iI, dm) = dI
     msgSetD  = "\n\nSet not found in  D.\n"
     msgGH'   = "\n\nAddGroup not found in the Ideal domain.\n"

     rbs gs genProps setA = 
       case 
           (lookupProp IsGxBasis genProps, Map.lookup AddGroup dm)  
       of
       (Unknown, _                ) ->
                              (dmr, error $ rsiMsg "baseSet" r msgGxBas)
       (No,      _                ) -> 
                              (dmr, error $ rsiMsg "baseSet" r msgGxBas)
       (_,       Nothing          ) -> 
                              (dmr, error $ rsiMsg "baseSet" r msgGH'  )
       (_,       Just (D1Group gH)) -> (Map.insert Set (D1Set o) dmr, o)
         where
         o = 
           let
             Just (D1Set setH) = Map.lookup Set dm
             gensH             = subgrGens gH
             ((_, gA), bel)    = (baseAddGroup x aD, membership setA)

             bel' 'r' r  = isCorrectRsi r 
             bel' _   r  = isCorrectRsi r  &&  (bel 'r' $ resRepr r)
             canr        = reduceCanG gs
             redRes x    = Rsi (canr x) dI aD
             (gensA, ps) = (subgrGens gA, subgrProps gA)
             (cardA, cardH) = (osetCard setA, osetCard setH)
             (finA, finH)   = (isFiniteSet setA, isFiniteSet setH)
             cycAl          = lookupProp IsCyclicGroup ps
             -----------------------------------------------------------
             props' = [(Finite,         fin'), (IsBaseSet, Yes),   
                       (FullType,       No  ),      -- for gH/={0}
                       (OrderIsTrivial, Yes ),      -- SO FAR
                       (OrderIsTotal,   No  ), 
                       (OrderIsNoether, Yes ), (OrderIsArtin, Yes)
                      ]
             fin' = case (cycAl, finA, finH) of 
                                              (Yes, _,   _  ) -> Yes
                                              (_,   Yes, _  ) -> Yes
                                              (_,   No,  Yes) -> No
                                              _               -> Unknown
             -----------------------------------------------------------
             card' = 
               case (cardA, cardH, gensA, gensH) 
               of
               (_,        Infinity, Just [g], Just [h]) -> 
                                                  Fin $ multiplicity g h
               (_,        Infinity, _,        _       ) -> UnknownV
               (_,        UnknownV, Just [g], Just [h]) -> 
                                                  Fin $ multiplicity g h
               (_,        UnknownV, _,        _       ) -> UnknownV
               (Infinity, _,        _,        _       ) -> Infinity 
               (UnknownV, _,        Just [g], Just [h]) -> 
                                                   Fin$ multiplicity g h
               (UnknownV, _,        _,        _       ) -> UnknownV
               (Fin n,    Fin m,    _,        _       ) -> 
                 if  
                   (mod n m) == 0  then  Fin $ quot n m
                 else    
                 error $ rsiMsg "baseSet" r
                                    "\n\ncard of quotient group D/H:  \
                                    \card(H) does not divide card(D).\n"
             -----------------------------------------------------------
             multiplicity x y =  
                          if x == y then 1 
                          else           succ $ multiplicity x $ sub y x
             -----------------------------------------------------------
             list' = 
               case (gensA, gensH) 
               of
               (Just [g], Just [h]) ->  
                       Just $ map redRes $ multiplesUpTo g h g [zeroS g]

               _                    ->
                      fmap (map (ct r) . nub . map canr) $ osetList setA

             multiplesUpTo x y sum zs =
                if  
                  y == sum then  zs 
                else             multiplesUpTo x y (add sum x) (sum: zs)      
             -----------------------------------------------------------
           in
           OSet {osetSample  = r,       membership  = bel', 
                 osetCard    = card',   osetPointed = Just $ Just r,
                 osetList    = list',
                 osetBounds  = (Nothing, Nothing, Nothing, Nothing),
                 osetProps   = props',
                 osetConstrs = [],      osetOpers   = []}


showsd_ verb r = showChar '(' . showsDomOf verb a . showString "/I<" . 
                 showsGs . showString ">)"
        where
        verb'   = pred verb
        (a, iI) = (resRepr r, resIdeal r)
        showsGs = case idealGens iI
                  of
                  Nothing      -> showChar '?'
                  Just []      -> id
                  Just [g]     -> showsn verb' g
                  Just (g: gs) -> showsn verb' g . showString "... a_" .
                                  shows (genLength (g: gs))


fromexpr_  r@(Rsi smp iD _)  e =  rd e        -- LOCAL
  where
  rd (E (L "-") []   [e2]) = p "-u" ([], "") (rd e2)
  rd (E (L "-") [e1] [e2]) = p "-"  (rd e1)  (rd e2)
  rd (E (L "+") [e1] [e2]) = p "+"  (rd e1)  (rd e2)
  rd (E (L "*") [e1] [e2]) = p "*"  (rd e1)  (rd e2)
  rd (E (L "/") [e1] [e2]) = p "/"  (rd e1)  (rd e2)
  rd (E (L "^") [e1] [e2]) = pw (rd e1) $ fromExpr (1 :: Integer) e2
  rd e                     = 
         case (fromExpr smp e, gsM, lookupProp IsGxBasis ps)
         of
         (_,         Nothing, _      ) -> error $ msg msgNoBas
         (_,         _,       No     ) -> error $ msg msgGxBas
         (_,         _,       Unknown) -> error $ msg msgGxBas
         (([x], ""), Just gs, _      ) -> ([ct r $ reduceCanG gs x], "")
         ((_,   ms), _,       _      ) -> ([], msg (msg' ++ ms))

  iI        = fst iD
  (gsM, ps) = (idealGens iI, idealGenProps iI)
  msg       = showString "\nfromExpr r e,\nr = " . showsn 1 r . 
              showString "\n <- D/I =  " . showsDomOf 1 r
  msg'      = "\n\nCould not read  e  by the sample  r.\n\n"

  p "-u" _         ([f], "") = ([-f],  "")
  p "-"  ([f], "") ([g], "") = ([f-g], "")
  p "+"  ([f], "") ([g], "") = ([f+g], "")
  p "*"  ([f], "") ([g], "") = ([f*g], "")
  p "/"  ([f], "") ([g], "") = 
                 case  divide_m f g  
                 of
                 Just q -> ([q], "")
                 _      -> ([],  msg "\n\nFailed to divide with `/'.\n")

  p _    ([_], "") pair     = pair
  p _    pair      _        = pair

  pw ([f], "" ) ([n], "" ) = ([f^n], "" )
  pw ([_], "" ) (_,   msg) = ([],    msg)
  pw (_,   msg) ([_], "" ) = ([],    msg)


{- old --------------------------------------------------------
fromexpr_  r@(Rsi smp iD _)  e =  
  (case (fromExpr smp e, gsM, lookupProp IsGxBasis ps) of
    (_       , Nothing, _      ) -> error $ msg msgNoBas
    (_       , _      , No     ) -> error $ msg msgGxBas
    (_       , _      , Unknown) -> error $ msg msgGxBas
    (([x],""), Just gs, _      ) -> ([ct r $ reduceCanG gs x], "")
    ((_  ,ms), _      , _      ) ->
         ([], msg ("\n\nCould not read  e  by the sample  r\n\n"++ms))
  ) where   iI        = fst iD
  (gsM, ps) = (idealGens iI, idealGenProps iI)
  msg       = ("fromExpr r e, \n"++) . ("r = "++) . shows r . 
              ("\n <- D/I =  "++) . showsDomOf r
  msg'      = "\n\nCould not read  e  by the sample  r\n\n"
------------------------------------------------------------------
-}



--------------------------------------------------------------------
instance LinSolvRing a => AddSemigroup (ResidueI a)  
  where
  zero_m  r = Just $ ct  r $ zeroS $ resRepr r
  neg_m   r = Just $ ctr r $   neg $ resRepr r
  add     r = ctr r . add (resRepr r) . resRepr
  times_m r = Just . ctr r . times (resRepr r)
 
  baseAddSemigroup  r@(Rsi x iD aD) dmr =  
   let
     zr          = zeroS x
     (aD', _   ) = baseSet x aD
     (aD1, smgA) = baseAddSemigroup x aD'
     (_,   gA  ) = baseAddGroup x aD1
     gensA       = subgrGens gA
     (_,   dm  ) = iD

     gH_m              = Map.lookup AddGroup dm
     Just (D1Group gH) = gH_m
     can_m             = subgrCanonic gH
     Just canr         = can_m
     smgAProps         = subsmgProps smgA
     (dmr', setRes)    = baseSet r dmr

     props'= [(Commutative,           Yes    ), (IsGroup, Yes),
              (IsMaxSubsemigroup,     No     ),
              (IsOrderedSubsemigroup, Unknown),  -- SO FAR
              (IsCyclicSemigroup,     cyc'   )   
             ]
     cyc' = case (lookup IsCyclicSemigroup smgAProps, osetCard setRes)
            of                                   
            (Just Yes, _    ) -> Yes
            (_,        Fin n) -> if isPrime n then Yes  
                                 else              Unknown
            _                 -> Unknown  -- further possible solutions?

     gens' = 
        case (gensA, osetList setRes)  
        of                        -- many optimizations are possible ***
        (Just xs, _        ) -> 
                  Just $ map (ct r) $ nub $ filter (/= zr) $ map canr xs
 
        (_,       Just ress) -> Just $ gensModulo ress
                                           where 
                                           gensModulo xs = xs  -- so far
        _                    -> Nothing

     s = Subsemigroup
                {subsmgType    = Add,    subsmgUnity = Just (zero_m r),
                 subsmgGens    = gens',  subsmgProps = props',
                 subsmgConstrs = [],     subsmgOpers = []  }
     -------------------------------------------------------------------
   in
   case (Map.lookup AddSemigroup dmr, gH_m, can_m)
   of
   (Just (D1Smg s), _,       _      ) -> (dmr, s)
   (_,              Nothing, _      ) -> 
                        (dmr, error $ rsiMsg "baseAddSemigroup" r msgGH)
   (_,              _,       Nothing) -> 
                        (dmr, error $ rsiMsg "baseAddSemigroup" r msgGH)
   _                                  ->
                             (Map.insert AddSemigroup (D1Smg s) dmr', s)


------------------------------------------------------------------------
instance LinSolvRing a => AddMonoid (ResidueI a)
instance LinSolvRing a => AddGroup  (ResidueI a)   
  where
  baseAddGroup  r@(Rsi x iD aD) dmr = 
    let
      (zr, (_, dm))     = (zeroS x, iD)
      gH_m              = Map.lookup AddGroup dm
      Just (D1Group gH) = gH_m
      can_m             = subgrCanonic gH
      Just canr         = can_m
      (dom1, setRes)    = baseSet r dmr
      (dom2, _)         = baseAddSemigroup r dom1
      canForRes         = const (zeroS r)
                                -- for the base subgroup is the full one
      dA = upAddGroup x aD

      Just (D1Group gA)   = Map.lookup AddGroup dA
      (gens_gA, props_gA) = (subgrGens gA, subgrProps gA)

      props' = [(IsNormalSubgroup,  Yes   ),
                (IsMaxSubgroup,     No    ), 
                (IsOrderedSubgroup, No    ),   -- SO FAR            
                (IsCyclicGroup,     cyc'  ),
                (IsPrimeGroup,      prime')
               ]
      prime' = case (lookup IsPrimeGroup props_gA, primeCard)
               of
               (Just Yes, _   ) -> Yes
               (_,        True) -> Yes
               _                -> Unknown

      primeCard = case osetCard setRes of Fin n -> isPrime n
                                          _     -> False

      cyc' = case (lookup IsCyclicGroup props_gA, primeCard)
             of
             (Just Yes, _   ) -> Yes
             (_,        True) -> Yes
             _                -> Unknown

      gens' = 
          case (gens_gA, osetList setRes)
          of                      -- many optimizations are possible ***
          (Just xs, _        ) -> 
                  Just $ map (ct r) $ nub $ filter (/= zr) $ map canr xs
                
          (_,       Just ress) -> Just $ gensModulo ress
                                         where 
                                         gensModulo xs = xs   -- so far
          _                    -> Nothing

      g = Subgroup {subgrType    = Add,             subgrGens  = gens', 
                    subgrCanonic = Just canForRes,  subgrProps = props',
                    subgrConstrs = [],              subgrOpers = []}
      ------------------------------------------------------------------
    in
    case (Map.lookup AddGroup dmr, gH_m, can_m)
    of
    (Just (D1Group g), _,       _      ) -> (dmr, g)
    (_,                Nothing, _      ) ->
                            (dmr, error $ rsiMsg "baseAddGroup" r msgGH)

    (_,                _,       Nothing) ->
                            (dmr, error $ rsiMsg "baseAddGroup" r msgGH)
    _                                    ->
                               (Map.insert AddGroup (D1Group g) dom2, g)
                                  

------------------------------------------------------------------------
instance LinSolvRing a => MulSemigroup (ResidueI a)
  where
  unity_m r = Just $ ctr r $ unity $ resRepr r
  mul     r = ctr r . mul (resRepr r) . resRepr
     
  divide_m  r1@(Rsi x iD d)  r2@(Rsi y _ _) =  
    let
      (iI, _)      = iD
      (props, gsM) = (idealGenProps iI, idealGens iI)
    in
    (case (gsM, lookup IsGxBasis props)
     of
     (Just gs, Just Yes) -> dv gs $ moduloBasis "" (y:gs) x
     _                   ->
          error $ concat ["\ndivide_m r1 r2,\nr1 = ", showsn 1 r1 $ 
                          showsWithDom 1 r2 "r2" "" msgGxBas]
    )
    where
    dv gs (x1, q:_) = 
                    if isZero x1 then  Just $ Rsi (reduceCanG gs q) iD d
                    else               Nothing
                   
  divide_m2 _ _ = 
             error "\ndivide_m2 (Rsi ..) _:   use  divide_m  instead.\n"
  root _ _ = error "\nroot _ (Rsi ..):   it is not defined for  \
                   \..=> ResidueI a  so far.\n"

  -- inv_m, power   are the default ones.

  baseMulSemigroup r dmr =  
    case
        (Map.lookup MulSemigroup dmr, resIdeal r) 
    of
    (Just (D1Smg s), _ ) -> (dmr, s)
    (_,              iI) ->
      (case (idealGens iI, idealGenProps iI)
       of
       (Just _, ps) -> smg ps
       _            -> 
                     (dmr, error $ rsiMsg "baseMulSemigroup" r msgGxBas)
      )
      where
      smg ps =
        let
          unR   = unity r
          props = [(Commutative,           Yes    ), (IsGroup,No),
                   (IsMaxSubsemigroup,     No     ),
                   (IsOrderedSubsemigroup, Unknown),  
                   (IsCyclicSemigroup,     No     )   
                                      -- because 0,1 <- subsemigroup
                  ]
          s = Subsemigroup {subsmgType    = Mul,
                            subsmgUnity   = Just $ Just unR,
                            subsmgGens    = Nothing, -- so far
                            subsmgProps   = props,
                            subsmgConstrs = [], 
                            subsmgOpers   = []}
        in
        case lookup IsGxBasis ps
        of
        Just Yes -> (Map.insert MulSemigroup (D1Smg s) dmr, s)
        _        -> (dmr, error $ rsiMsg "baseMulSemigroup" r msgGxBas)


------------------------------------------------------------------------
instance (LinSolvRing a, MulMonoid a) => MulMonoid (ResidueI a)

instance LinSolvRing a => Num (ResidueI a)  
  where  
  negate = neg
  (+)    = add
  (-)    = sub  
  (*)    = mul
  signum _ = 
         error "\nsignum (Rsi ..):  it is senseless for residue ring.\n"
  abs  _ = error "\nabs (Rsi ..):  it is senseless for residue ring.\n"
  fromInteger _ = 
      error 
      "\nfromInteger  to (ResidueI _):  use  fromi, fromi_m  instead.\n"

instance LinSolvRing a => Fractional (ResidueI a)  
  where
  (/) = divide
  fromRational _ = error "\nfromRational   to (ResidueI _):\ninstead \
                       \use  fromi, fromi_m  combined with  divide_m.\n"
