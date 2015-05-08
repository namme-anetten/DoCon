------------------------------------------------------------------------
------------------------------------------------------------------------
--  The Algebraic Domain Constructor  DoCon,   version 2.12
--
--  Copyright  Serge Mechveliani,    2012
------------------------------------------------------------------------
------------------------------------------------------------------------




module Set_   -- Set category,  OSet data  and related items.
              -- All needed from here is  reexported by  SetGroup.
(Set(..), OrderedSet(),
 compareTrivially, isFiniteSet, isBaseSet, intervalFromSet, card,
 ofFiniteSet, isoOSet, props_set_full_trivOrd, listToSubset, less_m, 
 lessEq_m, greater_m, greaterEq_m, incomparable, showsWithDom   
)
where
import qualified Data.Map as Map (empty)

import Data.Maybe (fromMaybe, isJust)
import Data.List  (find)

import Categs (Domains1, OSet(..), Properties_OSet, Property_OSet(..),  
                                                  Construction_OSet(..))
import Prelude_ (Length(..), DShow(..), -- class
                 Natural, PropValue(..), InfUnn(..), CompValue, 
                 Verbosity,  lookupProp, fmapmap, fmapfmap, showsn
                )
import Iparse_ (Expression(..))
import Common_ (minPartial, maxPartial)





------------------------------------------------------------------------
class (Eq a, Show a, DShow a) => Set a          -- partially ordered set
  where  
  compare_m  :: a -> a -> Maybe CompValue            -- partial ordering
  showsDomOf :: Verbosity -> a -> String -> String   -- for messages
                          -- sa
  fromExpr   :: a -> Expression String -> ([a], String)         -- parse
             -- sa   e                          messg

  baseSet    :: a -> Domains1 a -> (Domains1 a, OSet a)
             -- sa                              description of set 

-- compare_m    
-- needs *not* necessarily agree with `compare' of Ord.  For example, 
-- it agrees with `compare' for Char, but may differ for [Char].
--
-- showsDomOf verb x str --> str'   
--                    prints to string the short description of domain
--                    defined by the sample  x.  Used in error messages.
--
-- baseSet x dom --> (dom',o),    dom' = addToFM dom Set (...o).
--                                o  is either found in  dom  or built 
--                                   according to the construction of x.

------------------------------------------------------------------------
compareTrivially :: Eq a => a -> a -> Maybe CompValue
compareTrivially            x    y = if x==y then Just EQ  else  Nothing

isFiniteSet, isBaseSet :: OSet a -> PropValue

isFiniteSet = fromMaybe Unknown . lookup Finite    . osetProps
isBaseSet   = fromMaybe Unknown . lookup IsBaseSet . osetProps

intervalFromSet :: OSet a -> Maybe (Construction_OSet a)
                                      -- extract
                                      -- first interval construction
intervalFromSet set = find isInterval (osetConstrs set)
                               where
                               isInterval (Interval _ _ _ _) = True
                               isInterval _                  = False

card :: Set a => a -> InfUnn Natural
card             a =  case  baseSet a Map.empty of (_, s) -> osetCard s

ofFiniteSet :: Set a => a -> PropValue
ofFiniteSet a =  case  baseSet a Map.empty  of (_, s) -> isFiniteSet s

showsWithDom :: 
         Set a => Verbosity -> a -> String -> String -> String -> String
showsWithDom      verb         x    xName     domName =

  showChar '\n' . showString xName . showString " =  " . showsn verb x . 
  showString ("\n <-  " ++ domName) . showString eqSymbol . 
  showsDomOf verb x . showChar '\n'
  where  
  eqSymbol = if  null domName  then "" else " =  "

------------------------------------------------------------------------
isoOSet :: (a -> b) -> (b -> a) -> OSet a -> OSet b

-- For a given  oset  on the type `a',  
--                    a map  f: a -> b  which is an injection on  oset,
--                    its inverse  f_inv
-- produce the isomorphic copy of  oset  on `b'.

isoOSet f f_inv oset = 
  let
    OSet {osetSample = smp,   membership  = bel,
          osetCard   = card,  osetPointed = el,       
          osetList   = ll,    osetBounds  = bounds,       
          osetProps  = props, osetConstrs = conss} =  oset

    [b1', b2', b3', b4'] = 
                   case bounds  
                   of
                   (b1, b2, b3, b4) -> map (fmapfmap f) [b1, b2, b3, b4]
  in
  OSet {osetSample  = f smp,
        membership  = (\ m-> bel m . f_inv),
        osetCard    = card,
        osetPointed = fmapfmap f el,
        osetList    = fmapmap f ll,
        osetBounds  = (b1', b2', b3', b4'),
        osetProps   = props,
        osetConstrs = map (isoConstruction_OSet f f_inv) conss,
        osetOpers   = []}

------------------------------------------------------------------------
isoConstruction_OSet :: (a -> b) -> (b -> a) -> Construction_OSet a ->
                                                Construction_OSet b
isoConstruction_OSet f _fInv constr = 
  case constr  
  of
  Interval lb cl ub cu -> Interval (fmap f lb) cl (fmap f ub) cu

  -- (Union        sets) -> Union $ map (isoOSet f fInv) sets
  --                                                  !?
  -- (Intersection sets) -> Intersection $ map (isoOSet f fInv) sets
  -- ...

------------------------------------------------------------------------
listToSubset ::  
              Set a =>  [a] -> [Construction_OSet a] -> OSet a -> OSet a
                     -- xs     conss
-- Make a Listed Proper subset in the base set BS. 
-- Only those elements of  xs  remain which belong to the BS.
-- conss  overwrites the construction list.
-- See how the bounds and the property change. 

listToSubset xs newConss base =  
  let  
    (smp, bel, boundsB, props) = (osetSample base, membership base,
                                  osetBounds base, osetProps base
                                 )
    xs'                = filter (bel 'r') xs
    propsEmptyOrSingle = [(Finite,       Yes), (FullType,       No ),
                          (IsBaseSet,    No ), (OrderIsNoether, Yes), 
                          (OrderIsArtin, Yes), (OrderIsTrivial, Yes),
                          (OrderIsTotal, Yes)]
  in
  case xs'  
  of
  []  -> OSet {osetSample  = smp,
               membership  = (\ _ _ -> False), 
               osetCard    = Fin 0,
               osetPointed = Just Nothing,
               osetList    = Just [],
               osetBounds  = (Nothing, Nothing, Nothing, Nothing),
               osetProps   = propsEmptyOrSingle,
               osetConstrs = [],
               osetOpers   = []
              }                  
  [x] -> OSet {osetSample  = smp,
               membership  = (\_ y -> y == x), 
               osetCard    = Fin 1,
               osetPointed = Just $ Just x,
               osetList    = Just [x],
               osetBounds  = (Just $ Just x, Just $ Just x,
                              Just $ Just x, Just $ Just x),
               osetProps   = propsEmptyOrSingle,
               osetConstrs = [],
               osetOpers   = []}                  

  _   -> OSet {osetSample  = smp,
               membership  = (\ _ y -> elem y xs'), 
               osetCard    = Fin lng,
               osetPointed = el',
               osetList    = Just xs',
               osetBounds  = (low', upper', inf', sup'), 
               osetProps   = props',
               osetConstrs = newConss,
               osetOpers   = []}
      where
      lng     = genLength xs'
      min_xs' = minPartial compare_m xs'
      max_xs' = maxPartial compare_m xs'
      el'     = if  null xs'  then  Just Nothing  
                else                Just $ Just $ head xs'
      ------------------------------------------------------------------
      (lowB, upperB, infB, supB) = boundsB

      justOrOther (Just v) _ = Just $ Just v
      justOrOther _        y = y

      low'   = justOrOther min_xs' lowB
      upper' = justOrOther max_xs' upperB
      inf'   = justOrOther min_xs' infB
      sup'   = justOrOther max_xs' supB
      ------------------------------------------------------------------
                                            -- ordered subset properties 
      triv = lookupProp OrderIsTrivial props
      tot  = lookupProp OrderIsTotal   props
      isInterval = any isIntv newConss  where  
                                       isIntv (Interval _ _ _ _) = True
                                       isIntv _                  = False

      props' = [(Finite,         Yes  ), (FullType,     No),
                (IsBaseSet,      No   ),
                (OrderIsNoether, Yes  ), (OrderIsArtin, Yes),
                (OrderIsTrivial, triv'), (OrderIsTotal, tot')]
    
      triv' = case (triv, lng, tot == Yes || isInterval) of
                                               (Yes, _, _   ) -> Yes
                                               (_,   0, _   ) -> Yes
                                               (_,   1, _   ) -> Yes
                                               (_,   _, True) -> No
                                               _              -> Unknown

       -- Should we define this more definitely ?   ********
       -- - as  let  eqOrIncomp x y =  x==y || (compare_m x y)==Nothing
       --       in
       --       case  and [(eqOrIncomp x y)|  x<-xs, y<-xs]  of
       --                                               True -> Yes
       --                                               _    -> No
       -- Similar is  total'.
       -- *****************************************************

      tot' = case (tot == Yes || isInterval, lng, triv) of 
                                               (True, _, _  ) -> Yes
                                               (_,    0, _  ) -> Yes
                                               (_,    1, _  ) -> Yes
                                               (_,    _, Yes) -> No
                                               _              -> Unknown



{- probably, unnecessary: *********************************
instance  Set Property_OSet   where    
  fromExpr _ (L "Finite"    ) =  ([Finite]   , "")
  fromExpr _ (L "IsBaseSet" ) =  ([IsBaseSet], "")
  ...
  fromExpr _ e = ([] , "wrong expression for type Property_OSet:  "
                                                ++ (showsExpr e ""))
  compare_m =  compareTrivially  
  baseSet _ =  OSet  Finite (const True) (Just 7) 
                     (Just (Just Finite))
                     (Just [Finite,FullType,IsBaseSet ... ]
                     )  (Nothing,Nothing,Nothing,Nothing) 
                        props_set_full_trivOrd  [] []
***********************************************************
-}


------------------------------------------------------------------------
props_set_full_trivOrd = [(Finite,       Yes), (FullType,       Yes),
                          (IsBaseSet,    Yes), (OrderIsTrivial, Yes), 
                          (OrderIsTotal, No ), (OrderIsNoether, Yes), 
                          (OrderIsArtin, Yes)]        :: Properties_OSet

------------------------------------------------------------------------
class (Ord a, Set a) => OrderedSet a    

-- Presumed: 
-- on the base set BS,  compare_m  possesses (OrderIsTotal,Yes),
--                      and agrees with `compare':
--                               (compare_m x y) == (Just (compare x y))

------------------------------------------------------------------------
less_m, lessEq_m, greater_m, greaterEq_m, incomparable :: 
                                                 Set a => a -> a -> Bool

less_m    x y =  case  compare_m x y  of  Just LT -> True
                                          _       -> False
greater_m x y =  case  compare_m x y  of  Just GT -> True
                                          _       -> False

incomparable x = not . isJust . compare_m x

lessEq_m    x y =  x == y  ||  less_m    x y
greaterEq_m x y =  x == y  ||  greater_m x y
