------------------------------------------------------------------------
------------------------------------------------------------------------
--  The Algebraic Domain Constructor  DoCon,   version 2.12
--
--  Copyright  Serge Mechveliani,    2012
------------------------------------------------------------------------
------------------------------------------------------------------------






module DPrelude   -- DoCon Prelude
  (
   sublists, listsOverList, smParse,

   -- from Prelude_:
   Length(..), IsSingleton(..), Cast(..), DShow(..),  -- classes
   PropValue(..), InfUnn(..), MMaybe, CompValue, Comparison,
   Z, Natural,  Verbosity, ParensOrNot(..), ShowOptions(..),
   tuple31, tuple32, tuple33,  tuple41, tuple42, tuple43, tuple44,
   tuple51, tuple52, tuple53, tuple54, tuple55,
   setTuple21, setTuple22, setTuple31, setTuple32, setTuple33,
   setTuple41, setTuple42, setTuple43, setTuple44,
   setTuple51, setTuple52, setTuple53, setTuple54, setTuple55,
   mapTuple21, mapTuple22,
   mapTuple31, mapTuple32, mapTuple33,
   mapTuple41, mapTuple42, mapTuple43, mapTuple44,
   mapTuple51, mapTuple52, mapTuple53, mapTuple54, mapTuple55,
  
   zipRem, allMaybes, compose, mapmap, fmapmap, mapfmap, fmapfmap,
   boolToPropV, propVToBool, not3, and3, or3,  compBy,  delBy, 
   separate, pairNeighbours, removeFromAssocList, addToAssocList_C,
   addListToAssocList_C, propVOverList,  mbPropV, lookupProp,  
   updateProps, addUnknowns,  takeAsMuch, dropAsMuch,
   addListToMap, addListToMapWith,
   antiComp, minBy, maxBy, minimum, maximum, minAhead, maxAhead,
   ct, ctr,  toZ, fromZ,
   pageWidth, defaultVerbosity, defaultListSeparator, changeSeparator,
   defaultFieldSeparator, defaultShowOptions, addToShowOptions, shOpt, 
   showsn, shown, showsWithPreNLIf, showWithPreNLIf, showsByInit, 
   unparensUpper, showUnparensUpper, showsUnparensUpper, 
   showWithNLUnparensUpper, showsWithNLUnparensUpper,

   -- from Iparse_:
   Expression(..), OpDescr, OpTable, ParenTable, lexLots, infixParse,

   parenTable, opTable,   -- from OpTab_ 

   module List_,

   -- from Common_:
   partitionN, eqListsAsSets, del_n_th, halve, mulSign, invSign, 
   evenL, factorial, binomCoefs, isOrderedBy, mergeBy, mergeE, sort,
   sortBy, sortE,  sum1, product1, alteredSum, sum1byBinary,
   lexListComp,  minPartial, maxPartial,

   -- from Set_:
   less_m, lessEq_m, greater_m, greaterEq_m, incomparable, 
   showsWithDom,

   module System_   
  ) 

where   
import Prelude hiding (maximum, minimum)
import Prelude_
import Iparse_
import OpTab_
import Common_
import System_
import Set_ (Set(..),  less_m, lessEq_m, greater_m, greaterEq_m, 
                                         incomparable, showsWithDom)
import Char_ ()
import List_





------------------------------------------------------------------------
sublists :: [a] -> [[a]]
sublists []      =  [[]]
sublists (x: xs) =  (map (x:) ls) ++ ls  where  ls = sublists xs


listsOverList :: Natural -> [a] -> [[a]]

-- list of all lists of length  n  with the elements from  xs.
-- It does Not take notice of the repetitions in  xs.

listsOverList 0 _  = [[]]
listsOverList n [] = error ("\nlistsOverList " ++ (shows n " [].\n"))
listsOverList n xs =
  if
    n < 0  then  error ("\nlistsOverList " ++ (shows n
                                         " xs:     n > 0  required.\n"))
  else
  ll n xs  where  ll 0 _  = [[]]
                  ll n xs = concat [map (: l) xs | l <- ll (pred n) xs]
                                  -- probably,
                                  -- this concat needs optimization ***

------------------------------------------------------------------------
smParse :: Set a => a -> String -> a

-- Generic parsing by sample.
-- Makes use  of  infixParse, fromExpr.
-- See  infixParse  in Iparse.hs,  fromExpr  of Set class.

smParse sample s = 
  case  
      infixParse parenTable opTable$ lexLots s  
  of
  ([e], "") -> case  fromExpr sample e  
               of
               ([x], "" ) -> x
               (_,   msg) -> 
                   error $ 
                   showString "\nfromExpr sample str:  bad string." $
                   showsWithDom 1 sample "sample" "" ('\n': (msg++"\n"))

  (_,   msg) -> error ("\ninfixParse:  " ++ (msg ++ "\n"))
