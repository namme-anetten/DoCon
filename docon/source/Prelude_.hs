----------------------------------------------------------------------------
----------------------------------------------------------------------------
--  The Algebraic Domain Constructor  DoCon,   version 2.12
--
--  Copyright  Serge Mechveliani,    2012
----------------------------------------------------------------------------
----------------------------------------------------------------------------





module Prelude_   -- Initial part of the DoCon prelude.
                  -- All needed from here is  reexported by  DPrelude.

  (Length(..), IsSingleton(..), DShow(..), Cast(..),   -- classes
   Verbosity, ParensOrNot(..), ShowOptions(..),
   PropValue(..), InfUnn(..), MMaybe, CompValue, Comparison,  Z, Natural, 
   tuple31, tuple32, tuple33,  tuple41, tuple42, tuple43, tuple44,
   tuple51, tuple52, tuple53, tuple54, tuple55,
   setTuple21, setTuple22, setTuple31, setTuple32, setTuple33,
   setTuple41, setTuple42, setTuple43, setTuple44,
   setTuple51, setTuple52, setTuple53, setTuple54, setTuple55,
   mapTuple21, mapTuple22,
   mapTuple31, mapTuple32, mapTuple33,
   mapTuple41, mapTuple42, mapTuple43, mapTuple44,
   mapTuple51, mapTuple52, mapTuple53, mapTuple54, mapTuple55,

   ct, ctr, toZ, fromZ, 
   zipRem, allMaybes, compose,  mapmap, fmapmap, mapfmap, fmapfmap,
   boolToPropV, propVToBool, not3, and3, or3,  compBy,  delBy, separate, 
   pairNeighbours, removeFromAssocList, addToAssocList_C, 
   addListToAssocList_C, propVOverList, addListToMap, addListToMapWith,  
   updateProps, mbPropV, lookupProp, addUnknowns,  takeAsMuch, 
   dropAsMuch, antiComp,  minBy, maxBy, minimum, maximum, minAhead, 
   maxAhead,
   pageWidth, defaultVerbosity, defaultListSeparator, changeSeparator, 
   defaultFieldSeparator, defaultShowOptions, addToShowOptions, shOpt, 
   showsn, shown, showsWithPreNLIf, showWithPreNLIf, showsByInit, 
   unparensUpper, showUnparensUpper, showsUnparensUpper, 
   showWithNLUnparensUpper, showsWithNLUnparensUpper

   -- instances
   --  for []  :  Length IsSingleton,
   --  for Set :  IsSingleton,
   --  for Map :  IsSingleton
  ) 
where   
import qualified Data.Set as Set (Set(..), toList)
import qualified Data.Map as Map (Map(..), keys, fromList, toList, 
                                                 union, unionWith)

import Data.List (delete, genericLength, genericReplicate, intersperse)
import Prelude hiding (maximum, minimum)



------------------------------------------------------------------------
type Z       = Integer    -- IGNORE Int !
type Natural = Integer    -- presumed:  >= 0

toZ :: Integral a => a -> Z
toZ =  toInteger
{-# specialize toZ :: Int -> Z,  Integer -> Z #-}

fromZ :: Num a => Z -> a
fromZ =  fromInteger
{-# specialize fromZ :: Z -> Int,  Z -> Integer #-}

------------------------------------------------------------------------
data InfUnn a = Fin a | Infinity | UnknownV  deriving (Eq, Show, Read)
--
-- Example:
-- setCardinality(sS) = osetCard sS  :: InfUnn Z  may yield 
--   Fin n,    n Natural, or
--   Infinity,            or
--   UnknownV

instance Functor InfUnn  where  fmap f (Fin a)  = Fin (f a)
                                fmap _ Infinity = Infinity
                                fmap _ UnknownV = UnknownV

------------------------------------------------------------------------
class Cast a b where  cast :: Char -> a -> b -> a
                              --mode

  -- cast mode a b  means  cast  b  to domain of sample  `a'.
  --
  -- mode = 'r'        means the additional correction to perform,
  --        any other  means to project "as it is".
  --
  -- Examples.
  -- * Map coefficient c <- R to polynomial domain R[x1..xn]:
  --   cast mode pol c,
  --   mode = 'r'  means here the  check  c == zero  is needed,
  --   other mode  is usually set when  c  is known as non-zero.
  --
  -- * Projection  R -> R/I  to residue ring, 
  --   say, R = Z,  I = Ideal(g),  g > 1,  res <- R/I,  n <- R,  and
  --   cast mode res n   projects  n  to  R/I.
  --   mode = 'r'  
  --       takes first the remainder by g (g contained in res data),
  --   other mode  has sense when it is known that  0 <= n < g.

ct, ctr ::  Cast a b => a -> b -> a
ct  = cast '_'
ctr = cast 'r'

tuple31 (x,_,_) = x       -- there comes the language extension
tuple32 (_,x,_) = x       -- where these tuple things will be done
tuple33 (_,_,x) = x       -- nicer
                          --
tuple41 (x,_,_,_) = x     --
tuple42 (_,x,_,_) = x
tuple43 (_,_,x,_) = x
tuple44 (_,_,_,x) = x

tuple51 (x,_,_,_,_) = x
tuple52 (_,x,_,_,_) = x
tuple53 (_,_,x,_,_) = x
tuple54 (_,_,_,x,_) = x
tuple55 (_,_,_,_,x) = x

setTuple21 (_, y) x = (x, y)
setTuple22 (y, _) x = (y, x)

setTuple31 (_, y, z) x = (x, y, z)
setTuple32 (y, _, z) x = (y, x, z)
setTuple33 (y, z, _) x = (y, z, x)

setTuple41 (_, y, z, u) x = (x, y, z, u)
setTuple42 (y, _, z, u) x = (y, x, z, u)
setTuple43 (y, z, _, u) x = (y, z, x, u)
setTuple44 (y, z, u, _) x = (y, z, u, x)

setTuple51 (_, y, z, u, v) x = (x, y, z, u, v)
setTuple52 (y, _, z, u, v) x = (y, x, z, u, v)
setTuple53 (y, z, _, u, v) x = (y, z, x, u, v)
setTuple54 (y, z, u, _, v) x = (y, z, u, x, v)
setTuple55 (y, z, u, v, _) x = (y, z, u, v, x)

mapTuple21 f (x, y) =  (f x, y  )
mapTuple22 f (x, y) =  (x,   f y)

-- example:  mapTuple32 succ ('x', 2, 3) = ('x', 3, 3)

mapTuple31 :: (a -> d) -> (a, b, c) -> (d, b, c)
mapTuple31 f tuple =  setTuple31 tuple (f $ tuple31 tuple)

mapTuple32 f tuple =  setTuple32 tuple (f $ tuple32 tuple)
mapTuple33 f tuple =  setTuple33 tuple (f $ tuple33 tuple)

mapTuple41 f tuple =  setTuple41 tuple (f $ tuple41 tuple)
mapTuple42 f tuple =  setTuple42 tuple (f $ tuple42 tuple)
mapTuple43 f tuple =  setTuple43 tuple (f $ tuple43 tuple)
mapTuple44 f tuple =  setTuple44 tuple (f $ tuple44 tuple)

mapTuple51 f tuple =  setTuple51 tuple (f $ tuple51 tuple)
mapTuple52 f tuple =  setTuple52 tuple (f $ tuple52 tuple)
mapTuple53 f tuple =  setTuple53 tuple (f $ tuple53 tuple)
mapTuple54 f tuple =  setTuple54 tuple (f $ tuple54 tuple)
mapTuple55 f tuple =  setTuple55 tuple (f $ tuple55 tuple)


type CompValue = Ordering           -- `Ordering' is from Haskell-98
                                    -- and it does not sound well
type Comparison a = a -> a -> CompValue

type MMaybe a = Maybe (Maybe a)

  -- Example of usage:
  -- subsmgUnity sS -> 
  --     Just (Just u)   means here the unity  u  is found in sS,
  --     Just Nothing    - sS does not contain unity,
  --     Nothing         - cannot determine whether such  u  exists.

data PropValue = Yes | No| Unknown  
                           deriving (Eq, Ord, Enum, Show, Read)
------------------------------------------------------------------------
not3 :: PropValue -> PropValue
not3    Yes       =  No
not3    No        =  Yes
not3    _         =  Unknown

and3, or3 :: PropValue -> PropValue -> PropValue

and3    Yes  Yes = Yes
and3    No   _   = No
and3    _    No  = No
and3    _    _   = Unknown

or3    Yes  _   = Yes
or3    _    Yes = Yes
or3    No   No  = No
or3    _    _   = Unknown

boolToPropV :: Bool -> PropValue
boolToPropV    b    =  if  b  then Yes  else No

propVToBool :: PropValue -> Bool 
propVToBool    Yes       =  True
propVToBool    _         =  False
------------------------------------------------------------------------
compBy :: Ord b => (a -> b) -> Comparison a
compBy f x y = compare (f x) (f y)          
  -- 
  -- Usable tool to define comparison. Examples:
  -- compBy snd         compares pairs by second component,
  -- compBy (abs .snd)  -      by absolute value of second component


-- BEGIN  **************************************************************
-- suggestion for Haskell library? 

mapmap :: (a -> b) -> [[a]] -> [[b]]
mapmap    f        =  map (map f)

fmapmap :: Functor c => (a -> b) -> c [a] -> c [b]
fmapmap                 f        =  fmap (map f)

mapfmap :: Functor c => (a -> b) -> [c a] -> [c b]
mapfmap                 f        =  map (fmap f)

fmapfmap :: (Functor c, Functor d) => (a -> b) -> c (d a) -> c (d b)
fmapfmap                              f        =  fmap (fmap f)

allMaybes :: [Maybe a] -> Maybe [a]  -- taken from (non-standard) Maybes
                                     -- of `misc' and somewhat optimized
allMaybes ms = a [] ms  where
                        a xs []            = Just $ reverse xs
                        a xs (Just x : ms) = a (x: xs) ms
                        a _  _             = Nothing

compose :: [a -> a] -> a -> a
compose =  foldr (.) id

takeAsMuch, dropAsMuch  :: [a] -> [b] -> [b]

takeAsMuch (_: xs) (y: ys) =  y: (takeAsMuch xs ys)
takeAsMuch _       _       =  []

dropAsMuch xs ys =  case (xs, ys) of 
                                  ([],     _     ) -> ys
                                  (_,      []    ) -> []
                                  (_: xs', _: ys') -> dropAsMuch xs' ys'


zipRem :: [a] -> [b] -> ([(a, b)], [a], [b])

  -- zip preserving remainders. Example:
  -- for  xs = [1,2]  zipRem xs (xs++[3]) = ([(1,1),(2,2)], [], [3])

zipRem []      ys      = ([], [], ys)
zipRem xs      []      = ([], xs, [])
zipRem (x: xs) (y: ys) = ((x,y): ps, xs', ys')  
                                    where  (ps, xs', ys') = zipRem xs ys

delBy :: (a -> Bool) -> [a] -> [a]  
delBy _ []      = []        
delBy p (x: xs) = if  p x  then  xs  else  x: (delBy p xs)

separate :: Eq a => a -> [a] -> [[a]]
  --
  -- break list to lists separated by given separator
  -- Example:  ';' -> "ab;cd;;e f " -> ["ab", "cd", "", "e f "]
  --
separate _ [] = []
separate a xs = case  span (/= a) xs  of
                                      (ys, []   ) -> [ys]
                                      (ys, _: zs) -> ys: (separate a zs)

pairNeighbours :: [a] -> [(a, a)]
pairNeighbours (x: y: xs) = (x, y): (pairNeighbours xs)
pairNeighbours _          = []

removeFromAssocList :: Eq a => [(a, b)] -> a -> [(a, b)]

removeFromAssocList []                _  = []
removeFromAssocList ((x', y): pairs)  x  =  
              if 
                 x == x'  then  pairs
              else              (x', y): (removeFromAssocList pairs x)

addToAssocList_C :: 
                 Eq a => (b -> b -> b) -> [(a, b)] -> a -> b -> [(a, b)]
                         -- c
              -- combines with the previous binding: when a key is
              -- in the list, it binds with  (c oldValue newValue)

addToAssocList_C c pairs key value = add pairs 
  where
  add []          = [(key, value)] 
  add ((k,v): ps) = if  k /= key then  (k, v)        : (add ps)
                    else               (k, c v value): ps  

addListToAssocList_C :: 
              Eq a => (b -> b -> b) -> [(a, b)] -> [(a, b)] -> [(a, b)]

addListToAssocList_C c ps binds = foldl addOne ps binds
                          where
                          addOne ps (k, v) = addToAssocList_C c ps k v

addListToMap :: Ord k => Map.Map k a -> [(k, a)] -> Map.Map k a
addListToMap             mp             pairs    =
                                       Map.union (Map.fromList pairs) mp

addListToMapWith :: 
        Ord k => (a -> a -> a) -> Map.Map k a -> [(k, a)] -> Map.Map k a
               -- old  new
addListToMapWith f mp pairs =  Map.unionWith f mp (Map.fromList pairs)

-- END *****************************************************************





------------------------------------------------------------------------
class Length a where genLength :: a -> Natural
                                      -- for  List, Polynomial, and such

instance Length [a] where  genLength = genericLength

class IsSingleton a where  isSingleton :: a -> Bool

instance IsSingleton [a] where  isSingleton [_] = True
                                isSingleton _   = False

instance IsSingleton (Set.Set a)   where isSingleton =
                                                isSingleton . Set.toList
instance IsSingleton (Map.Map a b) where isSingleton =
                                                  isSingleton . Map.keys


------------------------------------------------------------------------
propVOverList :: 
          Eq a => [(a, PropValue)] -> a -> PropValue -> [(a, PropValue)]
                                                -- update property value
propVOverList ps _  Unknown = ps
propVOverList ps nm v       = pov ps
  where
  pov []            = [(nm, v)]
  pov ((nm1,v1):ps) = if  nm1 /= nm  then  (nm1, v1): (pov ps)
                      else                 (nm , v ): ps

updateProps :: 
        Eq a => [(a, PropValue)] -> [(a, PropValue)] -> [(a, PropValue)]

updateProps ps ps' = foldl update ps ps'
                           where
                           update ps (nm, v) = propVOverList ps nm v

mbPropV :: Maybe PropValue -> PropValue
mbPropV    (Just v)        =  v
mbPropV    _               =  Unknown

lookupProp :: Eq a => a -> [(a, PropValue)] -> PropValue
lookupProp            a =  mbPropV . lookup a

addUnknowns :: Eq a => [(a, PropValue)] -> [a] -> [(a, PropValue)]
addUnknowns props = foldl addOne props
  where
  addOne  []                nm = [(nm, Unknown)]
  addOne  ps@((nm',v): ps') nm = if  nm == nm'  then  ps
                                 else          (nm', v): (addOne ps' nm)

antiComp :: CompValue -> CompValue
antiComp    LT        =  GT
antiComp    GT        =  LT
antiComp    _         =  EQ

minBy, maxBy :: Comparison a -> [a] -> a

  -- Minimum, maximum by the given comparison
  -- Example:   minBy compare        [2,1,3,1] = 1
  --            minBy (flip compare) [2,1,3,1] = 3

minBy _  [] = error "minBy <comparison> []\n"
minBy cp xs = m xs
                where  m [x]        = x
                       m (x: y: xs) = case  cp x y  of  GT -> m (y: xs)
                                                        _  -> m (x: xs)
maxBy cp = minBy (flip cp)

minimum, maximum :: Ord a => [a] -> a
minimum = minBy compare
maximum = minBy (flip compare)

minAhead, maxAhead :: Comparison a -> [a] -> [a]
  --
  -- put ahead the minimum (maximum)  by maybe transposing a single 
  -- pair of list elements
  --
minAhead cp xs = m: (ys ++ zs)  where 
                                (ys, m: zs) = span ((== LT) . cp m') xs  
                                m'          = minBy cp xs

maxAhead cp = minAhead (flip cp)



------------------------------------------------------------------------
pageWidth :: Natural
pageWidth =  72

type Verbosity = Integer     
                   -- verbosity level in messages:
                   -- v < 1 is the least verbose,  1 is more verbose ...

-- class DShow and  type ShowOption  aim to improve Show of Haskell-2010

data ParensOrNot = Parens | ParensNot  deriving (Eq, Show, Read)

data ShowOptions = ShowOptions {verbosity      :: Verbosity,
                                listSeparator  :: String, 
                                fieldSeparator :: String,
                                parInShow      :: ParensOrNot}  
                                                           deriving (Eq)
-- 
-- Options for printing to a string -- related to the DShow class.
-- fieldSeparator  is for data fields except List.
-- parInShow  effects only the case of a data being a Tuple or a List;
--            is defines whether to unparenth the members of this data 
--            print at the top level.
--   Examples: 1) a polynomial list is printed as  "[x^2+1, x-1]",
--                under  parInShow = ParensNot,  and it is printed as 
--               "[(x^2+1), (x-1)]"  under Parens.
--             2) A pair list is printed as  "[(2,1),(1,2)]",
--                under Parens,  and it is printed as  "[2,1,1,2]"
--                under ParensNot.                   

defaultVerbosity :: Verbosity
defaultVerbosity =  1

defaultListSeparator :: String
defaultListSeparator =  ", "

defaultFieldSeparator :: String
defaultFieldSeparator =  ", "

defaultShowOptions :: ShowOptions 
defaultShowOptions =  ShowOptions 
                      {verbosity      = defaultVerbosity, 
                       listSeparator  = defaultListSeparator, 
                       fieldSeparator = defaultFieldSeparator,
                       parInShow      = Parens}

class DShow a                      -- aims to improve Show of Haskell-2010
  where  
  dShows    :: ShowOptions -> a -> String -> String
  dShow     :: ShowOptions -> a -> String 
  showsList :: ShowOptions -> [a] -> String -> String
  aShows    :: a -> String -> String
  aShow     :: a -> String

  -- showList is of Haskell-2010 Prelude,  showsList is of DShow.
  -- aShows  aims at fast parsing by the Axiom program (in Spad).

  dShow opts a = dShows opts a ""
  aShow a      = aShows a ""

  showsList opts xs =  id  

    -- it formats with NewLine according to  pageWidth

    showChar '[' . sl pageWidth xs . showChar ']'
    where
    opts'         = addToShowOptions (-1) $ opts {parInShow = Parens}
    sep           = listSeparator opts 
    sepHasNewLine = elem '\n' sep
    unparensIf    = case parInShow opts of Parens -> id
                                           _      -> unparensUpper "()"

    sl _ []  = id                               
    sl l [x] = let str = unparensIf $ dShow opts' x  
                                                  -- l  is the remaining
               in                                 -- current line width
               if  genLength str <= l  then  showString str
               else                          showString ('\n': str)

    sl l (x: xs) = 

      let xStr = unparensIf $ dShow opts' x
      in
      if  sepHasNewLine  then  
                      showString xStr . showString sep . sl pageWidth xs
      else
      let {str = xStr ++ sep;  lStr = genLength str}
      in
      if  lStr <= l  then  showString str . sl (l - lStr) xs
      else             showString ('\n': str) . sl (pageWidth - lStr) xs


changeSeparator :: Integer -> String -> String
                   -- j       str
-- For j >= 0, it appends j new line characters to  str.
-- For j < 0,  it cuts off (min n j) last new line characters from  str,
--             where  n  is the number of the trailing new line 
--             characters in  str.

changeSeparator j =  if  j >= 0  then  (++ (genericReplicate j '\n'))
                     else              reverse . cutNLs (- j) . reverse  
  where
  cutNLs 0 cs      = cs
  cutNLs _ []      = []
  cutNLs j (c: cs) = if  c /= '\n'  then  c: cs
                     else                 cutNLs (pred j) cs 

addToShowOptions :: Integer -> ShowOptions -> ShowOptions 
addToShowOptions    n          opts = 
                                    -- note: negative n `decreases' opts

                         opts {verbosity      = verb', 
                               listSeparator  = lSep', 
                               fieldSeparator = fSep' }
                         where
                         verb' = (verbosity opts) + n
                         lSep' = changeSeparator n $ listSeparator  opts 
                         fSep' = changeSeparator n $ fieldSeparator opts

shOpt :: Natural -> ShowOptions
shOpt n =  addToShowOptions n defaultShowOptions

------------------------------------------------------------------------
showsn :: DShow a => Natural -> a -> String -> String 
showsn n =  dShows (shOpt n)

shown :: DShow a => Natural -> a -> String
shown n =  dShow $ shOpt n


showsWithPreNLIf ::
   DShow a => ShowOptions -> Natural -> Natural -> a -> String -> String
              --  opts       n          m          a 

-- Print `a' to string starting from position No  n,  
-- but if this printing exheeds  pageWidth,  then first put NewLine  and 
-- the left margin of  m  positions.
-- Example:
-- If  pageWidth = 45,  show x = "(f (a + b))",
--                      show y = "(g (a + b), 0, (a + b))",
--                      str    = "beginning of 30 positions  x = ",
-- then
-- str ++ (showsWithPrNLIf 30 15 x "")
-- =
-- "beginning of 30 positions  x = (f (a + b))"
-- ,
-- str ++ (showsWithPreNLIf 30 15 y "")
-- =
-- "beginning of 30 positions  x =
--                  (g (a + b), 0, (a + b))"

showsWithPreNLIf opts n m a =

  let aStr    = dShow opts a
      aLn     = genLength aStr
      lMargin = genericReplicate m ' '
  in
  if  n + aLn <= pageWidth  then  showString aStr
  else              showChar '\n' . showString lMargin . showString aStr


showWithPreNLIf :: 
             DShow a => ShowOptions -> Natural -> Natural -> a -> String
showWithPreNLIf         opts           n          m          a =  
                                          showsWithPreNLIf opts n m a ""

------------------------------------------------------------------------
instance DShow ShowOptions 
  where 
  dShows opts opts' = 

    let sep = fieldSeparator opts
    in
    (if  verbosity opts < 2  then  id  else  showChar '\n') . 
    showString 
              "\n(ShowOptions {verbosity = " . shows (verbosity opts') .
    showString sep .
    showString "listSeparator = " . shows (listSeparator opts') .
    showString sep .
    showString "fieldSeparator = " . shows (fieldSeparator opts') . 
    showString sep . shows (parInShow opts') . 
    showString "})"

instance Show ShowOptions where  showsPrec _ = showsn 0 

instance DShow Bool where  dShows _ = shows 
                           aShows True  = showString "true" 
                           aShows False = showString "false" 
    
instance DShow Int where  
                   dShows _ = shows 
                   aShows n = showString "(I1 " .   -- SingleInteger
                              shows n . showChar ')'
instance DShow Integer where  
                       dShows _ = shows 
                       aShows n = showString "(I " . shows n . 
                                  showChar ')'

instance DShow Char where  dShows    _ = showChar 
                           showsList _ = showList
                                         -- of Haskell-2010 Prelude

instance DShow a => DShow (Maybe a) 
  where
  dShows _    Nothing  =  showString "Nothing"
  dShows opts (Just a) =  showString ("(Just " ++ sep) .
                          dShows opts a . showChar ')' 
                          where
                          sep = delete ',' $ fieldSeparator opts

instance DShow a => DShow [a] 
  where  
  dShows    = showsList
  aShows xs = showChar '[' . 
              (compose $ intersperse (showChar ',') $ map aShows xs) .
              showChar ']'
              where
              shList []      = id
              shList (x: xs) = aShows x . shList xs

instance (DShow a, DShow b) => DShow (a, b) 

-- (,) and ( , , )  need more care for new line

  where
  dShows opts (x, y) =  showChar '(' . shows1 x . showString sep . 
                        shows1 y . showChar ')'
        where
        opts'    = addToShowOptions (- 1) $ opts {parInShow = Parens}
        sep      = fieldSeparator opts
        shows1 x = (case parInShow opts of Parens -> id
                                           _      -> unparensUpper "()")
                   . dShows opts' x

  aShows (a, b) =  showString "(pair " . aShows a . showChar ' ' . 
                   aShows b . showChar ')'


instance (DShow a, DShow b, DShow c) => DShow (a, b, c) 
  where
  dShows opts (x, y, z) = showChar '(' . shows1 x . showSep . shows1 y . 
                          showSep . shows1 z . showChar ')'
        where
        opts'    = addToShowOptions (-1) $ opts {parInShow = Parens}
        showSep  = showString $ fieldSeparator opts
        shows1 x = (case parInShow opts of Parens -> id
                                           _      -> unparensUpper "()")
                   . dShows opts' x

instance (DShow a, DShow b, DShow c, DShow d) => DShow (a, b, c, d) 
  where
  dShows opts (x, y, z, u) = 
                showChar '(' . shows1 x . showSep . shows1 y . showSep . 
                shows1 z . showSep . shows1 u . showChar ')'
        where
        opts'    = addToShowOptions (-1) $ opts {parInShow = Parens}
        showSep  = showString $ fieldSeparator opts
        shows1 x = (case parInShow opts of Parens -> id
                                           _      -> unparensUpper "()")
                   . dShows opts' x

instance (DShow a, DShow b, DShow c, DShow d, DShow e) => 
                                              DShow (a, b, c, d, e) 
  where
  dShows opts (x, y, z, u, v) = 
                showChar '(' . shows1 x . showSep . shows1 y . showSep . 
                               shows1 z . showSep . shows1 u . showSep .
                               shows1 v . showChar ')'
        where
        opts'    = addToShowOptions (-1) $ opts {parInShow = Parens}
        showSep  = showString $ fieldSeparator opts
        shows1 x = (case parInShow opts of Parens -> id
                                           _      -> unparensUpper "()")
                   . dShows opts' x


instance (DShow a, DShow b) => DShow (Map.Map a b)
  where
  dShows opts mp =  showChar '{' . 
                    showsUnparensUpper opts "[]" (Map.toList mp) . 
                    showChar '}'

instance DShow a => DShow (Set.Set a)
  where
  dShows opts set = showChar '{' . 
                    showsUnparensUpper opts "[]" (Set.toList set) . 
                    showChar '}'
  
------------------------------------------------------------------------
showsByInit ::
            DShow a => ShowOptions -> Natural -> [a] -> String -> String
showsByInit            opts           n          xs =
  (case xs
   of
   []  -> showString "[]"
   [_] -> dShows opts xs
   _   -> showChar '(' . sho n xs . showChar ')'
  )
  where
  opts' = addToShowOptions (-1) opts
  sho _ []      = id
  sho n (x: ys) =
            if  n > 0  then
                      dShows opts' x . showString ", " . sho (pred n) ys
            else      dShows opts' x . showString ", ..."

------------------------------------------------------------------------
unparensUpper :: String -> String -> String
                 -- pars   xs
-- <spacesOrNLs><lpar>Foo<rpar><spacesOrNLs'> ->
-- <spacesOrNLs>Foo<spacesOrNLs'>,         otherwise, remain as it is.
-- Each character in <spacesOrNLs> and <spacesOrNLs'>  is ' ' or '\n'.
-- pars = [lpar, rpar]  is the two-character string representig a
--                      parenthesis pair,
--                      pars  must belong to  ["()","[]","{}","<>"].
-- Example:  if   dShow opts f =  "\n ( ( x))"  then
--           unparensUpper "()" $ dShow f =  "\n   x"

unparensUpper pars xs =  
  case pars 
  of
  [lpar, rpar] -> unpar lpar rpar xs
  _            -> 
      error $ concat ["\nunparensUpper ", pars, "\n ", xs,
        "\n:\nthe first argument must be two parenthesis characters.\n"]
  where
  unpar lpar rpar xs = 
             case  span (\ x -> x == '\n' || x == ' ') xs
             of
             (_,   []   ) -> xs
             (xs', c: ys) ->
                if  c /= lpar  then xs
                else
                case  span (\ x -> x == '\n' || x == ' ') $ reverse ys
                of
                (_,    []     ) -> xs
                (rYs', c': rZs) -> 
                           if  c' /= rpar  then xs
                           else  concat [xs', reverse rZs, reverse rYs']
  

showUnparensUpper :: DShow a => ShowOptions -> String -> a -> String
showUnparensUpper               opts           pars =
                                         unparensUpper pars . dShow opts

showsUnparensUpper ::
               DShow a => ShowOptions -> String -> a -> String -> String
showsUnparensUpper        opts           pars      a =
                              showString (showUnparensUpper opts pars a)

showWithNLUnparensUpper ::
             DShow a => ShowOptions -> Natural -> Natural -> a -> String
showWithNLUnparensUpper opts           n          m =
                           unparensUpper "()" . showWithPreNLIf opts n m

showsWithNLUnparensUpper ::
   DShow a => ShowOptions -> Natural -> Natural -> a -> String -> String
showsWithNLUnparensUpper opts   n          m          a =
                         showString (showWithNLUnparensUpper opts n m a)






{- reserve ************************************************************
Maybe, to join Cast, maybe, flip a b ... 
class Convertible a b  
  where  
  cvm :: a -> b -> Maybe b
  cv  :: a -> b -> b
  cv a b = fromMaybe (error "(cv a b) fail\n") (cvm a b)
-- cvm a b  tries to convert  a  to domain of  b.
--
-- b  is a *sample* for its domain.
-- DIFFERENCE from  Cast: 
--   cvm may return Nothing, it is more complex, may be expensive,
--   it is usually applied at the upper, "interface" level of the 
--   program, out of the nested cycles. 
-- Example:
-- for  f <- Z[x,y],  g <- Rational[x,y,z][u] = R,   cvm f g
-- has a chance to "extend and lift" f to R by adding denominators 1
-- and zero powers for z, u.

-- instance Convertible a a   where  cv a _ = a
instance Convertible Bool    Bool     where  cvm a _ = Just a
                                             cv  a _ = a
instance Convertible Char    Char     where  cvm a _ = Just a
                                             cv  a _ = a
instance Convertible Integer Integer  where  cvm a _ = Just a
                                             cv  a _ = a
*********************************************************************
-}
