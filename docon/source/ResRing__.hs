------------------------------------------------------------------------
------------------------------------------------------------------------
--  The Algebraic Domain Constructor  DoCon,   version 2.12
--
--  Copyright  Serge Mechveliani,    2012
------------------------------------------------------------------------
------------------------------------------------------------------------






module ResRing__   -- Continuation for ResRing_.
                   -- All needed from here is  reexported by  Residue.
( 
 -- instances  Ring .. Field   for  ..=> ResidueI a
 resRingHasNilp_   
)  
where
import qualified Data.Map as Map (lookup, insert)

import Data.List (genericTake, nub)

import DPrelude (Length(..), -- class
                 PropValue(..), lookupProp, not3, ct, ctr, mapmap, 
                                                      showsWithDom)
import Categs 
import SetGroup (Set(..), AddSemigroup(..), AddGroup(..), zeroS, unity, 
                                                    inv, divide, isZero)
import RingModule 
       (Ring(..), CommutativeRing(), LinSolvRing(..), GCDRing(..), 
        FactorizationRing(..), EuclideanRing(..), Field(), 
        genFactorizationsFromIdeal, eucGCDE, isGxRing, isMaxIdeal
       )
import LinAlg   (solveLinear_euc)
import ResEuc0_ (Residue(..)    )
import ResRing_ (ResidueI(..)   )





------------------------------------------------------------------------
-- local --------
msgGxR   name = showString (name ++ "  must be a  gx-ring.\n") 
msgGxBas name =                                                 
     showString ("\ngx-basis  needed for the ideal  " ++ (name ++ "\n"))

msgMax name = 
            showString ('\n': (name ++ "  must be a  maximal ideal.\n"))

reduceCanG :: LinSolvRing a => [a] -> a -> a                      
reduceCanG                     gs  =  fst . moduloBasis "cg" gs
-----------------


------------------------------------------------------------------------
instance LinSolvRing a => Ring (ResidueI a)   
  where
  fromi_m r = fmap (ctr r) . fromi_m (resRepr r)

  baseRing  r@(Rsi x iD aD)  dmr = 
    let
      (zr,    un    ) = (zeroS x, unity x)
      (aD',   _     ) = baseAddGroup zr aD
      (_,     rR    ) = baseRing zr aD'
      (rChar, rProps) = (subringChar rR, subringProps rR)
      (iI,    _     ) = iD
      (gsM, iProps, bProps, basFact) = 
                       (idealGens iI,     idealProps iI, 
                        idealGenProps iI, genFactorizationsFromIdeal iI)
      Just gs = gsM
      canr    = reduceCanG gs
      ------------------------------------------------------------------
      char' = case rChar
              of
              Just 0 -> Nothing                                -- SO FAR
              Just _ -> c (1 :: Integer) $ canr un
                          where                      -- may be expensive
                          c k sum = if sum == zr then  Just k
                                    else  c (succ k) (canr $ add sum un)
        -- any better solution? ***

      gens' = fmap (map (ct r) . nub . filter (/= zr) . map canr) $
                                                          subringGens rR
                                        -- any better solution ? ***
      ------------------------------------------------------------------
      [max, prime, primary] =
               [lookupProp p iProps | p <- [IsMaxIdeal, Prime, Primary]]

      msg = showString "\nbaseRing r dmr," . showsWithDom 1 r "r" "A/I"
      [fact, pir] = [lookupProp p rProps| p <- [Factorial, PIR]]
      props'      = completeProps  ringAxioms
                       [(IsField,        max       ), 
                        (HasZeroDiv,     not3 prime), 
                        (HasNilp,        hasnilp   ),
                        (IsPrimaryRing,  primary   ),    
                        (Factorial,      factQ     ),
                        (PIR,            pirQ      ),
                        (IsOrderedRing,  Unknown   ),   -- so far
                        (IsRealField,    Unknown   ),   --
                        (IsGradedRing,   Unknown   )
                       ]
      completeProps _ ps = ps   -- do we need them? ***
      ringAxioms         = []   --
      ------------------------------------------------------------------
      pirQ  = case (pir, max ) of (Yes, _  ) -> Yes
                                  (_  , Yes) -> Yes
                                  _          -> Unknown

      factQ = case (max, prime) of (Yes, _  ) -> Yes
                                   (_  , No ) -> No
                                   _          -> Unknown

      hasnilp = resRingHasNilp_ prime primary fact basFact  -- SEE below
      rg = Subring {subringChar    = char',
                    subringGens    = gens', 
                    subringProps   = props',
                    subringConstrs = [],
                    subringOpers   = []}
      ------------------------------------------------------------------
    in
    case (Map.lookup Ring dmr, gsM, lookup IsGxBasis bProps)
    of
    (Just (D1Ring rg), _     , _       ) -> (dmr, rg)
    (_,                Just _, Just Yes) ->
                                   (Map.insert Ring (D1Ring rg) dmr, rg)
    _                                    -> 
                                  (dmr, error $ msg $ msgGxBas "I" "\n")


-- This is common for  ResRing_, PolRes_:
--
-- For  hasNilp  we actually have to test  Rad(I)==I  which often is
-- complex and, in the general case, unsolvable.
-- So far, we provide it for the easy cases:

resRingHasNilp_ :: 
          PropValue -> PropValue -> PropValue -> Maybe [Factorization a]
                                                            -> PropValue
resRingHasNilp_ primeI primaryI factorialR basFact =
  case 
      (primeI, primaryI) 
  of
  (Yes, _  ) -> No
  (No , Yes) -> Yes
  _          ->
    case (basFact, factorialR) 
    of
    (_,                   No     ) -> Unknown
    (_,                   Unknown) -> Unknown
    (Nothing,             _      ) -> Unknown
    (Just factorizations, _      ) ->
          (case (any containsMultiple factorizations,
                                                any null factorizations)
           of
           (True, _   ) -> Yes
           (_,    True) -> Unknown
           _            -> 
                        if  genLength factorizations == 1  then  No
                        else                                     Unknown
          )
          where  containsMultiple = any (\ (_, n) -> n > 1)


------------------------------------------------------------------------
instance LinSolvRing a => CommutativeRing (ResidueI a)
instance LinSolvRing a => LinSolvRing     (ResidueI a)   
  where
  baseLinSolvRing  r@(Rsi _ (iI,_) aD)  dmr = 
    (case
         (Map.lookup LinSolvRing dmr, Map.lookup LinSolvRing aD)
     of
     (Just (D1LinSolvR t), _                   ) -> (dmr, t)
     (_,                   Just (D1LinSolvR aT)) ->
                            syzr (isGxRing aT == Yes) $ idealGenProps iI
    )
    where
    syzr False _  = (dmr, error $ msg $ msgGxR "A" "\n")
    syzr _     ps = 
      if  lookup IsGxBasis ps /= Just Yes  then
                        (dmr,          error $ msg $ msgGxBas "I" ".\n")
      else              (Map.insert LinSolvRing (D1LinSolvR rg) dmr, rg) 

    msg = showString "\nbaseLinSolvRing r dmr," . 
                                          showsWithDom 1 r "r" "A/I"
    rg  = LinSolvRingTerm 
          {linSolvRingProps = 
               [(ModuloBasisDetaching, Yes), (ModuloBasisCanonic, Yes),
                (WithSyzygyGens,       Yes), (IsGxRing,           Yes)]}

  -- Concerning  moduloBasis, gxBasis, syzygyGens:
  -- in the below operations for           Rsi x (iI,_) d, 
  --                                       (_,rR) = baseRing x d,  
  -- (IsGxRing,Yes)  is *presumed* for rR,
  -- basis, IsGxBasis  for iI  are checked explicitly.
  --
  -- See  Manual-'gx'-Residue.ring.
  -- For a/I,  moduloBasis  does not depend on the mode: it does
  -- always the canonic reduction and needs intermediate implicit
  -- gxBasis  application.

  gxBasis  []         = ([], [])
  gxBasis  xs@(x:xs') =        -- if  iI  is maximal, gxBasis  is
                               -- done in a/i  as in the field
    let Rsi x' iD aD   = x 
        (iI, _)        = iD
        toRes x        = Rsi x iD aD
        (zeroRes,zr)   = (zeroS x, zeroS x')
        (bPs, Just gs) = (idealGenProps iI, idealGens iI)
        isGxB          = (lookup IsGxBasis bPs) == (Just Yes)
        canRem         = fst . moduloBasis "cg" gs
    in   
    case (all (== zeroRes) xs, isGxB, isMaxIdeal iI)
    of
    (True, _,     _  ) -> ([], [])       
    (_,    False, _  ) -> 
                    error $ concat ["\ngxBasis rs,", 
                    showsWithDom 1 x "head r" "A/I" $ msgGxBas "I" "\n"]
    (_,    _,     Yes) ->                          
                       ([unity x], [(inv x): (map (const zeroRes) xs')])
    _                  ->
         let x'sgs        = (map resRepr xs) ++ gs
             (g's, rowsT) = gxBasis x'sgs
             rsT          = mapmap canRem rowsT
             a's          = map canRem g's
             (a''s, rs)   = unzip $ filter ((/= zr) . fst) $ zip a's rsT
         in  (map toRes a''s, mapmap toRes rs)

  moduloBasis _    [] r                = (r, [])
  moduloBasis mode xs r@(Rsi y' iD aD) =
    let
      (iI, _)        = iD
      (bPs, Just gs) = (idealGenProps iI, idealGens iI)
      canRem         = fst . moduloBasis "cg" gs
      toRes x        = Rsi x iD aD
    in
    if  (lookup IsGxBasis bPs) /= (Just Yes)  then 
        error $ concat ["\nmoduloBasis ", mode, " rs r,",
                        showsWithDom 1 r "r" "A/I" $ msgGxBas "I" "\n"]
    else  
    let l         = genLength xs
        x's       = map resRepr xs
        (a', q's) = moduloBasis "c" (x's ++ gs) y'
        (a: qs)   = map canRem (a': (genericTake l q's))
    in   
    (toRes a, map toRes qs)   -- do we need to process the case
                              -- IsMaxIdeal(i)  separately ?

  syzygyGens mode []       = 
        error
          ("(syzygyGens " ++mode ++ " [])   in the residue ring A/I.\n")

  syzygyGens mode xs@(x:_) =  
    let 
      (Rsi x' iD _)  = x  
      (iI, _)        = iD
      (zr, zeroRes)  = (zeroS x', zeroS x)
      l              = genLength xs
      maxI           = isMaxIdeal iI
      (bPs, Just gs) = (idealGenProps iI, idealGens iI)
      canRem         = fst .moduloBasis "cg" gs
    in
    case (maxI, (lookup IsGxBasis bPs) == (Just Yes))  
    of
    (_,   False) -> 
          error $ concat ["\nsyzygyGens ", mode, " rs,",
                  showsWithDom 1 x "head rs" "A/I" $ msgGxBas "I" ".\n"]

    (Yes, _    ) -> snd $ solveLinear_euc [xs] [zeroRes]
    _            -> mapmap (ct x) relsP'       
         where
         rels   = syzygyGens "" ((map resRepr xs) ++ gs)
         relsP  = mapmap canRem rels
         relsP' = filter (not . all (== zr)) (map (genericTake l) relsP)


------------------------------------------------------------------------
instance LinSolvRing a => GCDRing (ResidueI a)   
  where
  baseGCDRing  r@(Rsi _ (iI, _) _)  dmr = 
    (case
         (Map.lookup GCDRing dmr, isMaxIdeal iI, idealGenProps iI)
     of
     (Just (D1GCDR rg), _,   _ ) -> (dmr, rg)
     (_,                Yes, ps) -> gcr $ lookup IsGxBasis ps
     _                           -> (dmr, error $ msg $ msgMax "I" "\n")
    )
    where
    msg = showString "\nbaseGCDRing r rdom," . 
                                             showsWithDom 1 r "r" "A/I"
    gcr (Just Yes) = (Map.insert GCDRing (D1GCDR rg) dmr, rg) 
    gcr _          = (dmr, error $ msg $ msgGxBas "I" "\n")
    rg = GCDRingTerm
                  {gcdRingProps = [(WithCanAssoc, Yes), (WithGCD, Yes)]}

  canInv x = if  isZero x  then  unity x  else  x

  {- It presumes: 
     IsGxRing(R) = IsGxBasis(basis(I)) = isField(R/I)  
     The safer script is  case  isField (baseRing x _)  
                          of
                          Yes -> if  isZero x  then  unity x  else  x
                          _   -> error ("canInv (Rsi..):  "++msgMax)
     Here  isField (baseRing..)  includes the check of
     IsGxRing, IsGxBasis(basis(I)).  Similar is  canAssoc.
  -}

  canAssoc x = if  isZero x  then  x  else  unity x

  gcD []      = error "\ngcD []  :: ResidueI a.\n"
  gcD (x: xs) = foldl eucG x $ filter (/= z) xs
                         where
                         {z = zeroS x;  eucG x y = fst $ eucGCDE [x, y]}

  hasSquare _ = error "\nhasSquare (Rsi ..) :  \
                      \it is senseless for ..=> ResidueI a.\n"
  toSquareFree _ = error "\ntoSquareFree (Rsi ..) : \
                         \it is senseless for ..=> ResidueI a.\n"


------------------------------------------------------------------------
instance LinSolvRing a => FactorizationRing (ResidueI a)   
  where
  -- Presumed:  *** (IsMaxIdeal,Yes) ***  for iI

  factor x = [(x, 1)]
  isPrime  = const False 
  primes _ = []  

  baseFactrRing  r@(Rsi _ (iI, _) _)  dmr = 
    (case
         (Map.lookup FactorizationRing dmr, isMaxIdeal iI, 
                                                       idealGenProps iI)
     of
     (Just (D1FactrR rg), _,   _ ) -> (dmr, rg)
     (_,                  Yes, ps) -> fr $ lookup IsGxBasis ps
     _                             -> 
                                    (dmr, error $ msg $ msgMax "I" "\n")
    )
    where
    msg = showString "\nbaseFactr r rdom," . showsWithDom 1 r "r" "A/I" 

    fr (Just Yes) = (Map.insert FactorizationRing (D1FactrR rg) dmr, rg)
    fr _          = (dmr, error $ msg $ msgGxBas "I" "\n")

    rg = FactrRingTerm {factrRingProps = [(WithIsPrime,   Yes),
                                          (WithFactor,    Yes),
                                          (WithPrimeList, Yes)]}


------------------------------------------------------------------------
instance LinSolvRing a => EuclideanRing (ResidueI a)   
  where
  -- Presumed:  *** (IsMaxIdeal,Yes) ***  for iI

  eucNorm x = if  isZero x  then  error ("\neucNorm 0,  in  " ++ 
                                         (showsDomOf 1 x ".\n"))
              else                0      

  divRem mode x y = 
    case  
        zeroS y  
    of
    zr -> case (x == zr, y == zr)  
          of 
          (_,    True) -> error $ concat ["\ndivRem ", mode: " r 0,",
                                          showsWithDom 1 x "r" "" ".\n"]
          (True, _   ) -> (zr,         zr)
          _            -> (divide x y, zr)

  baseEucRing  r@(Rsi _ (iI,_) _)  dmr = 
    (case
         (Map.lookup EuclideanRing dmr, isMaxIdeal iI, idealGenProps iI)
     of
     (Just (D1EucR rg), _,   _ ) -> (dmr, rg)
     (_,                Yes, ps) -> er $ lookup IsGxBasis ps
     _                           -> (dmr, error $ msg $ msgMax "I" "\n")
    )
    where
    msg = showString "\nbaseEucRing r rdom," . 
                                              showsWithDom 1 r "r" "A/I" 
    er (Just Yes) = (Map.insert EuclideanRing (D1EucR rg) dmr, rg)
    er _          = (dmr, error $ msg $ msgGxBas "I" "\n")
    rg = EucRingTerm 
         {eucRingProps =
                 [(Euclidean, Yes), (DivRemCan, Yes), (DivRemMin, Yes)]}


------------------------------------------------------------------------
instance LinSolvRing a => Field (ResidueI a)   
                                    -- this is only for  R/I,  I maximal
