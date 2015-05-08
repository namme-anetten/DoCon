------------------------------------------------------------------------
------------------------------------------------------------------------
--  The Algebraic Domain Constructor  DoCon,   version 2.12
--
--  Copyright  Serge Mechveliani,  2012
------------------------------------------------------------------------
------------------------------------------------------------------------





module Sympol_  -- Operations with Symmetric Polynomials. 
                -- All needed from here is reexported by  AlgSymmF.
(SymPol(..), SymMon, 
 symPolMons, symPolPrttComp, symLm, symLdPrtt, cToSymPol, 
 reordSymPol, monToSymMon, symPolHomogForms
 -- instances for SymPol:
 --  Length(..), Show, DShow, Eq, Dom, Project, PolLike, 
 --  Set .. AddGroup, Num
)
where
import Data.List hiding (maximum, sort, sortBy)
import Prelude   hiding (maximum)

import DPrelude (Length(..), DShow(..), Cast(..), -- classes
                 Z, ct, ctr, allMaybes, compBy, sort, sortBy, maximum, 
                                 addToShowOptions, showsn, showsWithDom)
import Categs   (Dom(..), Domains1, OSet(..))
import SetGroup (Set(..), AddSemigroup(..), AddMonoid(), AddGroup(..), 
                 MulSemigroup(..),  compareTrivially, zeroS, isZero,
                                                      neg, sub, times)
import RingModule (Ring(..), CommutativeRing())
import VecMatr    (Vector(..))
import Pol        (PolLike(..), Mon)
import Partition  (Partition, PrttComp, prttWeight, showsPrtt)
import qualified Pol1_ (set_, asmg_, agr_)





------------------------------------------------------------------------
type {- Ring a => -}  SymMon a = (a, Partition)

                         -- like  Mon a, Pol a,
                         -- only with partition instead of power product
                     
data SymPol a = SymPol [SymMon a] a PrttComp (Domains1 a)

instance Dom SymPol where  sample (SymPol _ a _ _) = a
                           dom    (SymPol _ _ _ d) = d
                                               
symPolMons     :: SymPol a -> [SymMon a]
symPolPrttComp :: SymPol a -> PrttComp

symPolMons     (SymPol m _ _  _) = m
symPolPrttComp (SymPol _ _ cp _) = cp
                                        
symLm :: CommutativeRing a => SymPol a -> SymMon a
                                                 -- leading sym-monomial
symLm f = case symPolMons f  
          of 
          m: _ -> m
          _    -> error ("\nsymLm 0  \nin" ++ (showsDomOf 1 f "\n"))

symLdPrtt :: CommutativeRing a => SymPol a -> Partition
symLdPrtt =  snd . symLm

instance Length (SymPol a) where  genLength = genLength . symPolMons

instance Eq a => Eq (SymPol a) where
                               f == g =  (symPolMons f == symPolMons g)

------------------------------------------------------------------------
instance AddGroup a => Cast (SymPol a) (SymMon a) 
                                       -- sym-monomial to sym-polynomial
  where
  cast mode (SymPol _ c cp dm) (a, p) =  SymPol mons c cp dm
            where
            mons = if  mode == 'r' && isZero a  then []  else [(a, p)]

                                                
instance AddGroup a => Cast (SymPol a) [SymMon a]   -- from sym-mon list
  where
  cast mode (SymPol _ c cp dm) mons =  SymPol ms c cp dm
    where                                           -- order NOT checked
    ms = if mode /= 'r' then  mons  else  filter ((/= z) . fst) mons
    z  = zeroS c

instance Ring a => Cast (SymPol a) a
  where
  cast mode (SymPol _ _ cp dm) a = case mode  
                                   of
                                   'r' -> cToSymPol cp dm a
                                   _   -> SymPol [(a, [])] a cp dm
 
------------------------------------------------------------------------
instance PolLike SymPol
  where
  pIsConst f = case symPolMons f of (_, p): _ -> null p
                                    _         -> True
  pCoefs = map fst . symPolMons

  pTail f = case symPolMons f  
            of
            _: ms -> ct f ms
            _     -> error ("\npTail 0  in\n" ++ (showsDomOf 1 f ".\n"))

  pFreeCoef (SymPol mons a _ _) =
                         let (b, p) = last mons
                         in
                         if null mons then  zeroS a
                         else              if null p then b else zeroS a

  ldeg f = case symPolMons f 
           of  
           (_, p): _ -> prttWeight p
           _         -> 
                      error ("\nldeg 0  for\n"++ (showsDomOf 1 f ".\n"))

  deg f = case map (prttWeight . snd) $ symPolMons f 
          of 
          d: ds -> maximum (d: ds)
          _     -> error ("\ndeg 0  for\n" ++ (showsDomOf 1 f ".\n")) 

  pCDiv f c = let (cs, ps) = unzip $ symPolMons f
              in
              case allMaybes [divide_m a c | a <- cs]
              of
              Just quots -> Just $ ct f $ zip quots ps
              _          -> Nothing

  pMapCoef mode f g = cast mode g [(f a, p) | (a,p) <- symPolMons g]

  lpp   _ = error "\nlpp (SymPol ..):   not defined, so far.\n" 
  lm    _ = error "\nlm (SymPol ..):   not defined, so far.\n" 
  pCoef _ = error "\npCoef (SymPol ..):   not defined, so far.\n" 
  pVars _ = error ("\npVars (SymPol ..): \n" ++
                   "(SymPol ..) has implicit anonymous variables.\n")
  pPPO   _   = error "\npPPO (SymPol ..):   not defined, so far.\n" 
  pMapPP _ _ = error "\npMapPP _ (SymPol ..):   not defined, so far.\n" 
  degInVar _ _ _ = 
             error "\ndegInVar _ _ (SymPol ..):  not defined, so far.\n" 
  varPs _ _ = error "\nvarPs _ (SymPol ..):  not defined, so far.\n" 
  pValue _ _ = error "\npValue (SymPol ..) _:  not defined, so far.\n" 
  pDeriv _ _ = error "\npDeriv _ (SymPol ..) _:  not defined, so far.\n"
  pDivRem _ _ = 
             error "\npDivRem (SymPol ..) _:   it is senseless there.\n"
  pFromVec _ _ = error "\npFromVec (SymPol ..) _:  not defined.\n"
  pToVec _ _   = error "\npToVec _ (SymPol ..):  not defined.\n"

           
cToSymMon :: a -> SymMon a     -- with correctness condition  c /= 0
cToSymMon a = (a, [])

cToSymPol :: AddGroup a => PrttComp -> Domains1 a -> a -> SymPol a
cToSymPol                  cp          dm            a = 
                          if
                            isZero a  then  SymPol []            a cp dm
                          else              SymPol [cToSymMon a] a cp dm

-- specialize cToSymPol :: PrttComp-> Domains1 Z-> Z-> SymPol Z #-


add_ :: CommutativeRing a => SymPol a -> SymPol a -> SymPol a

add_ (SymPol mons c cp _) g =  ct g $ ad mons $ symPolMons g
  where
  z = zeroS c
  ad []       msG      = msG
  ad msF      []       = msF
  ad (m: msf) (n: msg) =
    let 
       {(a, p) = m;  (b, q) = n;  c = a+b}
    in  
    case cp p q  
    of
    GT -> m: (ad msf (n: msg))  
    LT -> n: (ad (m: msf) msg)
    _  -> if c == z then  ad msf msg  else  (c, p): (ad msf msg)

{-# specialize add_ :: SymPol Z -> SymPol Z -> SymPol Z #-}

------------------------------------------------------------------------
instance DShow a => Show  (SymPol a) where showsPrec _ = showsn 0
instance DShow a => DShow (SymPol a)
  where
  dShows opt f = showString "(SymPol " . 
                 (foldr (\mon f -> showsMon mon . f) (showString " )  ")
                        $ symPolMons f)
                 where
                 opt' = addToShowOptions (-1) opt
                 showsMon (c, la) = dShows opt' c . showChar '*' . 
                                    showsPrtt la . showChar ' '

------------------------------------------------------------------------
instance CommutativeRing a => Set (SymPol a)
  where
  compare_m         = compareTrivially
  showsDomOf verb f = showString "{SymPol " . 
                      showsDomOf verb (sample f) . showChar '}'

  fromExpr f e =        -- SymPol is parsed as the list of sym-monomials
                        -- Example:  " [ (2,[(4,3),(2,1)]), (-1,[]) ] "
      case fromExpr (symPolMons f) e  
      of
      ([ms], "") -> ([ctr f ms], "")
      (_,    _ ) ->
             ([], concat ["\nfromExpr spSample expr,", 
                  showsWithDom 1 f "spSample" "" "expr =\n", 
                  showsn 1 e "\n\nfromExpr  failed for SymMon list.\n"])
 
  baseSet  f@(SymPol _ c cp aDom)  dom = 
                          Pol1_.set_ (showsDomOf 1 f "") dom aDom f bel'
    where
    (z, bel) = (zeroS c, membership $ snd $ baseSet c aDom)
    bel' md (SymPol mons' _ cp' _) =                       -- membership
      let 
        (cfs, ps) = unzip mons' 
      in  
      all (/= z) cfs  &&  orderedBy cp ps  &&  orderedBy cp' ps  &&  
      bl cfs
         where
         bl = if md =='r' then  all (bel 'r')  else  const True
         orderedBy _    []         = True
         orderedBy _    [_]        = True
         orderedBy comp (p: q: ps) =
                              (comp p q) == GT && orderedBy comp (q: ps)

------------------------------------------------------------------------
instance CommutativeRing a => AddSemigroup (SymPol a)
  where
  add         = add_
  zero_m  f   = Just $ ctr f $ zeroS $ sample f
  neg_m   f   = Just $ ct  f [(neg a, p) | (a, p) <- symPolMons f]
  times_m f n = Just $ ctr f [(times a n, p) | (a, p) <- symPolMons f]

  baseAddSemigroup  f@(SymPol _ c _ aDom) dom =
                    Pol1_.asmg_
                          (showsDomOf 1 f "") dom aDom (ctr f $ zeroS c)

instance CommutativeRing a => AddMonoid (SymPol a)
instance CommutativeRing a => AddGroup  (SymPol a)
  where
  baseAddGroup  f@(SymPol _ c _ aDom) dom =
                      Pol1_.agr_ 
                          (showsDomOf 1 f "") dom aDom (ctr f $ zeroS c)

instance CommutativeRing a => Num (SymPol a)  
  where  
  negate = neg
  (+)    = add
  (-)    = sub
  _ * _  = error "\n(SymPol ..)*(SymPol ..):  \
                 \product not defined here, so far.\n"
  signum _ = error "\nsignum (SymPol ..):  is senseless.\n"
  abs    _ = error "\nabs (SymPol ..):  is senseless.\n"
  fromInteger _ = 
                error "\nfromInteger _  to (SymPol ..):   use  fromi.\n"

------------------------------------------------------------------------
reordSymPol :: PrttComp -> SymPol a -> SymPol a
reordSymPol cp (SymPol mons c _ dm) = 
                    SymPol (reverse $ sortBy (compBy snd) mons) c cp dm

------------------------------------------------------------------------
monToSymMon :: Mon a -> SymMon a 
monToSymMon (a, Vec js) = 
                       (a, gather $ reverse $ sort $ filter (/= 0) $ js)
  where
  gather []      = []
  gather (j: js) = (j, succ $ genLength js'): (gather js'')
                                            where 
                                            (js', js'') = span (== j) js

------------------------------------------------------------------------
symPolHomogForms :: AddGroup a => SymPol a -> [SymPol a]

symPolHomogForms f = map (ct f) $ forms $ symPolMons f
  where
  forms ms = gatherByW [(prttWeight la, (c, la)) | (c, la) <- ms] 

  gatherByW []            =  []
  gatherByW ((w, m): wms) =  (m: (map snd wms')): (gatherByW wms'')
                            where
                            (wms', wms'') = partition ((== w) . fst) wms
                                         -- HaskellPrelude.partition
           




{- RESERVE *********************************************************
-- Multiply diagram by the h-diagram:
--            hDiagramDiagramMul n (i,m) diagram
TO BE REVISED  acc.to Littlewood-Richardson rule ...
Here the  partition list  is OK, but the coefficients are wrong
-- The result is the integer linear combination of the diagrams 
-- represented as a list of  m-diagrams  - the ones paired with 
-- the integer multiplicities.
-- The result diagrams are ordered lexicographically in decreasing 
-- order.  Example:
-- [1]*[1,1,1] =  [2,1,1] + 4*[1,1,1,1];    more precisely:
-- [(1,1)]*[(1,3)] =  [ (1, [(2,1),(1,2)]), (4, [(1,4)]) ]
hDiagramDiagramMul ::Integer -> (Integer,Integer) -> YoungDiagram ->
                                          [(Integer,YoungDiagram)]
hDiagramDiagramMul  _  pair   []               = [ (1,[pair]) ]
hDiagramDiagramMul  n  (i,m)  pairs@((_,m1):_) =
  let n0   = m+m1-n
    kMax = min m m1                 -- bounds for i+j multiplicity
                                    -- in the result diagrams
    kMin = if  n0 < 0  then 0  else n0
    ks   = reverse [kMin..kMax]
    -- the part of the above product that have k items of i+j    
    m_dgsOf_k  0 _ _           _ =  []
    m_dgsOf_k  n m ((j,m'):ps) k =
      let ijPair =  if  k==0   then []  else [(i+j, k )]
	jPair  =  if  k==m'  then []  else [(j, m'-k)]
        m_dgsFor_ps = if m==k then [(1,ps)] -- it may occur [(1,[])]
                      else    hDiagramDiagramMul (n-m') (i,m-k) ps
        (mdgs_j,mdgs) =  span jHeaded m_dgsFor_ps
               -- ones starting with  j  will merge with the 
               -- above (j,m'-k),  m_dgsj are called merging pairs
           where  jHeaded (l,ps) =  not (null ps) && (fst (head ps))==j
        resForMergingPair (l, ((_,t):ps)) =
                           ( l*(m'-k+t),  ijPair++(j,m'-k+t):ps )
                                  --?
        resForNonMerging  (l,ps) =  ( l, ijPair++jPair++ps )
      in (map resForMergingPair mdgs_j)++(map resForNonMerging mdgs)
  in concat  (map (m_dgsOf_k n m pairs) ks) 


TO BE REVISED  ****************************************************
-- Multiply  sym-monomial  by  sym-polynomial.
-- Only the  h-monomial case  works so far:   (c*<i..i>) * f 
symMonSymPolMul :: 
 (CommutativeRing a, Num a) => SymMonomial a -> SymPol a -> SymPol a
symMonSymPolMul  (a,[]  )  f =  cSymPolMul a f
symMonSymPolMul  (a,diag)  f = 
  let (SymPol smons c cp vars) = f
    n = genLength vars;  zr = zeroS c;  un = unity c
    zeroSP = cToSymPol zr pLexComp vars
    hdSymMonMul (j,m) (b,diag) =
      let  pairs  = hDiagramDiagramMul n (j,m) diag
           smons' = [(b*(fromi un k), dg) | (k,dg) <- pairs]
      in   SymPol (filter ((/=zr).fst) smons')  c cp vars
  in  case  diag
    of [pair] -> let  pair = head diag 
                     gs = map (hdSymMonMul pair) smons
                in reordSymPol 
                    cp  (cSymPolMul a (foldl symPolAdd zeroSP gs))
      _   -> error ("symMonSymPolMul:  only h-monomial - the one of"
                  ++ " the kind  c*[(i,m)] - can handle so far \n")
--------------------------------------------------------------------
-- Multiply  sym-polynomials.
-- So far, it works only for the case when the first polynomial
-- consists of a single monomial which is an  h-monomial.
symPolMul :: (CommutativeRing a, Num a) =>
             SymPol a -> SymPol a -> SymPol a
symPolMul  f g =  case  symPolMons f  of
   [mon] -> symMonSymPolMul mon g
   _     -> error ( "(symPolMul f g):  f  must consist of a " ++
                    "single h-monomial - so far \n")
--------------------------------------------------------------------
-- The power of  sym-polynomial.
-- So far, it works only for the case when the first polynomial
-- consists of a single monomial which is an  h-monomial.
symPolPower ::  (CommutativeRing a, Num a) =>
                     SymPol a -> Integer -> SymPol a
symPolPower  f@(SymPol mons c cp vars)  n =
  let unSP = cToSymPol (unity c) cp vars
  in case  mons    
    of [mon] -> foldr symMonSymPolMul unSP (genericReplicate n mon)
       _     -> error("(symPolPower f n):  f  must consist "
                      ++ "of a single h-monomial - so far \n")
END RESERVE ********************************************************
-}
