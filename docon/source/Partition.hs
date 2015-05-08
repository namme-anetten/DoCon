------------------------------------------------------------------------
------------------------------------------------------------------------
--  The Algebraic Domain Constructor  DoCon,   version 2.12
--
--  Copyright  Serge Mechveliani,    2012
------------------------------------------------------------------------
------------------------------------------------------------------------



module Partition  
  -- Operations with  Partitions (Young diagrams), bands, hooks.
  -- This is the head module which also reexports all the needed items 
  -- from  Partit_, HookBand_.

  (isPrtt, subtrSHook_test, kostkaNumber, kostkaColumn, 
   kostkaTMinor, hookLengths, numOfStandardTableaux,
   permGroupCharValue, permGroupCharColumn, permGroupCharTMinor,

   -- from Partit_:
   Partition, EPartition, PrttComp,
   toEPrtt, fromEPrtt, prttToPP, ppToPrtt, prttWeight, prttLength,
   conjPrtt, prttUnion, pLexComp, pLexComp', prttLessEq_natural,
   minPrttOfWeight, prevPrttOfN_lex, prttsOfW, randomEPrtts, 
   showsPrtt,

   -- from HookBand_:
   SHook, HBand, sHookHeight, subtrSHook, firstSWHook, prevSWHook,
   subtrHBand, maxHWBand, prevHWBand
  )
where
import qualified Data.Map as Map (Map(..), empty, lookup, insert)

import Data.List (genericReplicate)

import DPrelude (Length(..), Z, factorial, mergeBy)
import Partit_  
import HookBand_ 



------------------------------------------------------------------------
isPrtt :: Partition -> Bool                       -- test "is partition"
isPrtt []                      =  True
isPrtt [(i, m)]                =  i > 0  &&  m > 0
isPrtt ((i, m): (j, k): pairs) =  
                              i > j  &&  m >0  && isPrtt ((j, k): pairs)

------------------------------------------------------------------------
subtrSHook_test :: Partition -> Bool
subtrSHook_test pt =  all testw [1 .. w]
  where
  w = prttWeight pt

  testw w' = let w'' = w - w' 
                 qs  = map (subtrSHook pt) $ hooks w'
             in 
             isMonotIncr qs  &&
             all (\ q -> isPrtt q && (prttWeight q) == w'') qs

  hooks w = maybe [] hks $ firstSWHook w pt
                     where
                     hks h = maybe [h] ((h :) . hks) $ prevSWHook pt h

  isMonotIncr []       = True
  isMonotIncr [_]      = True
  isMonotIncr (p:q:ps) = (pLexComp p q) == LT && isMonotIncr (q:ps)

------------------------------------------------------------------------
kostkaNumber :: 
  Map.Map Partition Z -> Partition -> Partition ->
                                               (Map.Map Partition Z,  Z)
  -- table               la           mu        newTable           value
{-    
Number of tableaux of the shape  la  and weight  mu   -- for |la|==|mu|.

`table' = tab(ro) 
is a  Map  (binary table - made functionally)  serving to store
the pairs  
                (la, v),    v = kostka_number(la,i_mu)
for some previously encountered la and the initials  i_mu  of weight
mu.
i_mu  are Not stored for they are defined uniquely by  la.

Each time the argument  la, mu   is non-trivial and not contained in
table, the value is found by the below method and Added to table.

Accumulating  this  table  accelerates  the   current   and   future
computation  of  the  Kostka  numbers  that  use   the    previously
accumulated table - even if  empty  is initiated in the argument.
But the table needs memory. The programmer can cut the growth of the
table by giving to the next  kostkaNumber   application the argument
table = empty.
See the examples for this presented by the functions
                                         kostkaColumn, kostkaTMinor.
METHOD.
1. It is known (see the book [Ma]) that 
    K( la , la    ) = 1,
    K( [n], mu    ) = 1,
    K( la , mu    ) = 0  except the case when  la >= mu  in the 
                         natural (partial) ordering,
    K( la , [1^w] ) = number of Standard tableaux 
                      = w! / ( Product(length(h)| h<-hooks(la)) )
2.
Let  mu  be Expanded and Reversed and  mu = w:muT

If  mu = [1^_]  then do the Standard tableaux case
else
    result =  sum( kostkaNumber(la-bnd,muT) |  bnd <- w_bands ),
  where
  all the h_w_bands  bnd  are formed in  la  in the lex-decreasing
  order. 
  To form these bands, compare them, take maximal or previous band,
  we use here the "lex" ordering on the diagram positions.

The tabulation idea founds on the following consideration.
For the same weight  mu  and for the different  la,   usually,  many
sequences of the deleted bands lead to the  same  remainder  diagram 
la~.   Such  la~  corresponds to the unique position   mu~++mu~~= mu 
in the weight diagram ...
Very probably, there exists scientific and direct method  to  reduce
the amount of the band sequences than the table.
-}


kostkaNumber tab la mu = 
  let
    --------------------------------------------------------------------
    -- in  `kn'  mu  is expanded and reversed;
    -- if  mu = w:muT  then  bnd  is the current  w-band;
    -- la >natural> mu

    kn tab _    []       []         = (tab, 1)
    kn _   _    _        []         =
            error $ msg ("... kn tab' currentBand (_:_) []\n" ++ wgtMsg)

    kn _   _    []       _          = 
            error $ msg ("... kn tab' currentBand [] (_:_)\n" ++ wgtMsg)

    kn tab _    [(_, 1)]  _          = (tab, 1)
    kn tab _    [(1, m)]  mu         = 
                          if mu == genericReplicate m 1 then (tab, 1)
                          else                               (tab, 0)

    kn tab bnd  la       mu@(_:muT) = 
       case  
           Map.lookup la tab  
       of   
       Just v -> (tab, v)
       _      -> 
         let laLower = subtrHBand la bnd 
             w'      = if null muT then 0 else head muT
             (tabLow, nLow) = 
                          case  maxHWBand 'l' laLower w'  
                          of
                          Nothing        -> (tab, 0)
                          Just maxLowBnd -> kn tab maxLowBnd laLower muT

             (tabPrev, nPrev) = case  prevHWBand 'l' la bnd 
                                       -- sum for all previous bands
                                of
                                Nothing    -> (tabLow, 0)
                                Just prevB -> kn tabLow prevB la mu
             v = nLow + nPrev
         in
         (Map.insert la v tabPrev, v)

    msg = ("kostkaNumber tab "++) . shows la . (' ':) . shows mu . 
          ("\n(given partitions must be of same weight)\n\n"++)

    wgtMsg = "Maybe, the initial partitions had different weights\n"
    --------------------------------------------------------------------
  in
  case (la == mu, prttLessEq_natural mu la, mu)
  of
  (True, _    , _       ) -> (tab, 1)
  (_,    False, _       ) -> (tab, 0)
  (_,    _,     [(1, _)]) -> (tab, numOfStandardTableaux la)
  _                       -> case reverse $ toEPrtt mu
                             of  
                             []   -> (tab, 0)
                             muER -> case  maxHWBand 'l' la $ head muER
                                     of
                                     Nothing  -> (tab, 0)
                                     Just bnd -> kn tab bnd la muER


------------------------------------------------------------------------
kostkaColumn :: Partition -> [Partition] -> (Map.Map Partition Z, [Z])
                -- mu        la_s            tab                  col
  -- yields 
  -- the list  col =  [ K(la, mu) |  la <- la_s ]   
  --   of the Kostka numbers,  la, mu  the partitions of the same 
  --   weight > 0,
  -- and the table of the accumulated values  K(la~,i_mu)  produced 
  -- by repeated application of  (tab',v) = kostkaNumber tab _ _
  --
  -- In particular, setting  la_s = allPartitions(w)  we obtain the
  -- whole column of  mu  of the Kostka matrix.


kostkaColumn mu la_s = 
  if  
    null mu then  error $ ("kostkaColumn [] la_s \n\n"++) $ msg "\n"
  else            (tab, reverse col)
    where
    (tab, col)           = foldl addKNum (Map.empty, []) la_s   
    addKNum (tab, vs) la = (tab', v: vs)  
                                  where 
                                  (tab', v) = kostkaNumber tab la mu
    msg = showString "length la_s = " . 
          shows (genLength la_s) . ('\n':) . msg'

    msg' = case la_s of la: _ -> showString "head la_s = " . shows la
                        _     -> id

------------------------------------------------------------------------
kostkaTMinor :: [Partition] -> [Partition] -> [[Integer]]
kostkaTMinor la_s mu_s =  [snd $ kostkaColumn la mu_s | la <- la_s]
  --
  -- Transposed minor of the matrix of the Kostka numbers.
  -- la_s, mu_s  must be the partitions of same weight w > 0, la_s, mu_s   
  -- define respectively the rows and the columns of transposed minor. 
  -- In particular, setting  la_s = mu_s = all_partitions(w) 
  -- yields the whole transposed Kostka matrix.
  -- Certain property:
  -- it is known [Ma] that K is strongly upper uni-triangular and 
  -- has 1-s in the first row.
  -- So, the result is strongly lower uni-triangular.

------------------------------------------------------------------------
hookLengths :: Partition -> [[Integer]]

  -- Matrix  {h(i,j)}, 
  -- h(i,j)  is the Length of the hook of the point (i,j) in the 
  --         Young diagram  la. 
  -- The result list of lists has the form of the Expanded partition
  -- for  la  (and the lists may differ in length), each  h(i,j) 
  -- being put in the corresponding cell of the diagram.

hookLengths = hls 
  where
  hls []          = []
  hls [(i,m)]     = singleBlockCase i m
  hls ((i,m): la) = 
    let
      (j, _)          = head la
      di              = i - j
      matrUpperRight  = singleBlockCase di m
      matrRem@(row:_) = hls la
      rows'           = genericReplicate m $ map (+ di) row
      matrUpperLeft   =  
         zipWith (\ i row -> map (+ i) row) (reverse [1 .. m]) rows'
    in    
    (zipWith (++) matrUpperLeft matrUpperRight) ++ matrRem

  singleBlockCase i m = 
          zipWith (\ h row -> map (+ h) row) (reverse [0 .. (m-1)]) rows
          where
          rows = genericReplicate m $ reverse [1 .. i]


------------------------------------------------------------------------
numOfStandardTableaux :: Partition -> Z

  -- number of standard tableaux =  
  --                    weight! / product[hookLength(h) | h<- hooks(la)]
  --
  -- The below script tries to keep the intermediate products 
  -- possibly smaller.

numOfStandardTableaux la = case la of

  []       -> error "numOfStandardTableaux []\n"
  [(_, 1)] -> 1 
  [(1, _)] -> 1
  _        -> nst $ foldl (mergeBy (flip compare)) [] $ hookLengths la
    where
                                      -- here  ls = l1 >= l2 >= ..  
                                      -- is the list of hook lengths
    nst ls = nt (prttWeight la) 1 1 ls

    nt w p q []     = quot ((factorial w)*p) q
    nt w p q (l:ls) = 
             let (ls', ls'') = span (== l) ls
                 qNew        = q*(l^(genLength ls'))
                 pNew        = if w == l then  p
                               else            p*(product [(l+1) .. w])
             in  nt (l-1) pNew qNew ls''


------------------------------------------------------------------------
permGroupCharValue :: 
   Map.Map Partition Z -> Partition -> Partition ->
                                               (Map.Map Partition Z,  Z)
   -- table               la           ro      (newTable,    chi(la,ro))


{-  Irreducible character value for the permutation group S(n).

It is known [Ma] that any such character  chi  is defined by the 
partition  la  of  n,  and  chi  can be expressed as certain 
determinant of the unit characters of the groups  S(la(i)).

`table' = tab(ro) 
is a  Map  (binary table - made functionally)  serving to store the 
pairs  
                     (mu, chi(mu,i_ro))
for some previously encountered  mu  and the initials  i_ro  of  ro.
i_ro  are not stored for they are defined uniquely by  mu.

Even if  table = empty  it still accumulates so that it 
accelerates on average the computation of current and further 
chi(la,ro) (for the same ro), see, for example, permGroupCharMatrix.

METHOD:   Murnaghan-Nakayama rule  +  storing/searching in table.

The MN-rule finds the value of the character  chi(la)  on any 
permutation conjugacy class given by the cyclic type partition  ro, 
|ro| = n  in this way:

   chy(la,ro) =  Sum[ (-1)^ht(tab) | tab <- hookTableaux(la,ro) ]

- here we call a  Hook Tableau  (h-tableau)  an analog of tableau of
shape la and weight ro  for the case of  skew hooks  instead of 
horizontal bands; 
and               ht(tab) =def=  Sum( ht(hook) |  hook <- tab )

The following cases are simple and computed specially:

(c1)  chy( [n]  , ro    ) = 1   
(c2)  chy( la   , [1^n] ) = numOfStanardTableaux(la),
(c3)  chy( [1^n], ro    ) = 
                     permutationSign(ro) = product( (-1)^(ro(i)-1) )

- though only (c2) gives a considerable gain.

Also it is written in [Ma] that  chy(la',ro) = sign(ro)*chy(la,ro)
- we use it when store and look-up in the table.
Easy arguments, like mu,ro = [],[1..],etc,  are NOT stored in tab.

The tabulation idea founds on the following consideration.
For the same weight  ro  and for the different  la,  many sequences
of the deleted hooks may lead to the same remainder diagram la~. 
Such la~ corresponds to the unique position  ro~++ro~~= ro 
in the weight diagram ...
-}


permGroupCharValue tab la ro = 
  case (la, ro) 
  of
  ([], _       ) -> error$ ("permGroupCharValue tab [] ro: \n"++) $
                           ("ro = "++) $ shows ro "\n"
  (_ , []      ) -> error$ ("permGroupCharValue tab la []: \n"++) $
                           ("la = "++) $ shows la "\n"
  (_ , [(1, _)]) -> (tab, numOfStandardTableaux la)
  _              -> cv tab la $ reverse $ toEPrtt ro
    where
    -- In this  cv  loop  la,ro  are not null,  
    -- ro  is expanded and reversed and does not equal to [1..1].
    --
    -- cv  runs through all the w-hooks by applying  prevSWHook.
    -- For each hook cv finds the part of the above Sum[..] given
    -- by all the h-tableaux starting with this hook, - by 
    -- applying  cv  recursively to  la - hook, tail(ro).
    --
    -- These hook sums are accumulated in  totalSum.

    cv tab _        []     = (tab, 1)
    cv tab [(_, 1)] _      = (tab, 1)
    cv tab [(1, _)] ro     = (tab, permutSign ro)
    cv tab la       (w:ro) = 
      let
         la'tab = Map.lookup (conjPrtt la) tab
      in 
      case (firstSWHook w la, Map.lookup la tab, la'tab)
      of  
      (Nothing, _     , _     ) -> (tab, 0)
      (_      , Just v, _     ) -> (tab, v)
      (_      , _     , Just v) -> (tab, v*(permutSign (w:ro)))
      (Just hk, _     , _     ) -> runHooks tab la (w:ro) hk 0

    permutSign pt = if  even (genLength $ filter even pt) then 1 else -1

    runHooks tab la (w:ro) hook totalSum =  
       let
         ht        = sHookHeight la hook
         (tab', v) = cv tab (subtrSHook la hook) ro
         newSum    = if  even ht  then  totalSum+v  else  totalSum-v
       in  
       case prevSWHook la hook  
       of
       Nothing    -> (Map.insert la newSum tab', newSum)
       Just nextH -> runHooks  tab' la (w:ro) nextH newSum
        

------------------------------------------------------------------------
permGroupCharColumn ::  
                  Partition -> [Partition] -> (Map.Map Partition Z, [Z])
                  -- ro        la_s           tab                   col

  -- List   col = [cha(la,ro) |  la <- la_s],
  --   of the character values obtained from  permGroupCharValue,
  --   la,ro  the partitions of the same weight > 0,
  -- and the table of the accumulated values  cha(la~,i_ro)  
  -- produced by the intermediate applications of 
  -- (tab',v) = permGroupCharValue tab _ _
  --
  -- In particular, setting   la_s = all partitions    we obtain the
  -- whole column of irreducible character matrix for S(w).


permGroupCharColumn [] []     = error "permGroupCharColumn [] []\n"
permGroupCharColumn [] (la:_) =
                       error $ ("permGroupCharColumn [] (la:_): \n"++) $
                               ("la = "++) $ shows la "\n"

permGroupCharColumn ro la_s   = (tab, reverse col)
    where
    (tab, col) = foldl addCharValue (Map.empty, []) la_s

    addCharValue (tab, vs) la = (tab', v:vs) 
                                where
                                (tab', v) = permGroupCharValue tab la ro 

------------------------------------------------------------------------
permGroupCharTMinor :: [Partition] -> [Partition] -> [[Integer]]
permGroupCharTMinor    ro_s           la_s =
                        [snd $ permGroupCharColumn ro la_s | ro <- ro_s]
  --
  -- Transposed minor  tC  of the matrix of the of
  --                       Irreducible Character Values  cha(w)(la,ro) 
  -- for the permutation group  S(w).
  -- ro_s, la_s   must be partitions of same weight  w > 0,  they define
  -- respectively the rows and columns of transposed minor. 
  -- In particular, setting  ro_s = la_s = all_partitions(w) 
  -- yields the whole transposed character matrix  tC.
  --
  -- One of TESTs:  tC * (transp tC)  must be diagonal
  --                - for the irreducible characters are orthogonal.









          
{- RESERVE  ******************************************************

  M = M(n) = M(la,mu) =  e_to_m_matrix n,   |la| = |mu| = n > 0 

  - the matrix to express any elementary symmetric product
  e(la) = e(la1)*..*e(lan)  of e(i)  as the linear combination of
  symmetric monomials  m(mu):  
                e(la) = sum( M(la,mu)*m(mu) | |mu|= n)
  - see the book [Ma].
  It is known that
    M  is symmetric,  M = transp(K)*J*K,    
         where
         K  is the Kostka matrix;
         J  is the conjugation matrix:  J(la,mu) = 1  if  la = mu'
                                                 = 0  otherwise;
    M(la,mu) /= 0  <=>  la <= mu'  in the natural ordering.
   Method:
   forming J*K means to map la->la'  to the row indices of  K  and
   to bring the new indexed row list to the lex-decreasing order.

e_to_m_matrix :: Z -> Matrix Z
e_to_m_matrix    n =  (transp kM)*jK
  where
  kM@(Mt rows) =  kostkaMatrix n
  jK           =  Mt (map snd irows)   -- J*K
  irows        =  sort greaterL (zip pts rows)
  pts          =  map conjPrtt  (prttsOfW [(n,1)])
  greaterL (la,_) (mu,_) =  (pLexComp la mu)==GT
-}










