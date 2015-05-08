------------------------------------------------------------------------
------------------------------------------------------------------------
--  The Algebraic Domain Constructor  DoCon,   version 2.12
--
--  Copyright  Serge D.Mechveliani,  2008
------------------------------------------------------------------------
------------------------------------------------------------------------






------------------------------------------------------------------------
{-  Operations with  Partitions (Young diagrams).  
    Initial module.


See  Manual 'symmf.i','symmf.p'.

Following the denotations of Macdonald's book [Ma], let  

  la, mu   denote the partitions of a natural  k,
  la'                 conjugate partition,
  m(la)               symmetric monomial function,
  e(i)                i-th elementary symmetric function,
  e(la)               e(la(1))*..*e(la(m)).

In the programs we will write sometimes  pt, pt1, p, q  instead of
la, mu.
The Young diagrams are coded as the partitions.
Also we use here use the following terminology:  

A part of the partition we call also a row or a line.
Block  of the diagram  la 
                 is a rectangular diagram corresponding to some pair
                 (i,m) <--> i^m  in  la.
Skew Diagram (Shape)
                    is the difference  la-mu  of the Young diagrams,
                    for any  mu  inside  la.
Skew Hook  (s-hook, SHook)
                         is a continuous skew diagram in which the
                         neighbour rows overlap in exactly one box.
s-w-hook                 is an  s-hook  of weight  w.
A Hook  (i,j)  in a diagram is the box with the coordinates (i,j);
                            it has  length = "arm" + "leg".

Horizontal band (h-band, HBand)  is a skew diagram that contains not
                                 more than one box in each column.
h-w-band                         is  an  h-band  of weight  w.

A Tableau of shape  la  and  weight  mu  is ... as in the book [Ma].

We represent a  skew hook  as the integer quartet  (w,b,r,b'), 
  w   is the weight of hook,
  b   is the No of the block in  la  where the hook starts, 
  r   is the No of the row in this block at the end of which the 
      hook starts,  
  b'  is the No of the last block of the hook - it has to terminate 
      at the last row of this block.
      b' can be derived from w,b,r,  but still let it be.

  (though in principle, the skew hook can be determined by the 
  single point in the diagram). 

An  h-band  hb  in the diagram  la  is represented as the  integer
list  [b1..bn] 
which means that for  la = [(i1,m1)..(in,mn)]  the so-called  
b-block of  bk  boxes is marked in the lowest row of the  k-th 
block of rows of  la  (this block corresponds to (ik,mk))  
- for  k = 1..n,  sum(bk ..) = w,  
n = length(la) = length(hb),  hb  may contain zeroes.  
An  h-band  consists of the b-blocks, each b-block is several 
continuous boxes in the end of the lowest row of the block of la.
Neither two b-blocks have a common column.
-}
------------------------------------------------------------------------





module Partit_ 

  -- All needed from here is reexported by  Partition.

  (Partition, EPartition, PrttComp,
   toEPrtt, fromEPrtt, prttToPP, ppToPrtt, prttWeight, prttLength,
   conjPrtt, prttUnion, pLexComp, pLexComp', prttLessEq_natural, 
   minPrttOfWeight, prevPrttOfN_lex, prttsOfW, randomEPrtts, 
   showsPrtt
  )
where
import Data.List (genericSplitAt, genericReplicate)

import DPrelude (Length(..), -- class 
                 Z, Comparison, sort)
import VecMatr (Vector(..), vecRepr)
import Pol     (PowerProduct)




------------------------------------------------------------------------
type Partition = [(Z, Z)]

            -- (Young) Partition,  or Ferrers diagram.
            -- It is   []  or  [(j1,m1)..(jk,mk)],  j1 >..> jk > 0,
            -- 
            -- which is denoted in mathematics as  (j1^m1...jk^mk),
            -- m(i)  is the multiplicity of  j(i)  in the partition.

type EPartition = [Z]
                -- expanded partition - it is obtained from Partition by
                -- expanding each (j,m) to jj..j  - m-times.

type PrttComp = Comparison Partition
                             -- SymPol a  uses  PrttComp Z  similarly as
                             -- Pol a     uses  PPComp

toEPrtt :: Partition -> EPartition
toEPrtt = concat . (map (\ (j, m) -> genericReplicate m j))

fromEPrtt :: EPartition -> Partition
fromEPrtt []     = []
fromEPrtt (j:js) = (j, succ $ genLength js'): (fromEPrtt ks)
                                              where  
                                              (js', ks) = span (== j) js


------------------------------------------------------------------------
prttToPP :: Z -> Partition -> PowerProduct
  -- Convert the partition  la = [i1^m1..il^ml] 
  -- into power product of given length  n >= l.
  -- Example:  7 [5^2,4,2^3] --> Vec [0,3,0,1,2,0,0]

prttToPP n = Vec . topp 0 . reverse 
  where
  topp jPrev []          = genericReplicate (n-jPrev) 0
  topp jPrev ((j,m): pt) = 
                     (genericReplicate (j-jPrev-1) 0) ++ (m:(topp j pt))

ppToPrtt :: PowerProduct -> Partition
ppToPrtt =  filter ((/= 0) . snd) . reverse . zip [1 ..] . vecRepr
------------------------------------------------------------------------
prttWeight :: Partition -> Z                                     -- |pt|
prttWeight [] = 0
prttWeight pt = sum [j*m | (j, m) <- pt]

prttLength :: Partition -> Z      -- l(pt) = height of Young diagram
prttLength = sum . map snd        -- = number of "actual variables"
------------------------------------------------------------------------
conjPrtt :: Partition -> Partition           -- conjugated partition pt'
conjPrtt []           = []        
conjPrtt [(j, m)]     = [(m, j)]
conjPrtt ((j, m): pt) = 
                        let j1  = fst $ head pt
                            pt1 = [(j'+m, m') | (j', m') <- conjPrtt pt]
                        in  pt1 ++ [(m, j-j1)]

------------------------------------------------------------------------
prttUnion :: Partition -> Partition -> Partition
   -- repeated diagram lines are copied, say, [3,2,1] [3*2] -> [3*3,2,1]
prttUnion = u   
  where
  u []         q            = q
  u p          []           = p
  u ((i,m): p) ((i',m'): q) =
    let 
      {im = (i, m);  i'm' = (i', m')}  
    in
    case (i == i', i > i') of
                          (True, _   ) -> (i, m+m'): (u p      q       )
                          (_   , True) -> im       : (u p      (i'm':q)) 
                          _            -> i'm'     : (u (im:p) q       )

------------------------------------------------------------------------
-- We call             pLexComp  
-- what is called the  inverse lexicographical ordering  in [Ma]:

pLexComp :: PrttComp
pLexComp []         []           = EQ
pLexComp []         (_:_)        = LT
pLexComp (_:_)      []           = GT
pLexComp ((i,m): d) ((j,m'): d') = case (compare i j, compare m m')
                                   of
                                   (EQ, EQ) -> pLexComp d d'
                                   (EQ, v ) -> v
                                   (v , _ ) -> v
 
pLexComp' :: PrttComp       -- Conjugated pLexComp comparison,
                            -- in Macdonald's book [Ma] denoted  Ln'
pLexComp' p q = pLexComp (conjPrtt q) (conjPrtt p)


prttLessEq_natural :: Partition -> Partition -> Bool

  -- Natural partial ordering on partitions:
  -- la <= mu  <=>  for each i > 0  sum(la,i) <= sum(mu,i),
  -- where  sum(la,i) = la(1)+..+la(i)  
  -- - if we represent the partition without multiplicities.

prttLessEq_natural = leq 0 
  where
  -- The predicate  " for each i  sum(p,i) <=  sum(q,i) + d ".
  -- In the below loop  d >= 0.

  leq _  []            _              = True
  leq d  p             []             = (prttWeight p) <= d
  leq d  p@((j,m): _)  q@((j1,m1): _) =  
                 let
                    {mmin = min m m1;  d'= d + mmin*(j1-j)}
                 in
                 d' >= 0  &&  leq d' (dropSome mmin p) (dropSome mmin q)

  dropSome k ((j,m): p) =  if k < m then  ((j, m-k):p)  else  p

------------------------------------------------------------------------
minPrttOfWeight :: Z -> Partition
minPrttOfWeight 0 =  []
minPrttOfWeight n =  [(1, n)]

------------------------------------------------------------------------
prevPrttOfN_lex :: Partition -> Maybe Partition

  -- Partition of k = |pt|  previous to  pt in the pLexComp order.
  -- Returns  Nothing  for the minimal partition
  -- - and the minimum is here either  [(1,k)]  or  [].

prevPrttOfN_lex pt = 
  case pt 
  of     
  []                -> Nothing
  [(1, _)]          -> Nothing
  [(2, 1)]          -> Just [(1, 2)] 
  [(2, m)]          -> Just [(2, m-1), (1, 2)] 
  [(2, 1), (1, m )] -> Just [(1, m+2)]
  [(2, m), (1, m')] -> Just [(2, m-1), (1, m'+2)]
  [(j, 1)]          -> Just [(j-1, 1), (1, 1)]            -- j > 2
  [(j, m)]          -> Just [(j, m-1), (j-1, 1), (1, 1)]   
  [(j, m), (1, k )] -> 
                    let            -- move last j to 1*k break this j+k
                                   -- to the maximal partition starting
                      j1 = j - 1         -- with j-1 and prepend j*(m-1)
                      pt'= case quotRem (j+k) j1  
                           of 
                           (m', 0) -> [(j1, m')]
                           (m', r) -> [(j1, m'), (r, 1)]
                    in
                    if m == 1 then Just pt'  else Just ((j, m-1): pt')

  pair : pt ->  fmap (pair :) $ prevPrttOfN_lex pt
                                                -- j > 2, pt not minimal

------------------------------------------------------------------------
prttsOfW :: Partition -> [Partition]

  -- pt -> [pt..minPt]  all partitions of w = |pt|  
  --         starting from pt listed in pLexComp -decreasing order

prttsOfW pt =  maybe [pt] ((pt :) . prttsOfW) $ prevPrttOfN_lex pt

------------------------------------------------------------------------
randomEPrtts ::  [Z] ->  Z -> [EPartition]
                 -- rands w   pts
  -- infinite list  pts  of the  Random Expanded Partitions  of  w 
  -- produced out of the infinite list  rands  of the random 
  -- Integers  n,  such that  0 <= n <= w.
  --
  -- rands  may be obtained by, say,  Random.random (0,w) s
  -- CAUTION:  
  -- we are not sure that these partitions are "very random".

randomEPrtts randoms w = 
  case (w, w < 0) 
  of
  (0, _   ) -> map (const [] ) [1 ..]
  (1, _   ) -> map (const [1]) [1 ..]
  (_, True) -> error $ ("randomEPrtts <randoms> "++) $ shows w 
                                                 ":   negative weight\n"
  _         -> rpts randoms
    where
    rpts rs = pt:(rpts rs')  where  (rs', pt) = randPt rs w 

    randPt rs w =   -- rands -> w -> (randsRest, PartitionOf_w)
      case w
      of
      0 -> (rs, [] )
      1 -> (rs, [1])
      _ -> let (j:js, js') = genericSplitAt w rs
               jsO         = reverse $ sort$ filter (/= 0) js
               (js'', pt ) = takePt (dropWhile (> j) jsO)  w
           in  (js''++js', pt)

    takePt js      0 = (js, []                  )
    takePt []      w = ([], genericReplicate w 1)
    takePt (j: js) w = if w < j then  takePt js w  else (js', j:pt)
                                             where  
                                             (js', pt) = takePt js (w-j)  

------------------------------------------------------------------------
showsPrtt :: Partition -> String -> String
showsPrtt la =  ('[' :) . sp la . (']':)
  where
  sp []         = id
  sp [(i,1)]    = shows i
  sp [(i,m)]    = shows i . ('*' :) . shows m
  sp ((i,m):pt) = let {si = shows i;  stail = (',' :) . sp pt}
                  in
                  if m == 1 then  si . stail
                  else            si . ('*' :) . shows m . stail
