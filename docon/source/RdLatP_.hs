------------------------------------------------------------------------
------------------------------------------------------------------------
--  The Algebraic Domain Constructor  DoCon,   version 2.12
--
--  Copyright  Serge Mechveliani,    2008
------------------------------------------------------------------------
------------------------------------------------------------------------




module RdLatP_ 
              (reduceLattice_UPolField, reduceLattice_UPolField_special)
where
import Data.List (genericDrop)

import Prelude hiding (maximum)

import DPrelude (Length(..), -- class
                 Z,  compBy, sum1, maximum, maxBy, mergeBy, sortBy)
import SetGroup   (zeroS)
import RingModule (Field())
import Permut     (applyTranspSeq)
import UPol_      (PolLike(..), UPol(..), lc, deg0, mUPolMul)
import Pol1_      ()





{-- Preface --------------------------------------------------------
    Basis Reduction for Lattice over  A = F[x],  F a field.
   
It is implemented after  [Le], section 1.
Denotations
-----------
Let  bs = [b(1)..b(n)]  be a lattice basis for  L  in  A^m,
b(i,j) =def= b(i)(j)  is the  j-th  component (coordinate) of  b(i).
bs  is considered as the matrix  b(i,j)  with the rows  b(i) <- L.
coef f i  is the coefficient of  x^i  in  f <- A.
Definition
----------
|v| = max [|v(i)| :...] = max [deg_x v(i) :...]  
                            is called the Order of vector  v  in  L.
A lattice basis  bs = [b(1)..b(n)]  is called a  reduced basis  
iff some coordinate permutation on  bs  yields  b's  satisfying
  (1) |b'(i)|   <= |b'(j)|    for  i < j
  (2) |b'(i,i)| >= |b'(i,j)|  for  i < j
  (2) |b'(i,i)| >  |b'(i,j)|  for  i > j
In particular,  for a reduced basis,  b(1)  is  the  smallest  order
vector in  L  and |b(i)|  are the so-called successive minima of  L.
Representation
--------------
A vector in  L  is a list of pairs  (j,f),   0 /= f <- A,
j <- [1..m]  the coordinate number, the list is ordered increasingly
by  j.
A permutation  pmt  on coordinates is presented by a list of integer
pairs,  each pair (i,j)  denotes the transposition of the components 
No i and j.   Applying these transpositions in the same order gives 
the permutation  inverse(pmt).
--------------------------------------------------------------------
-}


type SpPVec a = [(Z, UPol a)]     -- sparsely represented vector of
                                  -- univariate polynomials over `a'
type SpPVecO a = (SpPVec a, Z)    -- SpPVec accompanied by its order


reduceLattice_UPolField :: 
                 Field fF => Z -> [SpPVec fF] -> ([SpPVec fF], [(Z, Z)])
                          -- bnd  bs              bs'          pmt
  {-
   The Lattice Basis Reduction.
   bs   is the lattice generators for  L  over  A = F[x].
   b's  - for the mode  bnd = -1,  -  is the reduced basis for  L.
   In particular,  b's  contains the successive order minima for  L.
   pmt  means that permuting the coordinates with  pmt  
        (foldl (flip applyTranspSeq) b' pmt   - see Preface)
        gives the ordered reduced basis - the one with the 
        dominating main diagonal  b(i,i)  - see Preface.
   CAUTION:
   the result meaning for  bnd < 0  and  bnd >= 0  is different.
   bnd <  0  is described above.
   bnd >= 0  means searching of non-zero v <- Lattice(bs)  such that
             |v| <= bnd.  In this case  
                                bs' = [v]  - with the required  v,
                                  or  []   - if there is no such  v.
   bnd >= 0  is likely to cost less than computing the reduced basis
   under  bnd < 0.

   Small difference from [Le] in algorithm:  the generator list gets
   sorted by ||, and then the order is maintained.

   Example of usage
   ----------------
   For  bs = [[(1,1), (2,x^3+1), (3,x^2+x)], 
              [       (2,x^4)             ], 
              [                  (3,x^4)  ]
             ]                               - over  (Z/(5))[x],
   reduceLattice_UPolField (-1) bs =
   (b's,pmt),
   b's = [[(1,4*x^2+x),         (2,4*x^2+x),    (3,x^2)      ],
          [(1,4*x^3+x^2+1),     (2,x^2+1),      (3,x^3+x^2+x)],
          [(1,4*x^3+x^2+4*x+1), (2,x^2+4*x+1),  (3,x)        ]
         ]
   pmt = [(1,2),(2,3)].
   The ordered reduced basis is
                    [foldl (flip applyTranspSeq) v pmt | v <- b's] =

         [[(1,4*x^2+x),         (2,x^2),        (3,4*x^2+x)],
          [(1,x^2+1),           (2,x^3+x^2+x),  (3,4*x^3+x^2+1)],
          [(1,x^2+4*x+1),       (2,x),          (3,4*x^3+x^2+4*x+1)]
         ] 
   Finding of a small non-zero vector in  Lattice(bs):
     reduceLattice_UPolField 1 bs = ( [],  [(1,2),(2,3)] )
     reduceLattice_UPolField 3 bs =
                               ( [[(1,1),(2,x^3+1),(3,x^2+x)]], [] )
  -}


reduceLattice_UPolField bnd bs = 
  reduceLattice_UPolField_special 
       bnd [] (sortBy (compBy snd) [(b, ord b) | b <- bs, not $ null b])
                      where
                      ord [] = -1
                      ord v  = maximum $ map (deg0 'l' (-1) . snd) v 


reduceLattice_UPolField_special :: 
           Field fF 
           =>
           Z ->  [SpPVecO fF] -> [SpPVecO fF] -> ([SpPVec fF], [(Z, Z)])
        -- bnd   b's             bs   

  -- It is separated because the polynomial factorization calls directly 
  -- for this function, providing respectively large  b's  part.
  -- b's, bs  are free of zeroes, sorted encreasingly by  ||, 
  -- also  b' < b  for each  b' <- b's, b <- bs,
  -- and in the start,  b's  is a reduced ordered basis,  

reduceLattice_UPolField_special bnd b's bs =
                               (map (apply pmt' . fst) rs, reverse pmt')
  where
  (rs, pmt)   = rd (genLength b's) b's bs []
  pmt'        = reducePmt pmt
  apply pmt v = foldl (flip applyTranspSeq) v pmt

  reducePmt ps = delDoubles [(i, j) | (i, j) <- ps, i /= j]
         where
         delDoubles xs = let  ys = rmd xs
                         in  
                         if  xs == ys  then  xs  else  delDoubles ys
         rmd (x:y:xs) = if x == y then  rmd xs  else  x:(rmd (y:xs))
         rmd xs       = xs

  -- Put    a(i,j) = coef b(i,j) |b(i)|  or  coef b'(i,j) |b'(i)|.
  -- Note:  a(i,j) = 0 <==> deg b(i,j) < |b(i)|.
  -- b's = [b'(1)..b'(k)]  is the current reduced part.  
  -- In particular, for i <= k  a(i,i) /= 0,  a(i,j) = 0  for j < i.

  rd _ []      []           pmt = ([], pmt)
  rd _ (p:b's) []           pmt = case  (bnd < 0, snd p <= bnd)
                                  of
                                  (True, _   ) -> (p:b's, pmt)
                                  (_   , True) -> ([p],   pmt)
                                  _            -> ([],    pmt)
  rd k b's     ((b, ob): bsT) pmt =
    if
      bnd >= 0  &&  ob <= bnd  then (take 1 (b's ++ [(b, ob)]), pmt)
    else 
    let k'       = k+1
        b''      = reduce (map fst b's) b ob k
        (l,maxC) = maxBy (compBy (deg . snd)) b''  
        ob''     = deg maxC               -- for  b' /= []  l >= k
    in
    case (b'', ob'' < ob)
    of
    ([], _   ) -> rd k b's bsT pmt 
    (_ , True) ->
            let (lts, gts) = span ((<= ob'') . snd) b's
            in   
            rd (genLength lts) lts ((b'', ob''): (gts ++ bsT)) pmt

    _          ->             -- transpose pair of coordinates to
                              -- move maximum of b'' to position k+1
          rd k' (e's ++ [e]) es ((k', l): pmt)
            where
            [e's, e:es] = if l == k' then  bb
                          else       map (map (transp'' (k', l))) bb
            bb          = [b's, (b'', ob): bsT]

            transp'' ij (v, o) = (applyTranspSeq ij v, o)


reduce :: Field fF => [SpPVec fF] -> SpPVec fF -> Z -> Z -> SpPVec fF
                      -- vs          u            |u|  k
   -- Find  r(i) <- F  and reduce  u  to
   --                    u' = u - r(1)*x^e1*v(1) -..- r(k)*x^ek*v(k)
   -- so that  coef u'(i) |u| = 0  for  i <= k.  k = length vs

reduce _  [] _  _ = []
reduce vs u  ob k = rd vs [] u 0
  where                       -- uR is reduced part of u: |uR| < ob,
  rd _  uR []        _  = uR  -- each (i,f) <- u  of  i <= k  
  rd vs uR ((i,f):u) i' =     -- reduces by corresponding  v(i,i),
                              -- v(i,j) <--> a(i,j) of [Le]
    if i > k then  uR ++ ((i, f):u)
    else
    case  (genericDrop (i-i'-1) vs, deg f < ob)
    of
    (_: vs', True) -> rd vs' (uR ++ [(i, f)]) u i
    (v: vs', _   ) ->
         let (vl, vr)   = span ((/= i) . fst) v   
             g          = snd $ head vr   -- lc g <--> a(i,i) /= 0
             (a, og)    = (lc g, deg g)
             r          = -(lc f)/a
             [vl', vr'] = map mksm [vl, vr]
             mksm ps   = [(j, mUPolMul (r, ob-og) h) | (j, h) <- ps]
         in  
         rd (v: vs') (addVect uR vl') (addVect ((i, f): u) vr') (pred i)

  addVect u v = sumSimilar $ mergeBy (compBy fst) u v  
    where                                          
    sumSimilar []           = []
    sumSimilar ((i, f): ps) = 
                        let (ps', ps'') = span ((== i) . fst) ps
                            s           = sum1 (f:(map snd ps'))
                        in
                        if  s == zeroA  then sumSimilar ps''
                        else                 (i, s): (sumSimilar ps'')
  zeroA = zeroS $ snd $ head u
