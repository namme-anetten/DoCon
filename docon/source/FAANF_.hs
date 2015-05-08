------------------------------------------------------------------------
------------------------------------------------------------------------
--  The Algebraic Domain Constructor  DoCon,   version 2.12
--
--  Copyright  Serge Mechveliani,    2012
------------------------------------------------------------------------
------------------------------------------------------------------------




module FAANF_ (faaNF, faaNF_test)   

-- Reduction to Groebner Normal Form of non-commutative polynomial over
--                                                   a Commutative Ring.
where
import Data.Maybe (isJust)  

import DPrelude (tuple33, mapmap, ct, showsWithDom, sum1)
import Categs   (Dom(..))
import SetGroup (Set(..))
import FAA0_
import SetGroup   (MulSemigroup(..), zeroS, isZero, unity)
import RingModule (EuclideanRing(..))
import UPol_      (PolLike(..), lc)

import qualified PolNF_ (makeModes, coefNF)





------------------------------------------------------------------------
faaNF :: 
 EuclideanRing a => 
 String -> [FAA a] -> FAA a ->
 -- mode   gs         f        

 ( (FAA a, [FAA a]), (FAA a, [FAA a]),
                                     (FAA a, [[(FAAMon a, FAAMon a)]]) )
 -- lrem   lqs        rrem   rqs      biRem  biQs

  -- Non-commutative analogue for  polNF.
  -- mode   is as in polNF.
  --
  -- (lrem,lqs)   is the reduction result for  LeftIdeal(gs): 
  --                                                 f - q1*g1 -...,
  -- (rrem,rqs)   -- for RightIdeal(gs):             f - g1*q1 -...,
  --
  -- biRem        -- remainder for DoubleSidedIdeal(gs): 
  --                                      biRem = f - m1*g1*m1' -...
  --   For  gs = [g_1..g_k] 
  --   each qq_i <- biQs is  [(m_i_1,m_i_1')..(m_i_l(i),m_i_l(i)')],
  --   and it represents a linear combination 
  --           comb_i = m_i_1*g_i*m_i_1' +..+ m_i_l(i)*g_i*m_i_l(i)'
  --   to substract from f.
  --
  -- To understand the below program, read first the commutative 
  -- case: polNF.

faaNF mode gs f =  (nf 'l' mode gs f, nf 'r' mode gs f, biNF mode gs f)
  where
  choose :: Char -> (a, a) -> a
  choose 'l'  =  fst
  choose _    =  snd
  ----------------------------------------------------------------------
  nf :: EuclideanRing a => 
                  Char -> String -> [FAA a] -> FAA a -> (FAA a, [FAA a])
               -- sideMode rcMode   gs         f         rem    qs     
  nf smode rcmode gs f = 
    let
      (zr, zeroPol)     = (zeroS $ sample f, zeroS f)
      gqs               = [(g, zeroPol) | g <- gs]
      (tailMode, cMode) = PolNF_.makeModes rcmode
      ------------------------------------------------------------------
      -- append  pp-lpp(g) to (g, q):  pp -> (g, q) -> ((g, q), qt)  

      appendPPQuot pp gq@(g,_) = 
                         case (isZero g, divide_m2 pp (faaLPP g)) 
                         of
                         (True, _          ) -> (gq, (Nothing, Nothing))
                         (_,    (qtl,qtr,_)) -> (gq, (qtl,     qtr    ))
      ------------------------------------------------------------------
      nfh []  f = ([], f)       -- reduce f while possible, by head only
      nfh gqs f =
        if
          isZero f then (gqs, f)
        else  if a' == zr then  nfh gqs' newTail  
              else              (gqs',  ct f (monF': (faaMons newTail)))
        where
        (a, ppF) = faaLM f
        gqqs    = map (appendPPQuot ppF) gqs
        gqqDs   = filter (isJust . choose smode . snd) gqqs  
                                                 -- lpp-divisors for ppF
        bs       = map (lc . fst . fst) gqqDs
        (a', ds) = PolNF_.coefNF cMode bs a
        monF'    = (a', ppF)
        q's      = zipWith dTo_q ds gqqDs  -- accumulate quotient for gi
                   where                     
                   dTo_q d ((_, q), qts) = 
                                   case (d == zr, choose smode qts) 
                                   of
                                   (True, _      ) -> q
                                   (_,    Just p') -> q + (ct f (d, p'))

        newTail = foldl (-) (pTail f) $ zipWith tailProduct ds gqqDs
                where         
                tailProduct d ((g, _), qts) = 
                  case
                      (d == zr, choose smode qts) 
                  of
                  (True, _      ) -> zeroPol
                  (_,    Just p') -> 
                           choose smode $ faaMonFAAMul (d, p') $ pTail g

        gqs' = merge q's gqqs
      ------------------------------------------------------------------
      merge :: Set q=> [q] -> [((p, q), (Maybe a, Maybe a))] -> [(p, q)]

      merge []       pairs                = map fst pairs
      merge (q': qs) (((g, q), x): pairs) = 
                              case (choose smode x) 
                              of  
                              Nothing -> (g, q) : (merge (q': qs) pairs)
                              _       -> (g, q'): (merge qs       pairs)

      merge (q': _)  _  = 
                  error ("\nfaaNF(_e) ... (merge (q: _) [])   - ?\n" ++
                                      (showsWithDom 1 q' "q" "" ".\n"))
      -----------------------------------------------------------------
      processWithTail gqs f = 
                     let (gqs' , r' ) = nfh gqs f  
                         (gqs'', r'') = processWithTail gqs' $ pTail r'
                     in
                     if  isZero r' || not tailMode  then  (gqs', r')
                     else     (gqs'', ct f ((faaLM r'): (faaMons r'')))
      -----------------------------------------------------------------
      (gqs', r) = processWithTail gqs f 
    in
    (r, map snd gqs')


------------------------------------------------------------------------
biNF :: EuclideanRing a =>                                      -- local
        String -> [FAA a] -> FAA a -> (FAA a, [[(FAAMon a, FAAMon a)]])
                                       -- rem qqs   
biNF rcmode gs f = 
  let
    (zr, un, zeroPol) = (zeroS $ sample f, unity $ sample f, zeroS f)
    gqs               = [(g, []) | g <- gs]
    (tailMode, cMode) = PolNF_.makeModes rcmode
    --------------------------------------------------------------------
    -- append  pp-lpp(g) to (g, q):  pp -> (g, q) -> ((g, q), qt)  

    appendPPQuot pp gq@(g, _) = 
               if  isZero g then (gq, Nothing                          )
               else              (gq, tuple33 $ divide_m2 pp (faaLPP g))
    --------------------------------------------------------------------
    -- nfh :: ..=> gqs a -> FAA a -> (gqs a, FAA a)
     
    nfh []  f = ([], f)         -- reduce f while possible, by head only
    nfh gqs f =
      if
        isZero f then (gqs, f)
      else    if a' == zr then  nfh gqs' newTail  
              else              (gqs',  ct f (monF': (faaMons newTail)))

      where
      (a, ppF) = faaLM f
      gqqs     = map (appendPPQuot ppF) gqs
      gqqDs    = filter (isJust . snd) gqqs      -- lpp-divisors for ppF
      bs       = map (lc . fst . fst) gqqDs
      (a', ds) = PolNF_.coefNF cMode bs a
      monF'    = (a', ppF)
      q's      = zipWith dTo_q ds gqqDs           -- accumulate quotient 
                 where                            -- for each divisor gi
                 dTo_q d ((_, mpairs), qts) = 
                    case 
                        (d == zr, qts) 
                    of
                    (True, _          ) -> mpairs
                    (_,    Just (l, r)) -> ((d, l), (un, r)): mpairs

      newTail = foldl (-) (pTail f) $ zipWith tailProduct ds gqqDs
         where         
         tailProduct d ((g, _), qts) = 
               case (d == zr, qts) 
               of
               (True, _         ) -> zeroPol
               (_,    Just (l,r)) -> snd $ faaMonFAAMul (un,r) $ 
                                     fst $ faaMonFAAMul (d, l) $ pTail g
                                     -- mon(d,l)*(pTail g)*mon(1,r)
      gqs' = merge q's gqqs
    --------------------------------------------------------------------
    merge :: Set q => [q] -> [((g, q), Maybe a)] -> [(g, q)] 
                                                     -- update quotients
    merge []       pairs                = map fst pairs
    merge (q': qs) (((g, q), x): pairs) = 
                              case x 
                              of  
                              Nothing -> (g, q) : (merge (q': qs) pairs)
                              _       -> (g, q'): (merge qs       pairs)

    merge (q':_)  _ = error ("\nfaaNF(_e) ... (merge (q:_) [])  - ?\n"
                                    ++ (showsWithDom 1 q' "q" "" ".\n"))
    --------------------------------------------------------------------
    processWithTail gqs f = 
      let 
        (gqs',  r' ) = nfh gqs f  
        (gqs'', r'') = processWithTail gqs' $ pTail r'
      in
      if  isZero r' || not tailMode  then  (gqs', r')
      else                     (gqs'', ct f ((faaLM r'): (faaMons r'')))
    --------------------------------------------------------------------
    (gqs', r) = processWithTail gqs f 
  in
  (r, map snd gqs')



------------------------------------------------------------------------
faaNF_test :: EuclideanRing a => String -> [FAA a] -> FAA a ->
                                 -- mode   gs         f        

                       (((FAA a, [FAA a]),              -- (lrem, lqs)      
                         (FAA a, [FAA a]),              -- (rrem, rqs)
                         (FAA a, [[(FAA a, FAA a)]])    -- (biRem, biQs)
                        ),
                        (Bool, Bool, Bool)     -- (testL, testR, testBi)
                       )
-- testL  =  lrem == f - q1*g1 -..- qk*gk
--                                     &&  (faaLPP lrem) <=cp (faaLPP f)
-- testR     is similar
-- testBi =  biRem == f - m11*g1*m11' -..- m1l(1)*g1*m1l(1)' 
--                      - m21*g2*m21' -..
--                      ... 
--           &&  (faaLPP biRrem) <=cp (faaLPP f)
  
faaNF_test mode gs f = (((lrem, lqs), (rrem, rqs), (biRem, biQs')),
                                                 (testL, testR, testBi))
  where
  ((lrem, lqs), (rrem, rqs), (biRem, biQs)) = faaNF mode gs f

  biQs' = mapmap tofaa biQs where tofaa (m,m') = (ct f m, ct f m')
  cp    = faaFreeMOComp f    
  testL = lrem == (foldl (-) f $ zipWith (*) lqs gs)  && 
          elem (cp (faaLPP lrem) (faaLPP f)) [LT, EQ]

  testR  = rrem == (foldl (-) f $ zipWith (*) gs rqs)  &&  
           elem (cp (faaLPP rrem) (faaLPP f)) [LT, EQ]

  testBi = biRem == (foldl (-) f $ zipWith ml gs biQs')  &&  
           elem (cp (faaLPP biRem) (faaLPP f)) [LT, EQ]
  
  ml _ []  = zeroS f
  ml g qqs = sum1 [m*g*m' | (m, m') <- qqs]
