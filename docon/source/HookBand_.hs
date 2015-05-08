------------------------------------------------------------------------
------------------------------------------------------------------------
--  The Algebraic Domain Constructor  DoCon,   version 2.12
--
--  Copyright  Serge Mechveliani,    2012
------------------------------------------------------------------------
------------------------------------------------------------------------




module HookBand_ 

  -- Operations with Partitions.  Continuation.
  -- (Skew) hooks and horizontal bands.  
  -- See first  Partit_.hs.  See Manual 'symmf.i', 'symmf.p.p'.
  -- All needed from here is reexported by  Partition.

(SHook, HBand,  sHookHeight, subtrSHook, firstSWHook, prevSWHook,
 subtrHBand, maxHWBand, prevHWBand
)
where
import Data.List (genericTake, genericDrop, genericSplitAt)

import DPrelude (Length(..), -- class 
                 Natural, Z)
import Partit_  (Partition, prttUnion)






------------------------------------------------------------------------
type SHook = (Z, Z, Z, Z)

  -- Skew hook:  in  (w, hb, hr, hb')
  --
  -- w   is the weight of the hook, 
  -- hb         No of the starting block, 
  -- hr         No of the row in this block where the hook starts,
  -- hb'        No of the last block of the hook.

------------------------------------------------------------------------
sHookHeight :: Partition -> SHook -> Z       -- numberOfRowsOccupied - 1
sHookHeight    la   (_, b, r, b') =  (sum$ map snd laOfHook) - r
              where
              laOfHook =  genericTake (b'-b+1) $ genericDrop (pred b) la
                     
------------------------------------------------------------------------
subtrSHook :: Partition -> SHook -> Partition
subtrSHook    la           h@(w, b, r, _) =      -- partition la - sHook
  let
    (laI', (i,m): mu) = genericSplitAt (pred b) la
                           -- laI' is not touched by the hook.  Part the 
                           -- rows in the block (i,m) that are free too
                           -- and append them to the upper diagram
                           --
    laI = if r == 1 then  laI'  else  laI' ++ [(i, pred r)]
    nu  = (i, m - r + 1): mu                -- first several rows of  nu
                                           -- are touched by the hook
  in  
  laI ++ (subtr nu w)
    where                      
    msg = showString "\nsubtrSHook la hook,\nla = " . shows la .
          showString ",  hook = " . shows h . showChar '\n'

                               -- subtract the skew hook of weight
    subtr []       _ = []      -- w  starting from the first row
    subtr la       0 = la
    subtr [(1, m)] w =  
      if  
         m == w then []
      else           error $ msg ("\nreduced to  subtr [(1, m)] w   "
                                  ++ " with  m /= w :  wrong hook.\n"
                                 )
    subtr [(i, 1)] w =  if i == w then []  else [(i - w, 1)]
    subtr [(i, m)] w = 
      let  
         w' = m + i - 1 -w 
      in
      case (w < m || w' < 0,  w == m,  w') 
      of
      (True, _  , _  ) ->
              error $ msg ("reduced to  subtr [(i, m)] w   with  "++
                           "i > 1,  (w < m  or  w' < 0):  wrong hook.\n"
                          )
      (_,    True, _ ) -> [(pred i, m)]
      (_,    _,    0 ) -> [(pred i, pred m)]
      (_,    _,    _ ) -> [(pred i, pred m), (w', 1)]

    subtr ((i,m): la) w =
                let {((j, _): _) = la;  perim1 = m + i - j}
                in
                if w < perim1 then  prttUnion (subtr [(i, m)] w) la
                else             prttUnion (subtr [(i, m)] perim1      ) 
                                           (subtr la       (w - perim1))

------------------------------------------------------------------------
firstSWHook ::  Natural -> Partition -> Maybe SHook
             -- w          la
  -- First skew hook  la-mu  of weight  w  in the diagram  la   
  -- - the one with the highest possible head - if there exists any.

firstSWHook = fh
  where
  fh 0 _         = Nothing
  fh _ []        = Nothing
  fh w [(1, m)]  = if w > m then Nothing else  Just (w, 1, m-w+1, 1)
  fh w [(i, 1)]  = if w > i then Nothing else Just (w, 1, 1, 1)
  fh w [(i, m)]  = let perimeter = i+m-1
                   in
                   case (w > perimeter, w <= m) of
                                   (True, _   ) -> Nothing
                                   (_,    True) -> Just (w, 1, m-w+1, 1)
                                   _            -> Just (w, 1, 1,     1)
  fh w la@((i, m): mu) = 
    let 
       laRest = if m == 1 then  mu  else  (i, pred m): mu
    in
    case upperRightmostHook w la  
    of
    Just b -> Just (w, 1, 1, b) 
    _      -> case  fh w laRest
              of
              Nothing                    -> Nothing 
              hoo@(Just (_, hb, hi, hb')) -> 
                          case (m, hb)  
                          of
                          (1, _) -> Just (w, succ hb, hi,      succ hb')
                          (_, 1) -> Just (w, hb,      succ hi, hb'     )
                          _      -> hoo

  -- s-w-hook  starting with the upper-rightmost cell of  la 
  -- - if exists:                             w la --> Nothing | Just b,
  -- b = the No of the last block of the hook.

  upperRightmostHook = u  :: Natural -> Partition -> Maybe Z

  u 0 _             = Nothing
  u _ []            = Nothing
  u w [(i, m)]      = if  w < m || (w > m+i-1)  then  Nothing
                     else                            Just 1
  u w ((i, m): mu) = let {(j, _)= head mu;  perimeter = m+(i-j)-1}
                     in
                     case (w < m, w <= perimeter)  
                     of 
                     (True, _   ) -> Nothing
                     (_,    True) -> Just 1
                     _            -> fmap succ $ u (w-perimeter-1) mu

------------------------------------------------------------------------
prevSWHook :: Partition -> SHook -> Maybe SHook

  -- Previous  sw-hook  to the given  sw-hook
  -- - the ordering is so that the greater is the hook which head starts 
  -- higher.
  -- prevSWHook la h   is obtained by taking the part  laT  of partition  
  -- la  after the head row of the hook and applying firstSWHook to laT 
  -- ...
prevSWHook [] _            = Nothing
prevSWHook la (w, b, r, _) = 
  let 
    (i,m): mu = genericDrop (b-1) la
    laT       = if r == m then  mu  else (i, m-r): mu
  in
  case firstSWHook w laT
  of 
  Nothing               -> Nothing
  Just (_, b', r', b'') -> 
                         case (r == m, b') 
                         of 
                         (True, _) -> Just (w, b' + b,   r'  , b'' +b  )
                         (_,    1) -> Just (w, b,        r'+r, b'' +b-1)
                         _         -> Just (w, b' + b-1, r'  , b'' +b-1)

------------------------------------------------------------------------
type HBand = [Z]  

subtrHBand :: Partition -> HBand -> Partition  -- partition \ h-band 
subtrHBand    la           bn    =  sb la bn    
  where                                       
  sb []         []      = []
  sb []         _       = error msg
  sb _          []      = error msg
  sb (pair: la) (w: ws) =
    if  
      w == 0 then  pair: (sb la ws)
    else
    let {(i, m) = pair;  dif = sb la ws}
    in
    case (m, i-w, dif)
    of
    (1, 0 , _          ) -> dif
    (1, i', []         ) -> [(i', 1)]
    (1, i', (j,n): dif') -> if i' == j then (j,  succ n): dif'
                            else            (i', 1     ): dif
    (_, 0 , _          ) -> (i, pred m): dif
    (_, i', []         ) -> [(i, pred m), (i', 1)]
    (_, i', (j,n): dif') ->
                         if i' == j then (i, pred m): (j,  succ n): dif'
                         else            (i, pred m): (i', 1     ): dif

  msg = concat ["\nsubtrHBand ", shows la " ", shows bn 
               " :\n\nthe partition and band  must be of same length\n"]


------------------------------------------------------------------------
maxHWBand ::  Char -> Partition -> Z -> Maybe HBand
           -- mode    la           w
  -- Maximal h-w-band in the partition  la.
  -- mode = 'l'   is so far the ONLY valid value,
  --  and it means that the "lex" ordering is used on the 
  -- positions in the diagram  la:  
  --                   (i,j) > (i',j') =  i < i' || (i==i' && j>j'),
  --              where  i  is the number of the block of rows, 
  --                     j         number of the column.
  -- Comparing bands means comparing lexicographically the 
  -- sequences of their cell positions - starting from the maximal
  -- position. 

maxHWBand mode la w =  
  if
    mode /= 'l' then  
     error $ concat ["\nmaxHWBand ", [mode, ' '], shows la " ", shows w
                    " :\nmode = \'l\'  is the only possible, so far.\n"]
  else  mb la w
    where
    mb la           0 =  Just $ map (const 0) la
    mb []           _ =  Nothing
    mb [(i, _)]     w =  if i < w then Nothing else Just [w]
    mb ((i, _): la) w =  let {(j, _) = head la;  d = i-j;  w' = min d w}
                         in  fmap (w' :) $ mb la (w-w')

------------------------------------------------------------------------
prevHWBand :: Char -> Partition -> HBand -> Maybe HBand 
                                -- Previous (to the given) h-w-band.
                                -- Ordering, mode  are as in  maxHWBand.
prevHWBand mode la band  

  | mode /= 'l'                    =
           error $ msg "\nmode =  \'l\'  is the only possible so far.\n"

  | genLength la /= genLength band =
            error $ msg "\npartition and band must be of same length.\n"

  | otherwise                      = pb la band
    where
    msg = showString "\nprevHWBand " . showChar mode . shows la . 
                          showChar ' ' . shows band . showString "\n:\n"
    pb _       []       = Nothing
    pb _       [_]      = Nothing
    pb (_: la) (0: bnd) = case pb la bnd  of Nothing   -> Nothing
                                             Just bnd' -> Just (0: bnd')
    pb (_: la) (wt: bnd) = 
      case pb la bnd  
      of
      Just bnd' -> Just (wt: bnd')
      Nothing   -> 
        let (i', _): laT = la
            w'           = head bnd
            di           = case laT of (j, _): _ -> i'-j
                                       _         -> i'
        in
        case (w' >= di, laT)  
        of
        (True, _   ) -> Nothing
        (_,    []  ) -> Just [pred wt, succ w']
        _            ->
                   case  maxHWBand 'l' la (succ $ sum bnd)
                   of
                   Just mbnd -> Just ((pred wt): mbnd)
                   _         -> 
                     error $ msg 
                     "\nreduced to  maxHWBand,  and  maxBand  failed.\n"
