------------------------------------------------------------------------
------------------------------------------------------------------------
--  The Algebraic Domain Constructor  DoCon,   version 2.12
--
--  Copyright  Serge Mechveliani,    2014
------------------------------------------------------------------------
------------------------------------------------------------------------



-- Testing extention of the field  Q(alpha)  with the roots of 
--                                         x^4 + 4*alpha*x^3 + 2*x^2 - 1/3.
-- It relies on the Ferrari's method.


-- The variant of  
-- * d = r*(16*al^2 - 64/9)  for a root of discriminant for  resolvent,
-- * the levels  Al -- P -- Ferr -- E.



import qualified Data.Map as Map (empty)
import Data.List (delete)

import DPrelude  
import Categs (Ideal(..), Dom(..), Property_Ideal(..),
                                            Property_IdealGen(..)) 
import SetGroup (zeroS, isZero, unity, inv)
import RingModule 
import VecMatr  (Vector(..))
import Fraction (Fraction(..), canFr)
import Pol 
import GBasis  (polNF, gBasis, gBasisWithRadicals, isGBasis, algRelsPols)
import Residue (Residue(..), ResidueE(..), ResidueI(..), gensToIdeal)




-- ***************************************************************************
-- al  stands for  alpha.

type Q     = Fraction Integer    -- rational numbers - for coefficients
type Qrp   = UPol Q              -- for  Q[r]
type Qr    = ResidueE Qrp        -- for  Q(r)
type PQr   = UPol Qr             -- for  Q[al]
type Al    = Fraction PQr        -- for  Q(al)
type Px    = UPol Al             -- for  Al[x]
type PX    = Pol Al              -- for  Al[x1,x2,x3,x4]
type P     = Pol Al              -- for  Al[r3, r4, r1, r2, u, v]
type Ferr  = ResidueI P          -- for  P/Ideal(ferrariEqs)
type PFerr = UPol Ferr           -- for  Ferr[y]
type PE    = Pol Ferr            -- for  Ferr[uu, vv, dd]
type E     = ResidueI PE         -- for  PE/I(esqE_gr)
type Ez    = UPol E              -- for  E[z]


main = putStr $ concat 
  [
{-
   "r' = ",            shows r' ",   ",
   "r'^2 = ",          shows (r'^2) "\n",
   "inv (1 + r') = ",  shows (inv (unQr + r')) "\n",
-}
   "f =  ",                shows f "\n",
   "res_f = ",             shows res_f "\n\n",
   "res_f_c = ",           shows res_f_c "\n\n",
   "res_discr = ",         shows res_discr "\n",
   "d = ",                 shows d "\n",
   "d^2==res_discr = ",    shows (d^2 == res_discr) "\n\n",
   "cardano_f_res_c = ",   showsn 1 cardano_f_res_c "\n\n",
   "y1 = ",                shows y1 "\n",
--   "res_f_at_y1 = ",       shows res_f_at_y1 "\n",
  -- "res_f_at_y1_nf = ",    shows res_f_at_y1_nf "\n"

   "ferrariEqs =\n",        showsn 1 ferrariEqs "\n\n",
   "gFerrariEqs =\n",       showsn 1 gFerrariEqs "\n\n",
   "rel = ",                shows rel "\n",
   "ferrariEqs_plus =\n",   showsn 1 ferrariEqs_plus "\n\n",

   "f_roots =\n",            showsn 1 f_roots "\n\n",
   "viete_f =  ",            shows viete_f "\n\n",
   "inv roots =\n",          showsn 1 (map inv f_roots) "\n\n", 
   "test inv roots =  ",     shows [x * (inv x) | x <- f_roots] "\n\n",
   -- "f_root_rels =\n",        showsn 1 f_root_rels "\n\n",
   -- "gViete == f_root_rels ", shows (gViete == f_root_rels) "\n"

   "******************************************************\n",
   "chosen =\n ",            shows chosen "\n\n",
   "g =\n",                  shows g "\n\n",
   "discr_g =\n",            shows discr_g "\n\n",
   "eqsE =\n",               showsn 1 eqsE "\n\n",
   "eqsE_gr =\n",            showsn 1 eqsE_gr "\n",
   "gRoots =\n",             showsn 1 gRoots "\n\n",
   "check_inv_gRoots = ",    shows check_inv_gRoots "\n",
   "viete_g = ",             shows viete_g "\n\n",
   "fE =\n",                 shows fE "\n\n",
   "gE =\n",                 shows gE "\n\n",
   "g_on_gRoots = ",         shows g_on_gRoots "\n\n",
   "goals = ",               shows goals "\n"
  ]
  where
  -- Build the rational functions field  Al = Q(al).

  unQ = 1:/1  :: Q
  dQ  = upField unQ Map.empty        -- domain of Q

  -- Build  Q(r),  r = sqrt(-3).

  unQrp = cToUPol "r" dQ unQ         -- 1 in Q[r]
  dQrp  = upEucRing unQrp Map.empty
  r     = varP unQ unQrp
  r_eq  = r^2 + (fromi r 3)
  r_eqI = eucIdeal "be" r_eq [] [] [(r_eq, 1)]
  unQr  = Rse unQrp r_eqI dQrp
  dQr   = upField unQr Map.empty     -- domain of Qr = Q(r)
  r'    = ctr unQr r                 -- r = sqrt(-3)  in  Q(r)
 
  -- Build  Al = Qr(al)  - rational functions over Qr.

  unPQr = cToUPol "al" dQr unQr  :: PQr  -- 1 of PQr = Qr[al]
  alPQr = varP unQr unPQr                -- "al" <- PQr
  unAl  = unPQr :/ unPQr  :: Al          -- 1 in Al
  dAl  = upField unAl Map.empty          -- domain of Qr(al)
  al   = alPQr :/ unPQr  :: Al           -- al in Al
  rPQr = ctr unPQr r'
  r''  = rPQr :/ unPQr   :: Al           -- r = sqrt(-3) in Al

  ----------------------------------------------------------------------------
  -- The field  Al  is built.  All the further happens over Al.

  [n0, n1, n2, n3, n4, n9, n16, n27, n64] = 
                        map (fromi al) [0, 1, 2, 3, 4, 9, 16, 27, 64]  :: [Al] 
                                                                 -- cast to Al
  oneOn3 = unAl/n3                               -- 1/3  in Al

                        -- a4  a3     a2  a1  a0  
  [a4, a3, a2, a1, a0] =  [n1, n4*al, n2, n0, - oneOn3]  :: [Al]
                                         -- f = x^4 + 4*al*x^3 + 2*x^2 - 1/3

                      -- [n1, n0, n0, n0, n1]  :: [Al]  -- x^4 + 1
                      --  [n0, n2, n0, - oneOn3]  :: [Al]  -- al = 0
                                                   -- f = x^4 + 2*x^2 - 1/3
                      -- [n4/n3, n2, n0, - oneOn3]  :: [Al]   -- al = 1/3

  unPx = cToUPol "x" dAl unAl       -- 1 of Px = Al[x]
  dPx  = upEucRing unPx Map.empty   -- domain of Px
  x    = varP unAl unPx             -- x <- Px

  [a4', a3', a2', a1', a0'] = map (ctr unPx) [a4, a3, a2, a1, a0]   :: [Px]

  f =  a4'*x^4 + a3'*x^3 + a2'*x^2 + a1'*x + a0'  :: Px   -- f = p_4  of Paper

  -- Goal I:   build the extension  Al(x1..x4)  with the roots of  f.

  -- Form the cubic resolvent  res_f  for  f.
  -- f = x^4 + 4*al*x^3 + 2*x^2    - 1/3
  --           a          b    c=0  d
  --           a3         a2        a0

  [rs2, rs1, rs0] = [- a2, aa1, aa0]  :: [Al]   -- coefficients for res_f 
                    where     
                    aa1 = - n4*a0
                    aa0 = n4*a2*a0 - a3^2*a0

  [rs2', rs1', rs0'] = map (ctr unPx) [rs2, rs1, rs0]  :: [Px] 

  res_f =  x^3 + rs2'*x^2 + rs1'*x + rs0'   :: Px


  -- Goal I.1:  find a root for  res_f  by the Cardano method.
  --
  -- Form  res_f_c =  x^3 + p*x + q  -- a canonic form obtained by 
  --                                    the shift  res_f(x - rs2/3)

  res_f_c = upolSubst res_f (x - a) []  :: Px
                                        where 
                                        a = ctr unPx ((pCoef res_f [2])/n3)
  --
  -- It occurs   x^3 + ((16/3)*al^2 - 64/27),   that is  p = 0 !

  [p,  q] = [pCoef res_f_c [e] | e <- [1, 0]]  :: [Al]

  res_discr =  - n4*p^3 - n27*q^2   :: Al       -- disciminant res_f


  -- res_discr  occurs   d^2  for a certain  d  in Al  !

  d = r''*(n16*al^2 - n64/n9)  :: Al   -- do we need to care of  -d ?


  -- Build  P = Al[ ferVars ].

  ferVars = ["r3", "r4", "r1", "r2", "u", "v"]
     --
     -- u, v  are for the Cardano formulae for  res_f,
     -- r_i   are reserved for the Ferrari formulae for  f.

  -- To obtain more clear formulae for the roots x_i, define certain special
  -- ordering on the power products in [..u,v]:

  ppComp (Vec [r3,  r4,  r1,  r2,  u,  v ])
         (Vec [r3', r4', r1', r2', u', v']) =
         case
             lexListComp compare [r3, r4, r1, r2] [r3', r4', r1', r2']
         of
         -- r_i  are of a higher precedence

         EQ  -> (case compare (u + v) (u' + v') of EQ  -> compare u u'
                                                   val -> val
                )
         val -> val

  o   = (("deg2lex", 6), ppComp, [])
  unP = cToPol o ferVars dAl unAl      :: P   -- 1 in P = A[ferVars]
  dP  = upGCDLinSolvRing unP Map.empty        -- domain of P
  alP = ctr unP al                     :: P   -- al  in P

  [rr, d'] = map (ctr unP) [r'', d]        :: [P]

  [r3, r4, r1, r2, u, v] = varPs unAl unP  :: [P]

  [m0, m1, m2, m3, m4, m8, m27] = map (fromi unP) [0, 1, 2, 3, 4, 8, 27]  
  (m3on2, m27on2)               = (m3/m2, m27/m2)             

  [p', q']     = map (ctr unP) [p, q]
  (car1, car2) = (m3on2*d'*rr, m27on2*q')                          
  -- 
  -- It occurs  car1 = -car2  and  v^3 = 0  in  the Cardano equations!

  cardano_f_res_c_pre =                     -- Cardano relations for f_res_c
                        [u^3 - car1 + car2,
                         v^3 + car1 + car2,
                         u*v + m3*p'        ]  :: [P]
  -- It simplifies to 
  --
  cardano_f_res_c =  [v,  u^3 - car1 + car2]

  res_f_c_root =  u/m3   -- = (u + v)/3  the first root

  y1 = res_f_c_root - a  :: P   where 
                                a = ctr unP ((pCoef res_f [2])/n3)
     -- the "first" root to 
     -- res_f  is by shifting at  - a/3,  a = coef(res_f, 2)   

  -- y1  occurs  (u + 2)/3


  -- Test  res_f y1  =mod_cardano_f_res_c=  0:

  [rs2'', rs1'', rs0''] = map (ctr unP) [rs2, rs1, rs0]  :: [P] 

  res_f_at_y1 =  y1^3 + rs2''*y1^2 + rs1''*y1 + rs0''  :: P

  res_f_at_y1_nf =  fst $ polNF "rc" cardano_f_res_c res_f_at_y1
                                                         -- must be zero


  -- Add the Ferrari relations on  r_i  --------------------------------------

  [a, b, c, dd] =  [pCoef f [e] | e <- [3, 2, 1, 0]]  :: [Al]

  -- Form the equations  r1^2 - (a^2 - 4*b + 4*y1),
  --                     r2^2 - (y1^2 - 4*dd),       -- "-4*b" ?
  --                     r3^3 - (p1^2 - 8*q1),
  --                     r3^3 - (p2^2 - 8*q2)    in  P
  --
  -- for   p_i, q_i <- Pk  defined below.

  [a', b', c', dd'] = map (ctr unP) [a, b, c, dd]

  r1_eq =  r1^2 - (a'^2 - m4*b' + m4*y1)  :: P
  r2_eq =  r2^2 - (y1^2 - m4*dd')         :: P

  -- p = a  +- rt(a^2 - 4*b + 4*y1)   =  a +- r1
  -- q = y1 -+ rt(y1^2 - 4*dd)        =  y1 -+ r2

  p1 = a' + r1
  p2 = a' - r1
  q1 = y1 - r2
  q2 = y1 + r2

  -- r3 = rt(p1^2 - 8*q1);  r4 = rt(p2^2 - 8*q2)

  {- x =  1/4 * (- p +- rt(p^2 - 8*q)).  That is

     x1 = 1/4 * (- p1 + rt(p1^2 - 8*q1))  = (- p1 + r3)/4
     x2 =                                 = (- p1 - r3)/4
     x3 = 1/4 * (- p2 + rt(p2^2 - 8*q2))  = (- p2 + r4)/4
     x4 =                                 = (- p2 - r4)/4
  -}
  r3_eq = r3^2 - p1^2 + m8*q1
  r4_eq = r4^2 - p2^2 + m8*q2


  ferrariEqs  =  r3_eq : r4_eq : r1_eq : r2_eq : cardano_f_res_c
  gFerrariEqs =  gBasisWithRadicals ferrariEqs

  (fourOn3, eightOn3) = (m4/m3, m8/m3)  :: (P, P)

  rel =  r1*r2 + fourOn3*alP*u + eightOn3*alP   :: P
  -- 
  -- rel =  r1*r2 + (4/3)*al*u + (8/3)*al  
  --                             is proportional over Al to  viete_f_1,
  -- and it needs to be added to  I(ferrariEqs).

  -- Note:  for  conjRel = - r1*r2 + (4/3)*al*u + (8/3)*al,
  --             rel * conjRel  is in  Ideal(ferrariEqs).
  --             Does it follow that  rel  is zero on the Ferrari tuples? 

  ferrariEqs_plus =  fst $ gBasis (rel : gFerrariEqs)

  (dFerrI, ferrI) = gensToIdeal ferrariEqs_plus [] [(IsGxBasis, Yes)]

                                [(IsMaxIdeal, Yes)] -- ? only for gBasis in PE
                                dP Map.empty
                                                
  unFerr = Rsi unP (ferrI, dFerrI) dP    -- 1  in Ferr = P/(ferrariEqs_plus)

  dFerr = upField unFerr Map.empty    -- ? only for gBasis in PE

  alToFerr :: Al -> Ferr
  alToFerr =  ctr unFerr . ctr unP

  x1pre = (- p1) + r3   :: P
  x2pre = (- p1) - r3
  x3pre = (- p2) + r4
  x4pre = (- p2) - r4

  oneOn4  = m1/m4  :: P

  f_rootsP = [h/m4 | h <- [x1pre, x2pre, x3pre, x4pre]]  :: [P]
  f_roots  = map (ctr unFerr) f_rootsP  :: [Ferr]

  [g1, g2, g3, g4] = f_roots   :: [Ferr]  -- `g' stands for \gamma

  elemSyms4 = [g1 + g2 + g3 + g4,                              -- -a
               g1*g2 + g1*g3 + g1*g4 + g2*g3 + g2*g4 + g3*g4,  -- b
               g1*g2*g3 + g1*g2*g4 + g1*g3*g4 + g2*g3*g4,      -- -c
               g1*g2*g3*g4                                     -- dd
              ]              :: [Ferr]
  
  [a'', b'', c'', d''] = map (ctr unFerr) [a', b', c', dd']

  viete_f = zipWith (-) elemSyms4 [- a'', b'', - c'', d'']
  

  ----------------------------------------------------------------------------
  -- Choose `chosen' in {g1 .. g4}  and express the roots of 
  --
  --        g =  y^3 + (1/chosen^2 - 4)*y + 2*chosen.

  chosen = g4  :: Ferr    -- edit this


  unPFerr = cToUPol "y" dFerr unFerr  :: PFerr  -- 1 in Ferr[y]
  y       = varP unFerr unPFerr       :: PFerr

  inv_chosen = inv chosen   :: Ferr

  (p3, q3) = (inv_chosen^2 - n4, n2*chosen)  :: (Ferr, Ferr)
             where
             [n2, n4] = map (fromi unFerr) [2, 4]

  [p3', q3'] = map (ctr unPFerr) [p3, q3]  :: [PFerr]

  g =  y^3 + p3'*y + q3'   :: PFerr

  -- Apply the Cardano formulae for a canonic  g.

  discr_g =  - n4*p3^3 - n27*q3^2   :: Ferr   -- disciminant g
             where
             [n4, n27] = map (fromi unFerr) [4, 27]

  varsE = ["uu", "vv", "d2"]  

  ppCompE (Vec [u, v, d ]) (Vec [u', v', d']) =
                           case 
                               compare (u + v) (u' + v') 
                           of 
                           EQ  -> lexListComp compare [u, d] [u', d']
                           val -> val

  oE   = (("deg2lex", 3), ppCompE, [])
  unPE = cToPol oE varsE dFerr unFerr    :: PE   -- 1 in PE = Ferr[varsE]
  dPE  = upGCDLinSolvRing unPE Map.empty    
  [uu, vv, d2] = varPs unFerr unPE         :: [PE]
  rF           = ctr unFerr $ ctr unP r''  :: Ferr 
  rPE          = ctr unPE rF               :: PE
  discr_g'     = ctr unPE discr_g          :: PE
  [p3'', q3''] = map (ctr unPE) [p3, q3]   :: [PE]

  eqsE = [d2^2 - discr_g',
          uu^3 - n3On2*d2*rPE + n27On2*q3'',
          vv^3 + n3On2*d2*rPE + n27On2*q3'',
          uu*vv + n3'*p3''
         ]
         where [n2, n3, n27]        = map (fromi unFerr) [2, 3, 27] 
               [n3', n3On2, n27On2] = map (ctr unPE) [n3, n3/n2, n27/n2]

  eqsE_gr = fst $ gBasis eqsE


  -- Build  E = Ferr/I(eqsE).

  (dEI, eI) = gensToIdeal eqsE_gr [] [(IsGxBasis, Yes)] [] dPE Map.empty
                                                    -- (IsMaxIdeal, Yes) ?
  unE = Rsi unPE (eI, dEI) dPE      :: E  -- 1 in E
  dE  = upLinSolvRing unE Map.empty

  ferrToE :: Ferr -> E
  ferrToE =  ctr unE . ctr unPE

  alToE :: Al -> E
  alToE =  ferrToE . alToFerr

  [uu', vv', d2'] = map (ctr unE) [uu, vv, d2]   :: [E]

  gRoots = [(uu' + vv')/n3,                      -- roots to g
            (r*vv' - r*uu' - uu' - vv')/n6,
            (r*uu' - r*vv' - uu' - vv')/n6
           ]                                        :: [E]
           where [n3, n6] = map (fromi unE) [3, 6]
                 r        = alToE r''

  inv_gRoots       = map inv gRoots
  check_inv_gRoots = [xi*(inv xi) | xi <- gRoots]
  [xi1, xi2, xi3]  = gRoots

  viete_g = [xi1 + xi2 + xi3,                    -- elSym1 = 0
             xi1*xi2 + xi1*xi3 + xi2*xi3 - p,    -- elSym2 = p
             xi1*xi2*xi3 + q                     -- elSym0 = -q
            ]
            :: [E]
            where  [p, q] = map ferrToE [p3, q3]

  -- Lift  f, g  to  E[z].

  unEz = cToUPol "z" dE unE   :: Ez    -- Ez = UPol E  -- E[z]
  z    = varP unE unEz        :: Ez

  fE =  z^4 + a3'*z^3 + a2'*z^2 + a1'*z + a0'     :: Ez
        where
        [a3', a2', a1', a0'] = map (ctr unEz . alToE) [a3, a2, a1, a0]
 
  gE =  z^3 + p*z + q    :: Ez
                         where [p, q] = map (ctr unEz . ferrToE) [p3, q3]

  g_on_gRoots = [pValue gE [xi] | xi <- gRoots]  :: [E]


  chosen'                  = ferrToE chosen                        :: E
  otherRoots               = delete chosen' $ map ferrToE f_roots  :: [E]
  [other1, other2, other3] = otherRoots

  goal :: E -> E -> E     -- xi^9 * (f(1/xi)*g(gam))^2  +
  goal gam xi =           -- 2*chosen * (f(xi)*gam^3*g(1/gam))^2
                          -- must be  0

                 (xi^9) * (f_inv_xi*g_gam)^2  +
                 n2*chosen' * ((f_xi*(gam^3)*g_inv_gam))^2
                 where
                 n2        = fromi chosen' 2
                 f_xi      = pValue fE [xi]
                 f_inv_xi  = pValue fE [inv xi]
                 g_gam     = pValue gE [gam]
                 g_inv_gam = pValue gE [inv gam]

  goals = [goal gamma xi | gamma <- otherRoots, xi <- gRoots]
                                                        -- must be 9 zeroes





  {- Need this ?  **************************************************
     Find algebraic relations for  f_roots  in  Ferr.

  xx  = ["x1", "x2", "x3", "x4"]
  unX = cToPol (lexPPO 4) xx dAl unAl   -- 1 in PX = Al[x1,x2,x3,x4]
  dPX = upGCDLinSolvRing unX Map.empty

  [x1, x2, x3, x4] = varPs unAl unX  :: [PX]
  o'               = lexPPO 4
                     -- (("deglex", 4), degLex, [])  takes very long. Why?

  f_root_rels = algRelsPols ferrariEqs_plus ["x1", "x2", "x3", "x4"] o' 
                                                               f_rootsP
  elemSymsX = [x1 + x2 + x3 + x4,                              -- -a
               x1*x2 + x1*x3 + x1*x4 + x2*x3 + x2*x4 + x3*x4,  -- b
               x1*x2*x3 + x1*x2*x4 + x1*x3*x4 + x2*x3*x4,      -- -c
               x1*x2*x3*x4                                     -- dd
              ]              :: [PX]
  
  viete_f_X = zipWith (-) elemSymsX [- aa3, aa2, - aa1, aa0]  :: [PX]
              where
              [aa3, aa2, aa1, aa0] = map (ctr unX) [a3, a2, a1, a0]

  gViete = fst $ gBasis viete_f_X
                                       
  viete_by_rels  = map (fst . polNF "rc" f_root_rels) viete_f_X
  rels_by_gViete = map (fst . polNF "rc" gViete) f_root_rels
  -}
{-
  -- We need to compute in  PX/Rel_Gam_Fer,
  -- where  Rel_Gam_Fer = Relations_for_Gam in P

  viete_f    = zipWith (-) elemSyms [- aa3, aa2, - aa1, aa0]
  additional = []
  fs         = additional ++ viete_f 
  gs         = fst $ gBasis fs

  -- Build   F = Al[xx]/I(gs)
  (dF0, gsI) = gensToIdeal gs [] [(IsGxBasis, Yes)] [] dPX Map.empty
             
  unF = Rsi unX (gsI, dF0) dPX       :: F
  dF  = upLinSolvRing unF Map.empty 
  [x1', x2', x3', x4'] = map (ctr unF) [x1, x2, x3, x4]   :: [F]  
-}
              




{- Results  ********************************************************

f       =  x^4 + 4*al*x^3 + 2*x^2 - 1/3

res_f   =  x^3 - 2*x^2 + (4/3)*x + ((16/3)*al^2 - 8/3)

res_f_c =  x^3 + ((16/3)*al^2 - 64/27)

res_discr =  - 768*al^4 + (2048/3)*al^2 - 4096/27

d   =  r*(16*al^2 - 64/9)
d^2 =  - 768*al^4 + (2048/3)*al^2 - 4096/27

cardano_f_res_c =  [v,  u^3 + (144*al^2 - 64)]

y1 = (u + 2)/3

ferrariEqs =
[
r3^2 - r1^2 - 8 al r1 - 8 r2 + (8/3) u - 16 al^2 + 16/3,
r4^2 + (-1)*r1^2 + 8*al*r1 + 8*r2 + (8/3)*u - 16*al^2 + 16/3,
r1^2 - (4/3)*u - 16*al^2 + 16/3,
r2^2 - (1/9)*u^2 - (4/9)*u - 16/9,  
v,
u^3 + 144*al^2 - 64
]

gFerrariEqs =
[
v, 
u^3 + 144*al^2 - 64,  
r2^2 - (1/9)*u^2 - (4/9)*u - 16/9,  
r1^2 - (4/3)*u - 16*al^2 + 16/3,  
r4^2 + 8*al*r1 + 8*r2 + (4/3)*u - 32*al^2 + 32/3, 
r3^2 - 8*al*r1 - 8*r2 + (4/3)*u - 32*al^2 + 32/3  
]

rel =  r1*r2 + (4/3)*al*u + (8/3)*al  

is proportional to  viete_f_1,
and it needs to be added to  ferrariEqs.

ferrariEqs_plus =
[
v, 
u^3 + 144*al^2 - 64, 

r2^2 - (1/9)*u^2 - (4/9)*u - 16/9, 
r1 - (1/(12*al))*r2*u^2 + (1/(6*al))*r2*u + (2/(3*al))*r2,

r4^2 + (2/3)*r2*u^2 - (4/3)*r2*u + (8/3)*r2 + (4/3)*u - 32*al^2 + 32/3, 

r3^2 - (2/3)*r2*u^2 + (4/3)*r2*u - (8/3)*r2 + (4/3)*u - 32*al^2 + 32/3
]

Evidently,  Ideal(ferrariEqs_plus)  is maximal (?).

lpps by r_i = {r1, r2^2, r3^2, r4^2}.  dim-over-Al(y1) = 8.

dim Al(y1) = 3.   dim-over-Al = 24.


f_roots =
[
(1/4)*r3 - (1/(48*al))*r2*u^2 + (1/(24*al))*r2*u + (1/(6*al))*r2 - al, 
(-1/4)*r3 - (1/(48*al))*r2*u^2 + (1/(24*al))*r2*u + (1/(6*al))*r2 - al, 
(1/4)*r4 + (1/(48*al))*r2*u^2 - (1/(24*al))*r2*u - (1/(6*al))*r2 - al,
(-1/4)*r4 + (1/(48*al))*r2*u^2 - (1/(24*al))*r2*u - (1/(6*al))*r2 - al
]

test inv roots =  [(((1))),(((1))),(((1))),(((1)))]


Put chosen = g1
---------------

g = y^3 
    + y *( - (1/(32*al))*r3*r2*u^2 + (1/(16*al))*r3*r2*u + (1/(4*al))*r3*r2 
           + (3/2)*al*r3 + (3/2)*r2 - 1
         )
    + (1/2)*r3 - (1/(24*al))*r2*u^2 + (1/(12*al))*r2*u + (1/(3*al))*r2 - 2*al


discr_g =  (3/al)*r3*r2*u^2 - (6/al)*r3*r2*u - (24/al)*r3*r2 - 72*al*r3 
           - 6*r2*u^2 + 12*r2*u - 96*r2 - 864*al^2 + 256

        =  r3*r2*(3/al)*(u^2 - 2*u - 8) - 72*al*r3 + 6*r2*(- u^2 + 2*u - 16)
           - 864*al^2 + 256

eqsE =
[
d2^2 - (3/al)*r3*r2*u^2 + (6/al)*r3*r2*u + (24/al)*r3*r2 + 72*al*r3 + 6*r2*u^2
     - 12*r2*u + 96*r2 + 864*al^2 - 256
, 
uu^3 - (3/2)*r*d2 
     + (27/4)*r3 - (9/(16*al))*r2*u^2 + (9/(8*al))*r2*u + (9/(2*al))*r2 - 27*al
, 
vv^3 + ((3/2)*r)*d2 
     + (27/4)*r3 - (9/(16*al))*r2*u^2 + (9/(8*al))*r2*u + (9/(2*al))*r2 - 27*al
, 
uu*vv - (3/(32*al))*r3*r2*u^2 + (3/(16*al))*r3*r2*u + (3/(4*al))*r3*r2 
      + (9/2)*al*r3 + (9/2)*r2 - 3
]

eqsE_gr =
[
d2^2 - (3/al)*r3*r2*u^2 + (6/al)*r3*r2*u + (24/al)*r3*r2 + 72*al*r3 + 6*r2*u^2
     - 12*r2*u + 96*r2 + 864*al^2 - 256
, 
vv^2 + 
  ( (((-11/36864)*r)/(al^3 - (121/576)*al))*r3*r2*u^2 
    + (((11/18432)*r)/(al^3 + ((-121/576))*al))*r3*r2*u 
    + (((-1/64)*r*al^2 + (11/4608)*r)/(al^3 - (121/576)*al))*r3*r2 
    + ((((-1/192)*r)*al)/(al^2 + ((-121/576))))*r3*u 
    + ((((-1/256)*r)*al)/(al^2 + ((-121/576))))*r3 
    + ((((1/1536)*r))/(al^2 + ((-121/576))))*r2*u^2 
    + ((((1/256)*r))/(al^2 + ((-121/576))))*r2*u 
    + ((((-3/256)*r))/(al^2 + ((-121/576))))*r2 
    + ((((1/32)*r)*al^2 + ((11/1152)*r))/(al^2 + ((-121/576))))
  )*uu*d2 
  + 
  (((((3/512)))/(al^2 + ((-121/576))))*r3*r2*u^2 
    + ((((-3/256)))/(al^2 + ((-121/576))))*r3*r2*u 
    + ((((9/512)))/(al^2 + ((-121/576))))*r3*r2 
    + ((((11/512)))/(al^2 + ((-121/576))))*r3*u 
    + ((((9/32))*al^2 + ((-11/256)))/(al^2 + ((-121/576))))*r3 
    + ((((-3/64))*al^2 + ((11/1536)))/(al^3 + ((-121/576))*al))*r2*u^2 
    + ((((3/32))*al^2 + ((-55/1536)))/(al^3 + ((-121/576))*al))*r2*u 
    + ((((3/32))*al^2 + ((11/384)))/(al^3 + ((-121/576))*al))*r2 
    + ((((-9/4))*al^3 + ((5/32))*al)/(al^2 + ((-121/576))))
  )*uu
, 
uu*vv - (3/(32*al))*r3*r2*u^2 + (3/(16*al))*r3*r2*u 
      + (3/(4*al))*r3*r2 + (9/2)*al*r3 + (9/2)*r2 - 3
, 
uu^2 + 
  ((((11/36864)*r)/(al^3 + (-121/576)*al))*r3*r2*u^2 
    + ((((-11/18432)*r))/(al^3 - (121/576)*al))*r3*r2*u 
    + (((1/64)*r*al^2 - (11/4608)*r)/(al^3 - (121/576)*al))*r3*r2 
    + (((1/192)*r*al)/(al^2 - 121/576))*r3*u 
    + (((1/256)*r*al)/(al^2 - 121/576))*r3 
    + (((-1/1536)*r)/(al^2 - 121/576))*r2*u^2 
    + (((-1/256)*r)/(al^2 - 121/576))*r2*u 
    + (((3/256)*r)/(al^2 - 121/576))*r2 
    + (((-1/32)*r*al^2 - (11/1152)*r)/(al^2 - 121/576))
  )*vv*d2 
  + 
  (((3/512)/(al^2 - 121/576))*r3*r2*u^2 
    + ((-3/256)/(al^2 + (-121/576)))*r3*r2*u 
    + ((9/512)/(al^2 - 121/576))*r3*r2 
    + ((11/512)/(al^2 - 121/576))*r3*u 
    + (((9/32)*al^2 - 11/256)/(al^2 - 121/576))*r3 
    + (((-3/64)*al^2 + 11/1536)/(al^3 - (121/576)*al))*r2*u^2  -- ?
    + (((3/32)*al^2 - 55/1536)/(al^3 - (121/576)*al))*r2*u 
    + (((3/32)*al^2 + 11/384)/(al^3 - (121/576)*al))*r2 
    + (((-9/4)*al^3 + (5/32)*al)/(al^2 - 121/576))
  )*vv
]

-- one more copy:
[
d2^2 + ((((-3))/(al))*r3*r2*u^2 + (((6))/(al))*r3*r2*u + (((24))/(al))*r3*r2
  + ((72)*al)*r3 + ((6))*r2*u^2 + ((-12))*r2*u + ((96))*r2 + ((864)*al^2
     + (-256)))
,
vv^2 + ((((-11/36864)*r)/(al^3  -121/576*al))*r3*r2*u^2
 + ((11/18432)*r/(al^3 + (-121/576)*al))*r3*r2*u + (((-1/64)*r*al^2
 + (11/4608)*r)/(al^3 - (121/576)*al))*r3*r2
 + (((-1/192)*r)*al/(al^2 - 121/576))*r3*u
 + (((-1/256)*r*al)/(al^2 + (-121/576)))*r3
 + ((1/1536)*r/(al^2 - 121/576))*r2*u^2
 + (((1/256)*r)/(al^2 + ((-121/576))))*r2*u 
 + ((((-3/256)*r))/(al^2 + ((-121/576))))*r2 + ((((1/32)*r)*al^2 
 + ((11/1152)*r))/(al^2 + ((-121/576)))))*uu*d2 
 + (((3/512)/(al^2 + (-121/576)))*r3*r2*u^2
 + ((-3/256)/(al^2 - 121/576))*r3*r2*u
 + ((9/512)/(al^2 + (-121/576)))*r3*r2 + ((11/512)/(al^2 + ((-121/576))))*r3*u
 + (((9/32)*al^2 - 11/256)/(al^2 - 121/576))*r3 
 + (((-3/64)*al^2 + 11/1536)/(al^3 + (-121/576)*al))*r2*u^2 
 + (((3/32)*al^2 - 55/1536)/(al^3 + (-121/576)*al))*r2*u + (((3/32)*al^2 
 + (11/384))/(al^3 - 121/576)*al))*r2 + (((-9/4)*al^3 
 + (5/32)*al)/(al^2 - 121/576)))*uu
,
uu*vv + ((-3/32)/al)*r3*r2*u^2 + ((3/16)/al)*r3*r2*u + ((3/4)/al)*r3*r2 
      + (9/2)*al*r3 + (9/2)*r2 - 3
,
uu^2 + ((((11/36864)*r)/(al^3 - 121/576)*al)*r3*r2*u^2
 + (((-11/18432)*r)/(al^3 + (-121/576)*al))*r3*r2*u + ((((1/64)*r)*al^2
 + (-11/4608)*r)/(al^3 + (-121/576)*al))*r3*r2
 + ((1/192)*r*al/(al^2 + (-121/576)))*r3*u
 + (((1/256)*r*al)/(al^2 - 121/576))*r3
 + (((-1/1536)*r)/(al^2 - 121/576))*r2*u^2
 + (((-1/256)*r)/(al^2 - 121/576))*r2*u + (((3/256)*r)/(al^2 - 121/576))*r2
 + (((-1/32)*r*al^2 + (-11/1152)*r)/(al^2 - 121/576)))*vv*d2
 + (((3/512)/(al^2 - 121/576))*r3*r2*u^2
 + ((-3/256)/(al^2 - 121/576))*r3*r2*u + ((9/512)/(al^2 - 121/576))*r3*r2
 + ((11/512)/(al^2 - 121/576))*r3*u
 + (((9/32)*al^2 - 11/256)/(al^2 - 121/576))*r3
 + (((-3/64)*al^2 + (11/1536))/(al^3 + (-121/576)*al))*r2*u^2
 + (((3/32)*al^2 + (-55/1536))/(al^3 + (-121/576)*al))*r2*u
 + (((3/32)*al^2 + 11/384)/(al^3 + (-121/576)*al))*r2
 + (((-9/4)*al^3 + (5/32)*al)/(al^2 - 121/576)))*vv
]



gRoots = [ (1/3)*uu + (1/3)*vv, 
           ((-1/6)*r - 1/6)*uu + ((1/6)*r  - 1/6)*vv, 
           ((1/6)*r  - 1/6)*uu + ((-1/6)*r - 1/6)*vv
         ]
check_inv_gRoots = [((((1)))),((((1)))),((((1))))]
viete_g          = [(0),(0),(0)]

fE =  z^4 + 4*al*z^3 + 2*z^2 - 1/3

gE =
z^3 + z * (((((-1/32))/al)*r3*r2*u^2 + (((1/16))/(al))*r3*r2*u 
            + ((1/4)/al)*r3*r2 + ((3/2)*al)*r3 + (3/2)*r2 - 1)
          )  
    + (((1/2)*r3 + ((-1/24)/al)*r2*u^2 + ((1/12)/al)*r2*u 
                                         + ((1/3)/al)*r2 - 2*al))
g_on_gRoots = [(0),(0),(0)]



goals = [(0),(0),(0), (0),(0),(0), (0),(0),(0)]

------------
x + 9y = 256  min
x + y  = 90                  8y = 166   y = 20 min,  x = 70 min 

Timing for a  3 GHz machine:   
                           eqsE_gr                   takes  70 min,
                           each root pair (gam, xi)  takes  20 min. 
  (there are 36 root pairs to test).
------------



Put chosen = g2 
---------------

g = y^3 + (((1/32)/al)*r3*r2*u^2 + ((-1/16)/al)*r3*r2*u + ((-1/4)/al)*r3*r2 
          + (-3/2)*al*r3 + (3/2)*r2 - 1)*y 
          + ((-1/2)*r3 + ((-1/24)/al)*r2*u^2 + ((1/12)/al)*r2*u 
          + ((1/3)/al)*r2 - 2*al)

goals = [(0),(0),(0), (0),(0),(0), (0),(0),(0)]



Put chosen = g3 
---------------

chosen =  
       (1/4)*r4 + ((1/48)/al)*r2*u^2 + ((-1/24)/al)*r2*u - ((1/6)/al)*r2 - al

g =
y^3 + (((1/32)/al)*r4*r2*u^2 + ((-1/16)/al)*r4*r2*u + (((-1/4))/al)*r4*r2 
        + (3/2)*al*r4 - (3/2)*r2 - 1
       )*y
    + 
    (1/2)*r4 + ((1/24)/al)*r2*u^2 + ((-1/12)/al)*r2*u + ((-1/3)/al)*r2 - 2*al

goals = [(0),(0),(0), (0),(0),(0), (0),(0),(0)]



Put chosen = g4 
---------------

y^3 + (((-1/32)/al)*r4*r2*u^2 + ((1/16)/al)*r4*r2*u + ((1/4)/al)*r4*r2 
    + ((-3/2)*al*r4 + (-3/2)*r2 - 1)*y + ((-1/2)*r4 + ((1/24)/al)*r2*u^2 
    + ((-1/12)/al)*r2*u + ((-1/3)/al)*r2 - 2*al)



** reserve *************************************
f_root_rels =
[
x4^4 + 4*al*x4^3 + 2*x4^2 - 1/3
, 
x3^3 + x3^2*x4 + 4*al*x3^2 + x3*x4^2 + 4*al*x3*x4 + 2*x3 + x4^3 + 4*al*x4^2 
  + 2*x4
,
x2^2 + x2*x3 + x2*x4 + 4*al*x2 + x3^2 + x3*x4 + 4*al*x3 + x4^2 + 4*al*x4 + 2
, 
x1 + x2 + x3 + x4 + 4*al
]

gViete == f_root_rels 

lpp-s = {x1, x2^2, x3^3, x4^4}.  dim = 24.

under-pps = {x2^i*x3^j*x4^k | i <= 1, j <= 2, k <= 3}.
**********************************************************
-}