--------------------------------------------------------------------
--------------------------------------------------------------------
--  The Algebraic Domain Constructor  DoCon,   version 2.09
--
--  Copyright  Serge D.Mechveliani,  2005
--------------------------------------------------------------------
--------------------------------------------------------------------



-- A part of demonstration and test.

module Main 
where
import qualified Data.Map as Map (empty)
import DExport


-- Arithmetic  of  Cyclic Integer ring modelled via Groebner 
-- basis over Integer.
-- See  (Manual 'rsi.ex.c').
-- The cyclic integers are the elements of  CI = Z[x]/(g),
--
-- Z = Integer,  g = x^p' + x^(p'-1) +..+ 1,   p' = p - 1,  p prime.
--
-- g = (x^p - 1)/(x - 1)   is irreducible.
-- Concerning the arithmetics in CI,  see, for example, the book
--                    [Ed]: H.M.Edwards "Fermat's last theorem ...".
-- DoCon applies the constructor composition   ResidueI (UPol Z)
-- - using the underlying Groebner basis technique over an Euclidean 
-- ring.

--------------------------------------------------------------------
type P  = UPol Integer      -- Z[x]
type CI = ResidueI P        -- to represent P/(g)  - cyclic integers

cyclIntDemo :: Integer -> String -> String ->
               -- p       f1str     f2str

               ([PropValue],   -- a couple of tests  
                [CI],          -- [unity of CI,  x projection in CI]
                [CI],          -- [f1, f2]  read from  f1str, f2str
                Maybe CI,      -- divide_m f1 f2  in  CI
                [CI],          -- [norm f1, norm f2]
                Maybe CI       -- divide_m (norm f1) (norm f2)
               )

-- Build the ideal in  Z[x]  for cyclic integers for  p.
-- Build the cyclic integer ring as a residue ring  CI.
-- Read the two strings to polynomials in x, projecting them further 
--   to the elements  f1, f2  in  CI.
-- Compute in CI:  f1/f2, norm f1, norm f2, (norm f1)/(norm f2)

cyclIntDemo p f1str f2str =
  let                                             
    substXPower :: P -> Integer -> P
    substXPower    f    n    = ct f [(a, e*n)| (a, e) <- upolMons f]
             --
             -- f(x) -> f(x^n).  
             -- Here (ct f..) converts monomial list to domain of f.

    norm :: CI -> CI                   -- norm of cyclic integer r =
    norm  r@(Rsi f (iI, _) _) =        -- product (orbit r)
            let                         
               Just [g] = idealGens iI
               p'       = ldeg g                        -- p - 1
               fPowers  = map (substXPower f) [2 .. p'] 
            in  
            product1 (r: (map (ctr r) fPowers))
                                      -- here  ctr r  projects to CI

    unP      = cToUPol "x" dZ 1               -- 1 of P
    dP       = upGCDLinSolvRing unP Map.empty 
    x        = varP 1 unP                     -- x as element of P  
    g        = (x^p - unP)/(x - unP)
    (dI, iI) = gensToIdeal [g] [] bProps propsI dP Map.empty
                                            -- setting Ideal(g) in P
    eI       = (iI, dI)
    bProps   = [(IsGxBasis, Yes)]
    propsI   = [(Prime, Yes), (IsMaxIdeal, No)]
    unCI     = Rsi unP eI dP                    -- 1 of CI
    (_, rCI) = baseRing unCI Map.empty
    propsCI  = subringProps rCI
    xCI      = ctr unCI x            -- project x to residue ring CI

    [f1, f2]       = map (smParse unCI) [f1str, f2str] 
    mbQuot         = divide_m f1 f2
    [norm1, norm2] = map norm [f1, f2]
    mbNormQuot     = divide_m norm1 norm2
  in 
  ([lookupProp IsField propsCI,  lookupProp HasZeroDiv propsCI], 
   [unCI, xCI],
   [f1, f2],
   mbQuot, 
   [norm1, norm2], 
   mbNormQuot
  )


main = 
  let 
    p = 5
        -- this example is taken from [Ed], section 4.2, exercise 11

    f1str = " 38*x^3 + 62*x^2 + 56*x + 29 "
    f2str = " 3*x^3 +  4*x^2 +  7*x +   1 "

    -- f1  should be a multiple of  f2,
    -- hence, norm(f1) should be a multiple of norm(f2)
  in
  case  cyclIntDemo p f1str f2str
  of
  ([isField_CI, hasZeroDiv_CI],  [unCI, xCI],  [f1, f2],
   mbQuot,                       _norms,       mbNormQuot
   )
    ->
      putStr $ concat
      ["\n",
       "[isField CI, hasZeroDiv CI] = ", 
                             shows [isField_CI, hasZeroDiv_CI] "\n",

       "unCI =  ",                  shows unCI       "\n",
       "xCI  =  ",                  shows xCI        "\n",
       "f1   =  ",                  shows f1         "\n",
       "f2   =  ",                  shows f2         "\n",
       "divide_m f1 f2 = ",         shows mbQuot     "\n",
       "divide_m norm1 norm2 = ",   shows mbNormQuot "\n"
      ]