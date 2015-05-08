------------------------------------------------------------------------
------------------------------------------------------------------------
--  The Algebraic Domain Constructor  DoCon,   version 2.09
--
--  Copyright  Serge Mechveliani,    2005
------------------------------------------------------------------------
------------------------------------------------------------------------





module OpTab_ (parenTable, opTable) 

-- tables for the parentheses and operations for the infix parsing
where
import Iparse_ (ParenTable, OpTable)



--------------------------------------------------------------------
-- Edit the below scripts to change the parenthesis symbol  list  or
--
-- the infix operation symbol list.
--
-- See the files  princip.txt, Iparse.hs.
--------------------------------------------------------------------



parenTable :: ParenTable String
                        -- these are the DoCon prelude parentheses pairs

parenTable = [ ("(",")"), ("{","}"), ("<",">") ]



------------------------------------------------------------------------
-- Operation Table for  infixParse  function.


opTable :: OpTable String           -- the DoCon prelude infix table
opTable =        
         -- (0,r)            (l,r)            (l,0)
  [
   ("+",  ( Just (0,1,210,190), Just (1,1,100,100), Nothing )  ),
   ("-",  ( Just (0,1,210,190), Just (1,1,100,100), Nothing )  ),
   ("*",  ( Nothing,            Just (1,1,195,195), Nothing )  ),
   ("^",  ( Nothing,            Just (1,1,200,199), Nothing )  ),
   ("/",  ( Nothing,            Just (1,1,196,196), Nothing )  ),
   ("%",  ( Nothing,            Just (1,1,196,196), Nothing )  ),
                                      -- people use it for rationals

   (":/", ( Nothing,            Just (1,1,196,196), Nothing ) ),
                                           -- usually, for fractions

   (",",  ( Nothing,            Just (1,1, 80, 70), Nothing ) ),
                                      -- usually, a pair constructor

   ("'",  ( Just (0,1,220,190), Nothing           , Nothing  ) ),
                                   -- usually, a  Char  constructor.
                                   -- Thus  'a  reads to  'a'

   (":",  ( Nothing,            Just (1,1, 80, 70), Nothing  ) )
                                      -- usually, a list constructor


   -- ("[",  ( Just (0,1, 50, 40)], Nothing  , Nothing          ) ),
   -- ?? more list constructors 
   -- ("]",  ( Nothing,             Nothing , Just (1,0,20,20)] ) )
                                                       -- ?           
  ]
