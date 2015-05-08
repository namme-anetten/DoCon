module System_      -- Part of the DoCon Prelude.
                    -- All needed from here is  reexported by  DPrelude.

(partIOBuffer, outputStrings) -- axiomString_io
where
import System.IO (IOMode(..), IO(..), Handle, openFile, hPutStr, 
                                              hGetLine, hFlush)
import System.IO.Unsafe (unsafePerformIO)

import Prelude_ (Length(..), IsSingleton(..), Natural, 
                 mapTuple21, shOpt, showsByInit)
-- import Debug.Trace (trace)
 


------------------------------------------------------------------------
{- ? ----------
dir = showString "/home/mechvel/ghc/axiomInterface/"

toA_IO   = openFile (dir "toA")   WriteMode  :: IO Handle
fromA_IO = openFile (dir "fromA") ReadMode  
-- toA   = unsafePerformIO toA_IO   
-- fromA = unsafePerformIO fromA_IO

initIO :: IO (Handle, Handle)
initIO = do
         to   <- toA_IO
         from <- fromA_IO
         return (to, from)
-}


partIOBuffer :: Natural -> [String] -> (String, [String])
                -- bufSize strings      str     strings'
-- Part the initial concatenation portion  str  of  strings   which has 
-- size closest to  bufSize.  strings' is the remainder. 
-- In the concatenation the strings are separated with  semicolon.
-- It presumes that '\n' does not occur in  strings,
-- and '\n' is appended as the last letter to  str.
-- It is usually applied before  hPutStr,  and its aim is to reduce the 
-- number of the system calls by  hPutStr  (and thus to increase 
-- performance).

partIOBuffer bSize strings =  
                           mapTuple21 finish $ partBuf bSize id strings
  where
  message = showString "\npartIOBuffer " . shows bSize .
            showString "\n " . showsByInit (shOpt 1) 8 strings .
            showString "\n:\n"

  finish str = showString (dropWhile (== ';') str) "\n"

  partBuf bSize accumulated strings = 
    case 
        strings
    of
    []            -> (accumulated "", [])
    []:  _        -> error $ message "empty string encountered.\n"
    str: strings' -> 
         if  l >= bSize  then  (accum "", strings')
         else                  partBuf (bSize - l) accum strings'
         where
         l     = genLength str
         accum = accumulated . showChar ';' . showString str

------------------------------------------------------------------------
outputStrings :: Handle -> Natural -> [String] -> IO ()
                 -- hd     bufSize    strings
-- Put strings to the channel  hd  by the portions of length close to  
-- bufSize.

outputStrings hd bufSize strings = 
  do  
  let (str, strings') = partIOBuffer bufSize strings
  if  isSingleton str  then  return ()  
  else                       do {hPutStr hd str;  hFlush hd;
                                 outputStrings hd bufSize strings'} 

{-
axiomString_io :: (Handle, Handle) -> Natural -> [String] -> IO [String]
axiomString_io    (h1,     h2)        putSize    strings = 
  do
  let (str, strings') = partIOBuffer putSize strings
  hPutStr h1 str
  hFlush h1
  str' <- hGetLine h2
  return str'
-}
