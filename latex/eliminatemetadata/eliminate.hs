import System.Environment (getArgs)
import System.Exit (exitFailure)
import Text.Regex
import Control.Monad

regexMetaData = "[\\]ExecuteMetaData[[](.*).tex]{([^}]*)}"

regexTag tag = "%<[*]" ++ tag ++ ">((\n|.)*)%</" ++ tag ++ ">"

eliminate :: String -> String -> String -> IO ()
eliminate fileOut strproc strrest = case matchRegexAll (mkRegex regexMetaData) strrest of
    Just (b,m,a,[file,tag]) ->
       do 
          strtagfile <- readFile (file++".tex") 
          case matchRegexAll (mkRegex (regexTag tag)) strtagfile of
              Just (_,_,_,(tagstr:_)) -> eliminate fileOut (strproc ++ b ++ tagstr ++ "\n%" ++ m) a
              Nothing -> error ("tag:" ++ tag ++ " not found in file:"  ++ file++".tex")
    Nothing -> writeFile fileOut (strproc ++ strrest)

main :: IO ()
main = do args <- getArgs
          case args of
            [fileIn,fileOut] -> readFile fileIn >>= eliminate fileOut []
            _      -> do putStrLn "Usage: eliminate <SourceFile> <OutputFiles>"
                         exitFailure


