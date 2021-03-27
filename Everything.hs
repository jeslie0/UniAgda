import           Data.List
import           System.Directory
import           System.Environment

-- Agda specific code, based off the previous functions

-- Using literate agda through org can generate latex fragments. We don't want to import them, or other misc files, so we filter them out.
cleaningDirs :: [String] -> [String]
cleaningDirs = delete "ltximg" . delete "experimental" . delete "org" . delete "Everything" . delete "_build"

cleaningFiles :: [String] -> [String]
cleaningFiles = delete "Everything" . delete "Everything.lagda.org" . delete "Everything.agda"


agdaListAllFilePaths :: FilePath -> IO ([FilePath])
agdaListAllFilePaths path = do
  contents <- listDirectory path
  let (files, dirs) = partition (\xs -> '.' `elem` xs) contents
      cleanDirs = cleaningDirs dirs
      cleanFiles = map ((path ++ "/") ++) $ cleaningFiles files
      subDirNames = map ((path ++ "/") ++) cleanDirs
      ioListofFiles = sequence $ map (\x -> agdaListAllFilePaths x) subDirNames
  listofFiles <- ioListofFiles
  return $ cleanFiles ++ concat listofFiles


-- Now we need to clean the files for use. We want to remove the given file path, the extension, change all '/' into '.' and add "UniAgda." as a prefix


replace :: (Eq a) => a -> a -> [a] -> [a]
replace _ _ [] = []
replace c d (x:xs)
  | c == x    = d : replace c d xs
  | otherwise = x : replace c d xs


-- really, we want to find the last string that this happens for
findSubstringStart :: (Integral a) => String -> String -> a
findSubstringStart "" _ = 0
findSubstringStart _ "" = 0
findSubstringStart word sentence
  | word == take (length word) sentence = 0
  | otherwise                           = findSubstringStart word (tail sentence) + 1


uniAgdaFiles :: FilePath -> IO ([FilePath])
uniAgdaFiles path = do
  filePathList <- agdaListAllFilePaths path
  let fileList = map (drop (findSubstringStart "UniAgda" path)) filePathList
      filesNoExt = map (reverse . drop (length ".lagda.org") . reverse) fileList
      cleanedFiles = map (replace '/' '.') filesNoExt
  return  cleanedFiles



-- Given a file path, it makes the Everything.lagda.org file in that folder, importing everything in all sub directories
makeEverythingFile :: FilePath -> IO ()
makeEverythingFile path = do
  fileList <- uniAgdaFiles path
  let fileName = path ++ "/Everything.lagda.org"
      imports = map (\x -> "open import " ++ x ++ " public\n") fileList
      title = replace '/' '.' $ drop (findSubstringStart "UniAgda" path) path
      options = if "UniAgda/Core" `isSubsequenceOf` path then
        "{-# OPTIONS --without-K --no-import-sorts #-}"
        else
        "{-# OPTIONS --without-K --rewriting --no-import-sorts #-}"
      prelude = "#+title: " ++ title ++ ".Everything\n#+author: James Leslie\n#+STARTUP: noindent hideblocks latexpreview\n* Imports\n#+begin_src agda2\n" ++ options ++ "\nmodule " ++ title ++ ".Everything where\n\n"
      contents = concat $ [prelude] ++ imports ++ ["#+end_src"]
  writeFile fileName contents

listofDirs :: FilePath -> IO ([FilePath])
listofDirs path = do
  contents <- listDirectory path
  let dirs = snd $ partition (\xs -> '.' `elem` xs) contents
      cleanDirs = cleaningDirs dirs
      subDirNames = map ((path ++ "/") ++) cleanDirs
      ioListofDirs = sequence $ map (\x -> listofDirs x) subDirNames
  list <- ioListofDirs
  return $ subDirNames ++ concat list

main :: IO [()]
main = do
  args <- getArgs
  dirs <- listofDirs (args !! 0)
  sequence $ map makeEverythingFile $ dirs
