import System.Environment
import System.Directory
import System.IO
import Data.List

-- initDirectory = "/home/james/Dropbox/Documents/Haskell/TEST/"
-- folderName = "s"

-- listTupleSwap :: [(a , b)] -> ([a] , [b])
-- listTupleSwap [] = ([] , [])
-- listTupleSwap ((x,y):xs) = (x : fst (listTupleSwap xs) , y : snd (listTupleSwap xs))




-- folderNameIO :: IO String
-- folderNameIO = do
--   fullDirectory <- getCurrentDirectory
--   let fullDirectoryReverse = reverse fullDirectory
--       shortList = takeWhile (\x -> x /= '/') fullDirectoryReverse
  -- return $ reverse shortList



-- func :: IO ()
-- func = do
--   filesInDirList <- listDirectory initDirectory
--   folderName <- folderNameIO
--   let initString = "{-# --without-k --rewriting #-}\nmodule UniAgda." ++ folderName ++ " where\n\n"
--       contents = [initString] ++ (map (\x -> "open import " ++ x ++ " public \n") filesInDirList)
--   writeFile (initDirectory ++ "Everything.agda") $ concat contents


-- filesAndFolders :: FilePath -> IO ([FilePath], [FilePath])
-- filesAndFolders path = do
--   contents <- listDirectory path
--   let (files, dirs) = partition (\xs -> '.' `elem` xs) contents
--   return (files, dirs)
  
-- agdaListofFiles :: FilePath -> IO ([FilePath])
-- agdaListofFiles path = do
--   contents <- listDirectory path
--   let (files, dirs) = partition (\xs -> '.' `elem` xs) contents
--       cleanDirs = delete "ltximg" dirs
--       cleanFiles = delete "Everything.lagda.org" $ delete "Everything.agda" files
--       subDirNames = map ((path ++ "/") ++) cleanDirs
--       ioListofFiles = sequence $ map agdaListofFiles subDirNames
--   listofFiles <- ioListofFiles
--   return $ cleanFiles ++ concat listofFiles


cleaningDirs :: [String] -> [String]
cleaningDirs = delete "ltximg" . delete "experimental" . delete "org" . delete "Everything" . delete "_build"

cleaningFiles :: [String] -> [String]
cleaningFiles files = delete "Everything" $ map (takeWhile (\x -> x /= '.')) files



agdaListofFilePaths :: FilePath -> IO ([FilePath])
agdaListofFilePaths path = do
  contents <- listDirectory path
  let (files, dirs) = partition (\xs -> '.' `elem` xs) contents
      cleanDirs = cleaningDirs dirs
      cleanFiles = map (\x -> (path ++ "/") ++ x) $ cleaningFiles files
      subDirNames = map ((path ++ "/") ++) cleanDirs
      ioListofFiles = sequence $ map (\x -> agdaListofFilePaths x) subDirNames
  listofFiles <- ioListofFiles
  return $ cleanFiles ++ concat listofFiles



replaceChar :: Char -> Char -> String -> String
replaceChar _ _ "" = ""
replaceChar c d (s:str)
  | c == s    = d : replaceChar c d str
  | otherwise = s : replaceChar c d str

uniAgdaFiles :: FilePath -> IO ([FilePath])
uniAgdaFiles path = do
  fileList <- agdaListofFilePaths path
  let newList = map (drop (length "/home/james/Dropbox/Documents/Agda/Univalent-Agda/")) fileList
      dotsNotSlashList = map (replaceChar '/' '.') newList
  return dotsNotSlashList


makeEverythingFile :: FilePath -> IO ()
makeEverythingFile path = do
  fileList <- uniAgdaFiles path
  let imports = map (\x -> "open import " ++ x ++ " public\n") fileList
  writeFile (path ++ "/Everything.lagda.org") $ concat $ [prelude] ++ imports ++ ["#+end_src"]
    where
      name = replaceChar '/' '.' $ drop (length "/home/james/Dropbox/Documents/Agda/Univalent-Agda/UniAgda/") path
      prelude = if name == "" then "#+title: UniAgda.Everything\n#+author: James Leslie\n#+STARTUP: noindent hideblocks latexpreview\n* Imports\n#+begin_src agda2\n{-# OPTIONS --without-K --rewriting #-}\nmodule UniAgda.Everything where\n\n"
        else "#+title: UniAgda." ++ name ++ ".Everything\n#+author: James Leslie\n#+STARTUP: noindent hideblocks latexpreview\n* Imports\n#+begin_src agda2\n{-# OPTIONS --without-K --rewriting #-}\nmodule UniAgda." ++ name ++ ".Everything where\n\n"



listofDirs :: FilePath -> IO ([FilePath])
listofDirs path = do
  contents <- listDirectory path
  let (files, dirs) = partition (\xs -> '.' `elem` xs) contents
      cleanDirs = cleaningDirs dirs
      subDirNames = map ((path ++ "/") ++) cleanDirs
      ioListofDirs = sequence $ map (\x -> listofDirs x) subDirNames
  list <- ioListofDirs
  return $ subDirNames ++ concat list

main = do
  dirs <- listofDirs path
  sequence $ map makeEverythingFile $ dirs
  where
    path = "/home/james/Dropbox/Documents/Agda/Univalent-Agda"
