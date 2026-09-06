-- | Build a static HTML site for nuprl-hs into @website/@, suitable for
-- GitHub Pages. Example theories are checked with the kernel and rendered as
-- annotated, interactive documents; the browser performs no proving.
module Main (main) where

import Control.Monad (forM, forM_, unless, when)
import Data.List (sort)
import Data.Maybe (fromMaybe)
import Data.Text qualified as T
import Data.Text.IO qualified as TIO
import Options.Applicative
import System.Directory
  ( createDirectoryIfMissing
  , doesDirectoryExist
  , doesFileExist
  , getCurrentDirectory
  , listDirectory
  )
import System.Exit (exitFailure)
import System.FilePath ((</>), takeExtension, takeFileName)
import System.IO (hPutStrLn, stderr)

import Analyze
import Assets
import Html (fromHtml)
import Pages

data Opts = Opts
  { optRoot :: Maybe FilePath
  , optOut :: Maybe FilePath
  }

optsParser :: Parser Opts
optsParser =
  Opts
    <$> optional
      ( strOption
          ( long "root"
              <> metavar "DIR"
              <> help "Project root (directory that contains examples/). Default: search from cwd."
          )
      )
    <*> optional
      ( strOption
          ( long "out"
              <> metavar "DIR"
              <> help "Output directory. Default: <root>/website"
          )
      )

main :: IO ()
main = do
  opts <-
    execParser $
      info
        (optsParser <**> helper)
        ( fullDesc
            <> progDesc "Generate a static GitHub Pages site for nuprl-hs"
            <> header "build-website — nuprl-hs static site"
        )
  root <- maybe findRoot pure (optRoot opts)
  let outDir = fromMaybe (root </> "website") (optOut opts)
      exDir = root </> "examples"
  exists <- doesDirectoryExist exDir
  unless exists $ do
    hPutStrLn stderr ("no examples/ directory under " <> root)
    exitFailure
  files <- fmap (map (exDir </>) . sort . filter isTheory) (listDirectory exDir)
  when (null files) $ do
    hPutStrLn stderr ("no .nuprl files in " <> exDir)
    exitFailure
  putStrLn ("root    " <> root)
  putStrLn ("output  " <> outDir)
  putStrLn ("theories " <> show (length files))
  examples <- forM files $ \fp -> do
    src <- TIO.readFile fp
    let ax = annotateSource fp src
    case axError ax of
      Just e -> hPutStrLn stderr ("  warning " <> takeFileName fp <> ": " <> T.unpack e)
      Nothing ->
        putStrLn
          ( "  "
              <> takeFileName fp
              <> "  "
              <> show (countTheorems ax)
              <> " theorems, "
              <> show (countAbs ax)
              <> " abstractions"
          )
    pure ax
  writeSite outDir examples
  putStrLn ("wrote " <> outDir)

isTheory :: FilePath -> Bool
isTheory p = takeExtension p == ".nuprl"

findRoot :: IO FilePath
findRoot = do
  cwd <- getCurrentDirectory
  let candidates = take 6 (iterate parent cwd)
  found <- findFirst isProject candidates
  case found of
    Just r -> pure r
    Nothing -> do
      hPutStrLn stderr "could not find project root (looked for examples/*.nuprl and package.yaml)"
      exitFailure
  where
    parent p = let d = takeDir p in if d == p then p else d
    takeDir = reverse . drop 1 . dropWhile (`notElem` ("/\\" :: String)) . reverse

findFirst :: (FilePath -> IO Bool) -> [FilePath] -> IO (Maybe FilePath)
findFirst _ [] = pure Nothing
findFirst p (x : xs) = do
  ok <- p x
  if ok then pure (Just x) else findFirst p xs

isProject :: FilePath -> IO Bool
isProject dir = do
  pkg <- doesFileExist (dir </> "package.yaml")
  ex <- doesDirectoryExist (dir </> "examples")
  pure (pkg && ex)

writeSite :: FilePath -> [AnnotatedExample] -> IO ()
writeSite out examples = do
  createDirectoryIfMissing True (out </> "css")
  createDirectoryIfMissing True (out </> "js")
  createDirectoryIfMissing True (out </> "examples")
  TIO.writeFile (out </> "css" </> "site.css") css
  TIO.writeFile (out </> "js" </> "site.js") js
  TIO.writeFile (out </> "favicon.svg") faviconSvg
  TIO.writeFile (out </> ".nojekyll") ""
  TIO.writeFile (out </> "index.html") (fromHtml (indexPage examples))
  TIO.writeFile (out </> "404.html") (fromHtml notFoundPage)
  forM_ examples $ \ax -> do
    let dest = out </> "examples" </> T.unpack (axSlug ax) <> ".html"
    TIO.writeFile dest (fromHtml (examplePage ax))
