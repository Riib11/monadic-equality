{-# LANGUAGE CPP #-}
{-# LANGUAGE NoRebindableSyntax #-}
{-# OPTIONS_GHC -fno-warn-missing-import-lists #-}
module Paths_monadic_equality (
    version,
    getBinDir, getLibDir, getDynLibDir, getDataDir, getLibexecDir,
    getDataFileName, getSysconfDir
  ) where

import qualified Control.Exception as Exception
import Data.Version (Version(..))
import System.Environment (getEnv)
import Prelude

#if defined(VERSION_base)

#if MIN_VERSION_base(4,0,0)
catchIO :: IO a -> (Exception.IOException -> IO a) -> IO a
#else
catchIO :: IO a -> (Exception.Exception -> IO a) -> IO a
#endif

#else
catchIO :: IO a -> (Exception.IOException -> IO a) -> IO a
#endif
catchIO = Exception.catch

version :: Version
version = Version [0,1,0,0] []
bindir, libdir, dynlibdir, datadir, libexecdir, sysconfdir :: FilePath

bindir     = "/Users/henry/.cabal/bin"
libdir     = "/Users/henry/.cabal/lib/x86_64-osx-ghc-8.10.3/monadic-equality-0.1.0.0-inplace"
dynlibdir  = "/Users/henry/.cabal/lib/x86_64-osx-ghc-8.10.3"
datadir    = "/Users/henry/.cabal/share/x86_64-osx-ghc-8.10.3/monadic-equality-0.1.0.0"
libexecdir = "/Users/henry/.cabal/libexec/x86_64-osx-ghc-8.10.3/monadic-equality-0.1.0.0"
sysconfdir = "/Users/henry/.cabal/etc"

getBinDir, getLibDir, getDynLibDir, getDataDir, getLibexecDir, getSysconfDir :: IO FilePath
getBinDir = catchIO (getEnv "monadic_equality_bindir") (\_ -> return bindir)
getLibDir = catchIO (getEnv "monadic_equality_libdir") (\_ -> return libdir)
getDynLibDir = catchIO (getEnv "monadic_equality_dynlibdir") (\_ -> return dynlibdir)
getDataDir = catchIO (getEnv "monadic_equality_datadir") (\_ -> return datadir)
getLibexecDir = catchIO (getEnv "monadic_equality_libexecdir") (\_ -> return libexecdir)
getSysconfDir = catchIO (getEnv "monadic_equality_sysconfdir") (\_ -> return sysconfdir)

getDataFileName :: FilePath -> IO FilePath
getDataFileName name = do
  dir <- getDataDir
  return (dir ++ "/" ++ name)
