{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Common where

import Control.Exception
import Control.Monad.State
import Control.Monad.Reader
import Prelude
import System.Process
import qualified Filesystem.Path.CurrentOS as FP
import System.Exit
import Data.Set (Set)
import qualified Data.Set as S
import Data.Map (Map)
import Data.Graph
import qualified Data.Map as M
import GHC.IO.Handle

import Text.Parsec.Error

type Parser a = (String -> Either ParseError a)

type Interpreter a = ([Int] -> a -> Int)

type TypeChecker a t = (a -> Either TypeError t)

type Compiler a = (a -> String)

data ParseException = ParseException String

instance Show ParseException where
  show (ParseException e) = e

instance Exception ParseException


-- | Class for pretty printing x86
class PrettyPrint a where
  prettyPrint :: a -> String

compileToFile
  :: Parser a
  -> Compiler a
  -> String        -- ^ Program
  -> FilePath      -- ^ Output file
  -> IO ()
compileToFile p c prog fp = do
  case p prog of
    Left e -> throw (ParseException (show e))
    Right prog' -> do
      writeFile ass . c $ prog'
      (exitCode, stdOut, _) <- readProcessWithExitCode "gcc"
          ["-g", "./test/testenv/runtime.o", ass, "-g", "-O0", "-o", fp] ""
      case exitCode of
        (ExitFailure _) -> error stdOut
        ExitSuccess -> pure ()
 where
  ass = FP.encodeString $ FP.dropExtensions (FP.decodeString fp) FP.<.> "s"

runBinary :: (Show a) => FilePath -> [a] -> IO Int
runBinary fp ins = withCreateProcess process $
  \mbHIn _ _ ph -> case mbHIn of
    Just hIn -> do
     hSetBuffering hIn LineBuffering
     loop hIn ph ins
    Nothing -> error $ "runBinary: Failed to start " ++ fp
  where
   process =
     (proc fp []) { std_in = CreatePipe
                  , delegate_ctlc = True }

   loop hIn ph (i:is) = do
     mbExitCode <- getProcessExitCode ph
     case mbExitCode of
       Nothing -> do
         -- The process is probably closed so just ignore
         -- failure. Messy, I know
         catch (hPutStr hIn (show i ++ "\n"))
           (\(SomeException _) -> return ())
         loop hIn ph is
       Just x -> return $ exitCodeToInt x
   loop _ ph [] =
     exitCodeToInt <$> waitForProcess ph

exitCodeToInt :: ExitCode -> Int
exitCodeToInt ExitSuccess   = 0
exitCodeToInt (ExitFailure n) = n

mapSetToGraph :: (Ord a)
  => Map a (Set a)
  -> (Graph, Vertex -> ((), a, [a]), a -> Maybe Vertex)
mapSetToGraph m = graphFromEdges .
  map (\(k, ks) -> ((), k, ks)) . M.toList . M.map (S.toList) $ m



type FreshM a = ReaderT String (State Int) a

newtype FreshEnv a = FreshEnv { unFreshEnv :: FreshM a }
  deriving (Functor, Applicative, Monad, MonadReader String, MonadState Int)

fresh :: FreshEnv String
fresh = do
  x <- get
  prefix <- ask
  put (x+1)
  return (prefix ++ show x)

runFreshEnv :: String -> FreshEnv a -> a
runFreshEnv prefix c = flip evalState 0 $ runReaderT (unFreshEnv c) prefix
