{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Common where

import Control.Exception
import Control.Monad.State
import Control.Monad.Reader
import Data.Set (Set)
import qualified Data.Set as S
import Data.Map (Map)
import Data.Graph
import qualified Data.Map as M
import Data.Tuple
import qualified Filesystem.Path.CurrentOS as FP
import GHC.IO.Handle
import Prelude
import System.Exit
import System.Process
import Text.Parsec.Error

{-=--- Some Useful Types -----}

type Parser a = (String -> Either ParseError a)

type Interpreter a = ([Int] -> a -> Int)

type InterpreterIO a b = ([Int] -> a -> IO b)

type TypeChecker a t = (a -> Either TypeError t)

type Compiler a = (a -> String)

newtype ParseException = ParseException String

instance Show ParseException where
  show (ParseException e) = e

instance Exception ParseException

-- | Class for pretty printing x86
class PrettyPrint a where
  prettyPrint :: a -> String

{----- Some useful utility functions -----}

compileToFile
  :: Parser a
  -> Compiler a
  -> String        -- ^ Program
  -> FilePath      -- ^ Output file
  -> IO ()
compileToFile p c prog fp =
  case p prog of
    Left e -> throw (ParseException (show e))
    Right prog' -> do
      writeFile ass . c $ prog'
      (exitCode, _, stdErr) <- readProcessWithExitCode "gcc"
          ["-g", "./test/testenv/runtime.o", ass, "-g", "-O0", "-o", fp] ""
      case exitCode of
        (ExitFailure _) -> error stdErr
        ExitSuccess -> pure ()
 where
  ass = FP.encodeString $ FP.dropExtensions (FP.decodeString fp) FP.<.> "s"

runBinary :: (Show a)
          => FilePath
          -> [a]      -- input
          -> IO Int
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
         -- If an error gets thrown, it's probably because
         -- the process exited after checking exit code, but before
         -- we send the next input. So we'll ignore the failure.
         catch (hPutStr hIn (show i ++ "\n"))
           (\(SomeException _) -> return ())
         loop hIn ph is
       Just x -> return $ exitCodeToInt x
   loop _ ph [] =
     exitCodeToInt <$> waitForProcess ph

exitCodeToInt :: ExitCode -> Int
exitCodeToInt ExitSuccess   = 0
exitCodeToInt (ExitFailure n) = n

-- | Generate a Data.Graph and maps to/from vertex from adjacency sets
mapSetToGraph :: (Ord a)
  => Map a (Set a)
  -> (Graph, Map Vertex a, Map a Vertex)
mapSetToGraph m = (graph, vertexMap, keyMap)

 where
  keyMap =
    M.fromList
    . map swap
    . M.toList
    $ vertexMap

  vertexMap =
    M.fromList
    .map (\v -> (\(_, k, _) -> (v, k)) (nodeFromVertex v))
    . vertices
    $ graph

  (graph, nodeFromVertex, _) =
    graphFromEdges
    . map (\(k, ks) -> ((), k, ks))
    . M.toList
    . M.map S.toList
    $ m

{---- A monad for generating unique variable names -----}

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

{----- Registers -----}

data Register = Rsp | Rbp | Rax | Rbx | Rcx | Rdx | Rsi | Rdi
              | R8 | R9 | R10 | R11 | R12 | R13 | R14 | R15
              | Al
  deriving (Show, Ord, Eq)

callerSaved :: [Register]
callerSaved = [ Rax, Rdx, Rcx, Rsi, Rdi, R8, R9, R10, R11 ]

instance PrettyPrint Register where
  prettyPrint Rsp = "%rsp"
  prettyPrint Rbp = "%rbp"
  prettyPrint Rax = "%rax"
  prettyPrint Rbx = "%rbx"
  prettyPrint Rcx = "%rcx"
  prettyPrint Rdx = "%rdx"
  prettyPrint Rsi = "%rsi"
  prettyPrint Rdi = "%rdi"
  prettyPrint R8  = "%r8"
  prettyPrint R9  = "%r9"
  prettyPrint R10 = "%r10"
  prettyPrint R11 = "%r11"
  prettyPrint R12 = "%r12"
  prettyPrint R13 = "%r13"
  prettyPrint R14 = "%r14"
  prettyPrint R15 = "%r15"
  prettyPrint Al  = "%al"
