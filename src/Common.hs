module Common where

import Control.Exception
import Prelude
import System.Process
import qualified Filesystem.Path.CurrentOS as FP
import System.Exit
import GHC.IO.Handle

class PrettyPrint a where
  prettyPrint :: a -> String

compileToFile
  :: (String -> a) -- ^ Parser
  -> (a -> String) -- ^ Compiler
  -> String        -- ^ Program
  -> FilePath      -- ^ Output file
  -> IO ()
compileToFile p c prog fp = do
  writeFile ass . c . p $ prog
  (exitCode, stdOut, _) <- readProcessWithExitCode "gcc"
      ["-g", "./test/testenv/runtime.o", ass, "-g", "-O0", "-o", fp] ""
  case exitCode of
    (ExitFailure _) -> error stdOut
    ExitSuccess ->
      pure ()
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
