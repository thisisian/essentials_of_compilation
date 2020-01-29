{-# OPTIONS_GHC -fno-warn-missing-signatures #-}

import Control.Exception
import System.Directory
import System.Exit
import System.IO.Temp
import System.Process
import System.Random
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.Ingredients.ConsoleReporter

import Common
import qualified R0
import qualified R1
import qualified R2
import qualified Chapter2 as Ch2
import qualified Chapter3 as Ch3

main :: IO ()
main = defaultMain
  $ localOption (Quiet True)
  $ testGroup "Essentials Of Compilation" $
  [ch4Tests]

ingredients = defaultIngredients


{----- Chapter 1 Tests -----}

exercise1Test :: String -> String -> TestTree
exercise1Test input expected = testCase "Exercise 1" $
  assertEqual ("Exercise 1: " ++ input)
    expected
    (show . R0.pe . R0.doParse $ input)

ch1Tests :: TestTree
ch1Tests = testGroup "Chapter 1" $
  [ parseTest R0.parse "(+ 8 2)"
  , parseTest R0.parse "(+ (+ (read) (- 4)) (read))"
  , parseTest R0.parse "(+ (+ (+ (read) (- 9)) (- 4)) (- 2))"
  , exercise1Test "(+ 1 (+ (read) 1))" "(+ 2 (read))"
  , exercise1Test
      "(+ (read) 2)"
      "(+ 2 (read))"
  , exercise1Test
      "(+ (read) 2)"
      "(+ 2 (read))"
  , exercise1Test
      "(+ (+ 2 3) (+ (read) 2))"
      "(+ 7 (read))"
  , exercise1Test
      "(+ (read) (+ 2 (read)))"
      "(+ 2 (+ (read) (read)))"
  , exercise1Test
      "(+ (+ (read) 2) (+ (read) 3))"
      "(+ 5 (+ (read) (read)))"
  , exercise1Test
      "(+ (+ 5 (read)) (read))"
      "(+ 5 (+ (read) (read)))"
  , exercise1Test
      "(+ 1 (+ (+ (- 2) (read)) (+ 1 (read))))"
      "(+ (read) (read))"
  , exercise1Test
      "(- (+ (read) (- (+ (read) (read)))))"
      "(+ (- (read)) (+ (read) (read)))"
  , exercise1Test
      "(- (+ (read) (+ 5 (+ (read) (- 2)))))"
      "(+ -3 (+ (- (read)) (- (read))))"
  , exercise1Test
      "(- (- (+ (read) 1)))"
      "(+ 1 (read))"
  ]


{----- Chapter 2 -----}

ch2CompileTest :: String -> TestTree
ch2CompileTest =
  compileTest R1.parse dummyTypeChecker R1.interp Ch2.compile

ch2Tests = testGroup "Chapter 1" $
  [ interpTest R1.parse dummyTypeChecker R1.interp testExpr10 [] 42
  , interpTest R1.parse dummyTypeChecker R1.interp testExpr11 [] 42
  , interpTest R1.parse dummyTypeChecker R1.interp testExpr12 [] 42
  , interpTest R1.parse dummyTypeChecker R1.interp testExpr13 [52, 10] 42
  , ch2CompileTest testExpr1
  , ch2CompileTest testExpr2
  , ch2CompileTest testExpr3
  , ch2CompileTest testExpr4
  , ch2CompileTest testExpr5
  , ch2CompileTest testExpr6
  , ch2CompileTest testExpr7
  , ch2CompileTest testExpr8
  , ch2CompileTest testExpr9
  , ch2CompileTest testExpr10
  , ch2CompileTest testExpr11
  , ch2CompileTest testExpr12
  , ch2CompileTest testExpr13
  , ch2CompileTest testExpr14
  , ch2CompileTest testExpr15
  , ch2CompileTest testExpr16
  , ch2CompileTest testExpr17
  , ch2CompileTest testExpr18
  , ch2CompileTest testExpr19
  , ch2CompileTest testExpr20
  , ch2CompileTest testExpr21
  , ch2CompileTest testExpr22
  , ch2CompileTest testExpr23
  , ch2CompileTest testExpr24
  , ch2CompileTest testExpr25
  ]

ch3CompileTest :: String -> TestTree
ch3CompileTest =
  compileTest R1.parse dummyTypeChecker R1.interp Ch3.compile

ch3Tests = testGroup "Chapter 2" $
  [ ch3CompileTest testExpr1
  , ch3CompileTest testExpr2
  , ch3CompileTest testExpr3
  , ch3CompileTest testExpr4
  , ch3CompileTest testExpr5
  , ch3CompileTest testExpr6
  , ch3CompileTest testExpr7
  , ch3CompileTest testExpr8
  , ch3CompileTest testExpr9
  , ch3CompileTest testExpr10
  , ch3CompileTest testExpr11
  , ch3CompileTest testExpr12
  , ch3CompileTest testExpr13
  , ch3CompileTest testExpr14
  , ch3CompileTest testExpr15
  , ch3CompileTest testExpr16
  , ch3CompileTest testExpr17
  , ch3CompileTest testExpr18
  , ch3CompileTest testExpr19
  , ch3CompileTest testExpr20
  , ch3CompileTest testExpr21
  , ch3CompileTest testExpr22
  , ch3CompileTest testExpr23
  , ch3CompileTest testExpr24
  ]

testExpr1 = "(+ 8 2)"
testExpr2 = "(+ (read) 2)"
testExpr3 = "(+ (read) (read))"
testExpr4 = "(read)"
testExpr5 = "(let ([x (let ([x 5]) x)]) x)"
testExpr6 = "(+ (+ (read) (- 4)) (read))"
testExpr7 = "(+ (+ (+ (read) (- 9)) (- 4)) (- 2))"
testExpr8 = "(let ([x (+ 12 20)]) (+ 10 x))"
testExpr9 = "(let ([x 32]) (+ (let ([x 10]) x) x))"
testExpr10 = "(let ([x (+ 12 20)]) (+ 10 x))"
testExpr11 = "(let ([x 32]) (+ (let ([x 10]) x) x))"
testExpr12 = "(let ([x1 32]) (+ (let ([x2 10]) x2) x1))"
testExpr13 = "(let ([x (read)]) (let ([y (read)]) (+ x (- y))))"
testExpr14 = "(let ([x 32]) (+ (let ([x 10]) x) x))"
testExpr15 = "(let ([ x (let ([ x (read)]) (+ x (read))) ]) (+ (let ([ x 15 ]) (+ (- x) 100)) (+ x 105)))"
testExpr16 = "(+ (let ([ x (read)]) (+ x  (let ([ x (read)]) (+ x (let ([ x (read)]) (+ x (let ([ x (read)]) (+ x (let ([ x (read)]) (+ x (let ([ x (read)]) (+ x (let ([ x (read)]) (+ x (let ([ x (read)]) (+ x (let ([ x (read)]) (+ x (let ([ x (read)]) (+ x (let ([ x (read)]) (+ x (read))))))))))))))))))))))) (let ([ x (read)]) (+ x (let ([ x (read)]) (+ x (let ([ x (read)]) (+ x (let ([ x (read)]) (+ x (let ([ x (read)]) (+ x (let ([ x (read)]) (+ x (let ([ x (read)]) (+ x (let ([ x (read)]) (+ x (let ([ x (read)]) (+ x (read))))))))))))))))))))"
testExpr17 =  "(+ (let ([y (read)]) y) (let ([y (read)]) y))"
testExpr18 = "(let ([x (read)]) (+ (let ([y (read)]) (+ x (- y))) x))"
testExpr19 = "(+ (let ([ x 1 ]) (+ x 2)) 3)"
testExpr20 =  "(let ([x (read)]) (+ (let ([y (read)]) (+ x y)) (let ([y (read)]) (+ y x))))"
testExpr21 = "3"
testExpr22 = "(- (let ([x (+ 2 3)]) (- (+ x x))))"
testExpr23 = "(- (read))"
testExpr24 = "(let ([x 5]) (let ([x x]) (- (+ x (+ x (- (+ x x)))))))"
testExpr25 = "(let ([x 5]) x)"

{----- Chapter 4 Tests -----}

ch4TypeCheck = typeCheckTest R2.parse R2.typeCheck

ch4TypeCheckFail = typeCheckFailTest R2.parse R2.typeCheck

ch4InterpTest = interpTest R2.parse R2.typeCheck R2.interp

ch4Tests :: TestTree
ch4Tests = testGroup "Chapter 4" $
  [ parseTest R2.parse testExpr22
  , parseTest R2.parse testExpr26
  , parseTest R2.parse testExpr27
  , parseTest R2.parse testExpr28
  , parseTest R2.parse testExpr29
  , ch4TypeCheckFail "(if (cmp eq? 2 2) (cmp eq? 4 4) (- 3))"
  , ch4TypeCheckFail "(if (cmp eq? 2 2) (- 9 3) #f)"
  , ch4TypeCheckFail "(if (cmp eq? 2 #f) #t #t)"
  , ch4TypeCheckFail "(if (cmp eq? 2 #f) #t #t)"
  , ch4TypeCheckFail "(cmp <= #t 3)"
  , ch4TypeCheckFail "(let ([x 2]) y)"
  , ch4TypeCheckFail "(- #t)"
  , ch4TypeCheckFail "(+ #t 2)"
  , ch4TypeCheckFail "(or 2 #f)"
  , ch4TypeCheck testExpr26 R2.TBool
  , ch4TypeCheck testExpr27 R2.TBool
  , ch4TypeCheck testExpr29 R2.TBool
  , ch4TypeCheck testExpr30 R2.TBool
  , ch4TypeCheck testExpr31 R2.TBool
  , ch4InterpTest testExpr26 [] 1
  , ch4InterpTest testExpr27 [] 0
  , ch4InterpTest testExpr28 [] 1
  , ch4InterpTest testExpr29 [] 0
  , ch4InterpTest testExpr30 [5] 1
  , ch4InterpTest testExpr31 [2,3] 0
  , ch4InterpTest testExpr32 [50] (-50)
  , ch4InterpTest testExpr33 [] 10
  ]

testExpr26 = "(cmp <= (+ 2 3) (- 9 3))"
testExpr27 = "(if (and #t #f) (or #t #f) #f)"
testExpr28 = "(if (and #t #f) #f (cmp <= 2 3))"
testExpr29 = "(if (not #f) (cmp > 2 3) #f)"
testExpr30 = "(let ([x (read)]) (if (cmp <= x 3) (and #t #f) (or #t #f)))"
testExpr31 = "(let ([x (read)]) (let ([y (read)]) (cmp >= x y)))"
testExpr32 = "(- (let ([x (read)]) (if (and #t #t) (if (or #f #f) 90 (if (not #f) (if (cmp eq? x 100) 90 (if (cmp < x 100) x 90)) 90)) 90)))"
testExpr33 = "(if (not (not (and #f #t))) 90 10)"

{----- Generalized Tests -----}

parseTest :: (Show a) => Parser a -> String -> TestTree
parseTest p prog = testCase ("Parse -- " ++ prog) $
  case p prog of
    Left e -> assertFailure (show e)
    Right prog' -> assertEqual "" prog (show prog')

compileTest
  :: Parser a
  -> TypeChecker a b
  -> Interpreter a
  -> Compiler a
  -> String            -- ^ Program
  -> TestTree
compileTest p tc i c prog = testCase ("Compile -- " ++ prog) $
  case p prog of
    Left e -> assertFailure (show e)
    Right prog' -> case tc prog' of
      Left e' -> assertFailure (show e')
      Right _ -> do
        gen <- getStdGen
        let input = randoms gen
            expected =  i input prog' `mod` 256
        actual <- compileAndRun c prog' input
        assertEqual ""
          expected
          actual

interpTest
  :: Parser a
  -> TypeChecker a b
  -> Interpreter a
  -> String -> [Int] -> Int -> TestTree
interpTest p tc i prog ins expected = testCase ("Interp -- " ++ prog) $
  case p prog of
    Left e -> assertFailure (show e)
    Right prog' -> case tc prog' of
      Left e' -> assertFailure (show e')
      Right _ -> assertEqual "" expected (i ins prog')

typeCheckTest :: (Show b, Eq b)
  => Parser a -> TypeChecker a b -> String -> b -> TestTree
typeCheckTest p tc prog expected = testCase ("TypeCheck -- " ++ prog) $
  case p prog of
    Left e -> assertFailure (show e)
    Right prog' -> case tc prog' of
      Left e' -> assertFailure (show e')
      Right ty -> assertEqual "" expected ty

typeCheckFailTest :: (Show b)
  => Parser a -> TypeChecker a b -> String -> TestTree
typeCheckFailTest p tc prog = testCase ("TypeCheck Failure -- " ++ prog) $
  case p prog of
    Left e -> assertFailure (show e)
    Right prog' -> case tc prog' of
      Left _ -> assertBool "" True
      Right ty -> assertFailure ("Expected failure, but got " ++ show ty)

{----- Utilities -----}

dummyTypeChecker :: TypeChecker a ()
dummyTypeChecker a = Right ()

compileAndRun :: Compiler a -> a -> [Int] -> IO (Int)
compileAndRun c prog ins = do
  tAsm <- emptySystemTempFile "eocAsm.s"
  let tBin = tAsm ++ ".out"
  result <- finally
     (do writeFile tAsm (c prog)
         (exitCode, stdOut, _) <- readProcessWithExitCode "gcc" ["-g", "./test/testenv/runtime.o", tAsm, "-g", "-O0", "-o", tBin] ""
         case exitCode of
           (ExitFailure _) -> return $ Left stdOut
           (ExitSuccess) -> Right <$> runBinary tBin ins)
     (do return ())
  case result of
    Left e -> error $ e
    Right x -> return x
