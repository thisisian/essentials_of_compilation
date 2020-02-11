{-# OPTIONS_GHC -fno-warn-missing-signatures #-}

import Control.Exception
import Data.Either
import System.Directory
import System.Exit
import System.IO.Temp
import System.Process
import System.Random
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.Ingredients.ConsoleReporter
import Test.Tasty.QuickCheck
import Test.QuickCheck.Monadic

import Common
import qualified R0
import qualified R1
import qualified R2
import qualified Chapter2 as Ch2
import qualified Chapter3 as Ch3
import qualified Chapter4 as Ch4

main :: IO ()
main = defaultMain
  $ localOption (Quiet True)
  $ testGroup "Essentials Of Compilation" $
  --[ch1Tests, ch2Tests, ch3Tests, ch4Tests]
  [ch4Tests]

{----- Chapter 1 -----}

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

ch2InterpTest :: String -> [Int] -> Int -> TestTree
ch2InterpTest prog ins expected =
  interpTest R1.parse dummyTypeChecker R1.interp prog ins expected

ch2Tests = testGroup "Chapter 2" $
  [ ch2InterpTest "(let ([x (+ 12 20)]) (+ 10 x))" [] 42
  , ch2InterpTest "(let ([x 32]) (+ (let ([x 10]) x) x))" [] 42
  , ch2InterpTest "(let ([x (+ 12 20)]) (+ 10 x))" [] 42
  , ch2InterpTest
      "(let ([x (read)]) (let ([y (read)]) (+ x (- y))))" [52, 10] 42
  ] ++
  map ch2CompileTest ch2TestExprs

ch2TestExprs :: [String]
ch2TestExprs =
  [ "(+ 8 2)"
  , "(+ (read) 2)"
  , "(+ (read) (read))"
  , "(read)"
  , "(let ([x (let ([x 5]) x)]) x)"
  , "(+ (+ (read) (- 4)) (read))"
  , "(+ (+ (+ (read) (- 9)) (- 4)) (- 2))"
  , "(let ([x (+ 12 20)]) (+ 10 x))"
  , "(let ([x 32]) (+ (let ([x 10]) x) x))"
  , "(let ([x (+ 12 20)]) (+ 10 x))"
  , "(let ([x 32]) (+ (let ([x 10]) x) x))"
  , "(let ([x1 32]) (+ (let ([x2 10]) x2) x1))"
  , "(let ([x (read)]) (let ([y (read)]) (+ x (- y))))"
  , "(let ([x 32]) (+ (let ([x 10]) x) x))"
  , "(let ([ x (let ([ x (read)]) (+ x (read))) ]) (+ (let ([ x 15 ]) (+ (- x) 100)) (+ x 105)))"
  , "(+ (let ([ x (read)]) (+ x  (let ([ x (read)]) (+ x (let ([ x (read)]) (+ x (let ([ x (read)]) (+ x (let ([ x (read)]) (+ x (let ([ x (read)]) (+ x (let ([ x (read)]) (+ x (let ([ x (read)]) (+ x (let ([ x (read)]) (+ x (let ([ x (read)]) (+ x (let ([ x (read)]) (+ x (read))))))))))))))))))))))) (let ([ x (read)]) (+ x (let ([ x (read)]) (+ x (let ([ x (read)]) (+ x (let ([ x (read)]) (+ x (let ([ x (read)]) (+ x (let ([ x (read)]) (+ x (let ([ x (read)]) (+ x (let ([ x (read)]) (+ x (let ([ x (read)]) (+ x (read))))))))))))))))))))"
  , "(+ (let ([y (read)]) y) (let ([y (read)]) y))"
  , "(let ([x (read)]) (+ (let ([y (read)]) (+ x (- y))) x))"
  , "(+ (let ([ x 1 ]) (+ x 2)) 3)"
  , "(let ([x (read)]) (+ (let ([y (read)]) (+ x y)) (let ([y (read)]) (+ y x))))"
  , "3"
  , "(- (let ([x (+ 2 3)]) (- (+ x x))))"
  , "(- (read))"
  , "(let ([x 5]) (let ([x x]) (- (+ x (+ x (- (+ x x)))))))"
  , "(let ([x 5]) x)"
  , "(- 0 (+ 1 1))"
  ]

{----- Chapter 3 -----}

ch3CompileTest :: String -> TestTree
ch3CompileTest =
  compileTest R1.parse dummyTypeChecker R1.interp Ch3.compile

ch3Tests = testGroup "Chapter 3" $ map (ch3CompileTest) ch2TestExprs

{----- Chapter 4 Tests -----}

ch4TypeCheck = typeCheckTest R2.parse R2.typeCheck

ch4TypeCheckProp :: TestTree
ch4TypeCheckProp = testProperty "TypeCheck random programs" (property (prop_ShouldTypeCheck R2.typeCheck))

ch4InterpCompilerEqProp :: TestTree
ch4InterpCompilerEqProp = testProperty "Check compiler/interpreter equality on random progresms" $
 withMaxSuccess 10000 (mapSize (\x -> 2) (property (prop_InterpCompilerEquality R2.interp Ch4.compile)))

ch4TypeCheckFail = typeCheckFailTest R2.parse R2.typeCheck

ch4InterpTest = interpTest R2.parse R2.typeCheck R2.interp

ch4CompileTest :: String -> TestTree
ch4CompileTest =
  compileTest R2.parse R2.typeCheck R2.interp Ch4.compile

ch4Tests :: TestTree
ch4Tests = testGroup "Chapter 4" $
  --[ parseTest R2.parse (ch4TestExprs !! 1)
  --, parseTest R2.parse (ch4TestExprs !! 2)
  --, parseTest R2.parse (ch4TestExprs !! 3)
  --, parseTest R2.parse (ch4TestExprs !! 4)
  --, ch4TypeCheckFail "(if (cmp eq? 2 2) (cmp eq? 4 4) (- 3))"
  --, ch4TypeCheckFail "(if (cmp eq? 2 2) (- 9 3) #f)"
  --, ch4TypeCheckFail "(if (cmp eq? 2 #f) #t #t)"
  --, ch4TypeCheckFail "(if (cmp eq? 2 #f) #t #t)"
  --, ch4TypeCheckFail "(cmp <= #t 3)"
  --, ch4TypeCheckFail "(let ([x 2]) y)"
  --, ch4TypeCheckFail "(- #t)"
  --, ch4TypeCheckFail "(+ #t 2)"
  --, ch4TypeCheckFail "(or 2 #f)"
  --, ch4TypeCheck (ch4TestExprs !! 1) R2.TBool
  --, ch4TypeCheck (ch4TestExprs !! 2) R2.TBool
  --, ch4TypeCheck (ch4TestExprs !! 3) R2.TBool
  --, ch4TypeCheck (ch4TestExprs !! 4) R2.TBool
  --, ch4TypeCheck (ch4TestExprs !! 5) R2.TBool
  --, ch4InterpTest (ch4TestExprs !! 1) [] 0
  --, ch4InterpTest (ch4TestExprs !! 2) [] 1
  --, ch4InterpTest (ch4TestExprs !! 3) [] 0
  --, ch4InterpTest (ch4TestExprs !! 4) [5] 1
  --, ch4InterpTest (ch4TestExprs !! 5) [2,3] 0
  --, ch4InterpTest (ch4TestExprs !! 6) [50] (-50)
  --, ch4InterpTest (ch4TestExprs !! 7) [] 10
  --, ch4InterpTest "(cmp > (read) (read))" [0, 100] 0
  --] ++
  map ch4CompileTest ch2TestExprs ++
  map ch4CompileTest ch4TestExprs ++
  -- [ ch4TypeCheck2 ]
  --[ch4InterpCompilerEqProp] ++
  []

ch4TestExprs =
  [ "(cmp <= (+ 2 3) (- 9 3))"
  , "(if (and #t #f) (or #t #f) #f)"
  , "(if (and #t #f) #f (cmp <= 2 3))"
  , "(if (not #f) (cmp > 2 3) #f)"
  , "(let ([x (read)]) (if (cmp <= x 3) (and #t #f) (or #t #f)))"
  , "(let ([x (read)]) (let ([y (read)]) (cmp >= x y)))"
  , "(- (let ([x (read)]) (if (and #t #t) (if (or #f #f) 90 (if (not #f) (if (cmp eq? x 100) 90 (if (cmp < x 100) x 90)) 90)) 90)))"
  , "(if (not (not (and #f #t))) 90 10)"
  , "(let ([x (read)]) (if (cmp <= x 3) #t #f))"
  , "(and #f #t)"
  , "(or #f #t)"
  , "(and #t #f)"
  , "#t"
  , "#f"
  , "(let ([r (read)]) (let ([x #t]) (let ([y (- 2)]) (let ([z (+ 5 9)]) (let ([m y]) (let ([n (not (cmp >= r z))]) (if (cmp eq? r z) (cmp eq? r y) (if (cmp < r m) x #f))))))))"
  , "(let ([x (- 0)]) (let ([y x]) 0))"
  , "(let ([rco23 (read)]) rco23)"
  , "(if (let ([j (let ([h -2]) #f)]) j) #f #f)"
  , "(- (if #f (read) 0))"
  , "(let ([n (and #t (cmp eq? 11 (let ([f -5]) f)))]) -4)"
  , "(let ([x 5]) (if (not #f) x 100))"
  , "(let ([x 5]) (if (or #f #f) 90 x))"
  , "(if #f (let ([d (if #f 0 0)]) d) 0)"
  , "(cmp > (read) (read))"
  ]

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
compileTest p tc i c prog = testCase ("Compile -- " ++ prog) $ do
  prog' <- parseAssert p prog
  typeCheckAssert tc prog'
  input <- randomInput
  let expected =  i input prog' `mod` 256
  actual <- compileAndRun c input prog'
  assertEqual ""
    expected
    actual

interpTest
  :: Parser a
  -> TypeChecker a b
  -> Interpreter a
  -> String -> [Int] -> Int -> TestTree
interpTest p tc i prog ins expected = testCase ("Interp -- " ++ prog) $ do
  prog' <- parseAssert p prog
  typeCheckAssert tc prog'
  assertEqual "" expected (i ins prog')

testCompileStep
  :: Parser a
  -> TypeChecker a b
  -> (a -> c)
  -> (a -> c)
  -> Interpreter c
  -> String  -- Description
  -> String
  -> TestTree
testCompileStep p tc refStps testStps i desc prog = testCase (desc ++ " -- " ++ prog) $ do
  prog' <- parseAssert p prog
  typeCheckAssert tc prog'
  let ref = refStps prog'
      test = testStps prog'
  input <- randomInput
  assertEqual ""
    (i input ref)
    (i input test)

typeCheckTest :: (Show b, Eq b)
  => Parser a -> TypeChecker a b -> String -> b -> TestTree
typeCheckTest p tc prog expected = testCase ("TypeCheck -- " ++ prog) $ do
  prog' <- parseAssert p prog
  case tc prog' of
    Left e' -> assertFailure (show e')
    Right ty -> assertEqual "" expected ty

typeCheckFailTest :: (Show b)
  => Parser a -> TypeChecker a b -> String -> TestTree
typeCheckFailTest p tc prog = testCase ("TypeCheck Failure -- " ++ prog) $ do
  prog' <- parseAssert p prog
  case tc prog' of
    Left _ -> assertBool "" True
    Right ty -> assertFailure ("Expected failure, but got " ++ show ty)

{----- Properties -----}

prop_ShouldTypeCheck :: (Arbitrary a)
                     => TypeChecker a b
                     -> a
                     -> Bool
prop_ShouldTypeCheck tc prog = isRight $ tc prog

prop_InterpCompilerEquality :: (Arbitrary a)
                            => Interpreter a
                            -> Compiler a
                            -> a
                            -> Property
prop_InterpCompilerEquality i c prog = monadicIO $ do
 ins <- run (randomInput)
 compileRes <- run (compileAndRun c ins prog)
 let interpRes = i ins prog `mod` 256
 return (interpRes == compileRes)


{----- Utilities -----}

randomInput :: IO [Int]
randomInput = do
  gen <- getStdGen
  return $ randoms gen

dummyTypeChecker :: TypeChecker a ()
dummyTypeChecker _ = Right ()

parseAssert :: Parser a -> String -> IO a
parseAssert p prog =
  case p prog of
    Left e -> assertFailure (show e)
    Right prog' -> return prog'

typeCheckAssert :: TypeChecker a b -> a -> IO ()
typeCheckAssert tc prog =
  case tc prog of
    Left e -> assertFailure (show e)
    Right _ -> return ()

compileAndRun :: Compiler a -> [Int] -> a -> IO Int
compileAndRun c ins prog = do
  withEmptyTempFile "eocAsm.s" $ \asm ->
    withEmptyTempFile "eocBin.out" $ \bin -> do
      writeFile asm (c prog)
      (exitCode, stdOut, _) <- readProcessWithExitCode "gcc"
        ["-g", "./test/testenv/runtime.o", asm, "-g", "-O0", "-o", bin] ""
      case exitCode of
        (ExitFailure _) -> error $ stdOut
        ExitSuccess -> runBinary bin ins

withEmptyTempFile :: String -> (FilePath -> IO b) -> IO b
withEmptyTempFile fp f =
  bracket
    (emptySystemTempFile fp)
    removeFile
    f
