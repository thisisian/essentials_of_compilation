{-# OPTIONS_GHC -fno-warn-missing-signatures #-}

import Test.HUnit
import Text.Parsec hiding (parseTest)
import Common
import System.Directory
import System.Random
import qualified R0
import qualified R1
import qualified Chapter2 as Ch2
import qualified Chapter3 as Ch3

main :: IO ()
main = runTestTT ch3Tests >> pure ()

parseTest :: (Show a) => (String -> a) -> String -> Test
parseTest p input = TestCase $
  assertEqual ("Parse Test: " ++ input)
    input
    (show . p $ input)

interpTest :: (Eq b, Show b)
  => (String -> a) -> (a -> b) -> String -> b -> Test
interpTest p i input expected = TestCase $
  let actual = i . p $ input
  in assertEqual ("Interp Test: " ++ input) expected actual

equalInterpTest :: (Eq b, Show b)
  => (String -> a) -> (a -> b) -> (a -> b) -> String -> Test
equalInterpTest p iRef iTest input = TestLabel ("EqualInterp Test: " ++ input) $ TestCase $
  let actual = iRef (p input)
      expected = iTest (p input)
  in assertEqual ("Equal Test: " ++ input) expected actual

compileTest :: (Random b, Show b)
  => (String -> a)     -- ^ Parser
  -> ([b] -> a -> Int) -- ^ Interpreter
  -> (a -> String)     -- ^ Compiler
  -> String            -- ^ Program
  -> Test
compileTest p i c prog = TestLabel "" $ TestCase $ do
  gen <- getStdGen
  let input = randoms gen
      expected =  i input (p prog) `mod` 256
  compileToFile p c prog "./test/testenv/test"
  actual <- runBinary "./test/testenv/test" input
  removeFile "./test/testenv/test.s"
  removeFile "./test/testenv/test"
  assertEqual ("Compile Test: " ++ prog)
    expected
    actual


-- R0 --

exercise1Test :: String -> String -> Test
exercise1Test input expected = TestCase $
  assertEqual ("Exercise 1: " ++ input)
    expected
    (show . R0.pe . R0.doParse $ input)

r0Tests :: Test
r0Tests = TestLabel "R0" . TestList $
  [ parseTest R0.doParse "(+ 8 2)"
  , parseTest R0.doParse "(+ (+ (read) (- 4)) (read))"
  , parseTest R0.doParse "(+ (+ (+ (read) (- 9)) (- 4)) (- 2))"
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


-- R1 --

testR1Uniquify :: String -> Test
testR1Uniquify =
  equalInterpTest R1.doParse (R1.interp [0,5..]) (R1.interp [0,5..] . Ch2.uniquify)

testR1RCO :: String -> Test
testR1RCO =
  equalInterpTest R1.doParse (R1.interp [0,5..]) (R1.interp [0,5..] . Ch2.rco . Ch2.uniquify )

ch2CompileTest :: String -> Test
ch2CompileTest =
  compileTest R1.doParse R1.interp Ch2.compile

ch2Tests = TestLabel "Ch1". TestList $
  [ interpTest R1.doParse (R1.interp []) testExpr10 42
  , interpTest R1.doParse (R1.interp []) testExpr11 42
  , interpTest R1.doParse (R1.interp []) testExpr12 42
  , interpTest R1.doParse (R1.interp [52, 10]) testExpr13 42
  , testR1Uniquify testExpr1
  , testR1Uniquify testExpr2
  , testR1Uniquify testExpr3
  , testR1Uniquify testExpr4
  , testR1Uniquify testExpr5
  , testR1RCO testExpr1
  , testR1RCO testExpr2
  , testR1RCO testExpr3
  , testR1RCO testExpr4
  , testR1RCO testExpr5
  , testR1RCO testExpr6
  , testR1RCO testExpr7
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

ch3CompileTest :: String -> Test
ch3CompileTest =
  compileTest R1.doParse R1.interp Ch3.compile

ch3Tests = TestLabel "Ch2". TestList $
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
