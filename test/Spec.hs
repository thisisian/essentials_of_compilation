import Test.HUnit
import Text.Parsec hiding (parseTest)
import Common
import System.Directory
import qualified R0
import qualified R1
import qualified Chapter2 as Ch2

main :: IO ()
main = runTestTT r1Tests >> pure ()

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

compileTest :: (Show b)
  => (String -> a)     -- ^ Parser
  -> ([b] -> a -> Int) -- ^ Interpreter
  -> (a -> String)     -- ^ Compiler
  -> [b]               -- ^ Inputs
  -> String            -- ^ Program
  -> Test
compileTest p i c input prog = TestLabel ("") $ TestCase $ do
  let expected =  (i input (p prog)) `mod` 256
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
 -- , interpTest R0.doParse R0.interp "(+ 8 2)" 10
 -- , interpTest R0.doParse R0.interp "(+ (- 1) (+ 2 (- 3)))" (-2)
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

ch2CompileTest :: [Int] -> String -> Test
ch2CompileTest input =
  compileTest R1.doParse R1.interp Ch2.compile input


r1Tests = TestLabel "R1". TestList $
  [ parseTest R1.doParse "(+ 8 2)"
  , parseTest R1.doParse "(+ (+ (read) (- 4)) (read))"
  , parseTest R1.doParse "(+ (+ (+ (read) (- 9)) (- 4)) (- 2))"
  , parseTest R1.doParse "(let ([x (+ 12 20)]) (+ 10 x))"
  , parseTest R1.doParse "(let ([x 32]) (+ (let ([x 10]) x) x))"
  , interpTest R1.doParse (R1.interp []) "(let ([x (+ 12 20)]) (+ 10 x))" 42
  , interpTest R1.doParse (R1.interp []) "(let ([x 32]) (+ (let ([x 10]) x) x))" 42
  , interpTest R1.doParse (R1.interp []) "(let ([x1 32]) (+ (let ([x2 10]) x2) x1))" 42
  , interpTest R1.doParse (R1.interp [52, 10]) "(let ([x (read)]) (let ([y (read)]) (+ x (- y))))" 42
  , testR1Uniquify testR1Expr1
  , testR1Uniquify testR1Expr2
  , testR1Uniquify testR1Expr3
  , testR1Uniquify testR1Expr4
  , testR1Uniquify testR1Expr5
  , testR1RCO testR1Expr1
  , testR1RCO testR1Expr2
  , testR1RCO testR1Expr3
  , testR1RCO testR1Expr4
  , testR1RCO testR1Expr5
  , testR1RCO testR1Expr6
  , testR1RCO testR1Expr7
  , ch2CompileTest [] testR1ExprS1
  , ch2CompileTest [10] testR1ExprS2
  , ch2CompileTest [5,10] testR1ExprS3
  , ch2CompileTest [5] testR1ExprS4
  , ch2CompileTest [] testR1Expr1
  , ch2CompileTest [6, 2] testR1ExprS5
  , ch2CompileTest [3,6,2,3,4,6,2,1,7,4,3,2,4,5,7,2,1,5,6,7,3,2,1] testR1Expr3
  , ch2CompileTest [7,3] testR1Expr5
  , ch2CompileTest [] testR1Expr6
  , ch2CompileTest [7,3,2] testR1Expr7
  ]

testR1ExprS1 = "(+ 8 2)"
testR1ExprS2 = "(+ (read) 2)"
testR1ExprS3 = "(+ (read) (read))"
testR1ExprS4 = "(read)"
testR1ExprS5 = "(let ([ x (let ([ x 5 ]) x) ]) x)"

testR1Expr1 = "(let ([x 32]) (+ (let ([x 10]) x) x))"
testR1Expr2 = "(let ([ x (let ([ x (read)]) (+ x (read))) ]) (+ (let ([ x 15 ]) (+ (- x) 100)) (+ x 105)))"
testR1Expr3 = "(+ (let ([ x (read)]) (+ x  (let ([ x (read)]) (+ x (let ([ x (read)]) (+ x (let ([ x (read)]) (+ x (let ([ x (read)]) (+ x (let ([ x (read)]) (+ x (let ([ x (read)]) (+ x (let ([ x (read)]) (+ x (let ([ x (read)]) (+ x (let ([ x (read)]) (+ x (let ([ x (read)]) (+ x (read))))))))))))))))))))))) (let ([ x (read)]) (+ x (let ([ x (read)]) (+ x (let ([ x (read)]) (+ x (let ([ x (read)]) (+ x (let ([ x (read)]) (+ x (let ([ x (read)]) (+ x (let ([ x (read)]) (+ x (let ([ x (read)]) (+ x (let ([ x (read)]) (+ x (read))))))))))))))))))))"
testR1Expr4 =  "(+ (let ([y (read)]) y) (let ([y (read)]) y))"
testR1Expr5 = "(let ([x (read)]) (+ (let ([y (read)]) (+ x (- y))) x))"
testR1Expr6 = "(+ (let ([ x 1 ]) (+ x 2)) 3)"
testR1Expr7 =  "(let ([x (read)]) (+ (let ([y (read)]) (+ x y)) (let ([y (read)]) (+ y x))))"
