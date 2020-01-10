import Test.HUnit
import Text.Parsec hiding (parseTest)
import qualified R0

main :: IO ()
main = runTestTT r0Tests >> pure ()

fromRight :: Either a b -> b
fromRight (Right b) = b
fromRight _ = undefined

parseTest :: (Show a) => (Parsec String () a) -> String -> Test
parseTest p input = TestCase $
  assertEqual ("Parse Test: " ++ input)
    input
    (show . fromRight $ parse p "" input)

interpIOTest :: (Eq b, Show b)
  => (Parsec String () a) -> (a -> IO b) -> String -> b -> Test
interpIOTest p i input expected = TestCase $ do
  actual <- i (fromRight (parse p "" input))
  assertEqual ("Interp Test: " ++ input) expected actual



-- R0 --

exercise1Test :: String -> String -> Test
exercise1Test input expected = TestCase $
  assertEqual ("Exercise 1: " ++ input)
    expected
    (show . R0.pe2 . R0.doParse $ input)

r0Tests :: Test
r0Tests = TestLabel "R0" . TestList $
  [ parseTest R0.pProgram "(+ 8 2)"
  , parseTest R0.pProgram "(+ (+ (read) (- 4)) (read))"
  , parseTest R0.pProgram "(+ (+ (+ (read) (- 9)) (- 4)) (- 2))"
  , interpIOTest R0.pProgram R0.interp "(+ 8 2)" 10
  , interpIOTest R0.pProgram R0.interp "(+ (- 1) (+ 2 (- 3)))" (-2)
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
