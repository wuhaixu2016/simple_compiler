-- In your package.yaml, add the following:
--      dependencies:
--      OTHER DEPENDENCIES YOU HAVE
--      - tasty
--      - tasty-hunit
import           Test.Tasty
import           Test.Tasty.HUnit

-- import your AST
import           AST                            ( Program
                                                , Type
                                                , Result
                                                )
-- import your EVALUATE TYPE function
import           EvalType                       ( evalType )
-- import your EVALUATE VALUE function
import           EvalValue                      ( evalValue )

import           Util
import           ExamplesCore
import           ExamplesADT

mkTestCase :: Example -> [TestTree]
mkTestCase (Example n p Nothing r) =
    [testCase (n ++ " [ill-typed]") $ evalType p @?= Nothing]
mkTestCase (Example n p (Just t) r) =
    [ testCase (n ++ " [well-typed]") $ evalType p @?= Just t
    , testCase (n ++ " [value]") $ evalValue p @?= r
    ]

mkTestSuite :: String -> [Example] -> TestTree
mkTestSuite n es = testGroup n $ es >>= mkTestCase

testTasks :: [TestTree]
testTasks =
    [ mkTestSuite "simple"  simple
    , mkTestSuite "complex" complex
    , mkTestSuite "adt"     adt
    ]

main :: IO ()
main = defaultMain $ testGroup "" testTasks
