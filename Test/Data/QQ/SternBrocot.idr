module Test.Data.QQ.SternBrocot

import Data.QQ.SternBrocot
import Data.ZZ

testSuite : List (String, Bool)
testSuite =
  [
    ("1 # 2", 1 # 2 == Pos [L]),
    ("0 # 15", 0 # 15 == Zero),
    ("-12 # 13", -12 # 13 == Neg [L, R, R, R, R, R, R, R, R, R, R, R]),

    ("1 # 2 == 2 # 4", 1 # 2 == 2 # 4),
    ("1 # 2 /= 6 # 8", 1 # 2 /= 6 # 8),
    ("0 # 1 == 0 # 10", 0 # 1 == 0 # 10),
    ("0 # 1 /= 1 # 2", 0 # 1 /= 1 # 2),
    ("-14 # 4 == -7 # 2", -14 # 4 == -7 # 2),
    
    ("compare (1 # 3) (3 # 9)", compare (1 # 3) (3 # 9) == EQ),
    ("compare (4 # 9) (1 # 2)", compare (4 # 9) (1 # 2) == LT),
    ("compare (4 # 9) (0 # 2)", compare (4 # 9) (0 # 2) == GT),
    ("compare (-1 # 2) (112 # 225)", compare (-1 # 2) (112 # 225) == LT)
  ]

total
processTest : (String, Bool) -> String
processTest (name, outcome) = case outcome of
  False => "❌ " ++ name
  True => "✓ " ++ name

export
testQQ : IO ()
testQQ = do
  for (map processTest testSuite) putStrLn
  x <- pure True
  case any (not . snd) testSuite of
    True => putStrLn "Failure"
    False => putStrLn "Success"

