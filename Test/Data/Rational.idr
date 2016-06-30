module Test.Data.Rational

import Data.Rational
import Data.ZZ

testSuite : List (String, Bool)
testSuite =
  [
    ("1 # 2", 1 # 2 == Pos [L]),
    ("0 # 15", 0 # 15 == Zero),
    ("-12 # 13", -12 # 13 == Neg [L, R, R, R, R, R, R, R, R, R, R, R]),

    ("cast Z == Zero", cast Z == Zero),
    ("cast S Z == Pos []", cast (S Z) == Pos []),
    ("cast 4 == 4 # 1", cast (S (S (S (S Z)))) == 4 # 1),

    ("1 # 2 == 2 # 4", 1 # 2 == 2 # 4),
    ("1 # 2 /= 6 # 8", 1 # 2 /= 6 # 8),
    ("0 # 1 == 0 # 10", 0 # 1 == 0 # 10),
    ("0 # 1 /= 1 # 2", 0 # 1 /= 1 # 2),
    ("-14 # 4 == -7 # 2", -14 # 4 == -7 # 2),
    
    ("compare (1 # 3) (3 # 9)", compare (1 # 3) (3 # 9) == EQ),
    ("compare (4 # 9) (1 # 2)", compare (4 # 9) (1 # 2) == LT),
    ("compare (4 # 9) (0 # 2)", compare (4 # 9) (0 # 2) == GT),
    ("compare (-1 # 2) (112 # 225)", compare (-1 # 2) (112 # 225) == LT),

    ("1 # 2 + 1 # 4 == 3 # 4", 1 # 2 + 1 # 4 == 3 # 4),
    ("7 # 2 + Zero == 7 # 2", 7 # 2 + Zero == 7 # 2),
    ("-3 # 9 + 1 # 4 == -1 # 12", -3 # 9 + 1 # 4 == -1 # 12),
    ("-1 # 2 + -1 # 3 == -5 # 6", -1 # 2 + -1 # 3 == -5 # 6),
    ("Zero + -1 # 2 == -1 # 2", Zero + -1 # 2 == -1 # 2),

    ("1 # 2 * Zero == Zero", 1 # 2 * Zero == Zero),
    ("Zero * (-1 # 2) == Zero", Zero * (-1 # 2) == Zero),
    ("1 # 1 * (2 # 3) == 2 # 3", 1 # 1 * (2 # 3) == 2 # 3),
    ("-9 # 5 * (3 # 2) == -27 # 10", -9 # 5 * (3 # 2) == -27 # 10),
    ("-1 # 2 * (-3 # 1) == 3 # 2", -1 # 2 * (-3 # 1) == 3 # 2),

    ("fromInteger 5 == 5 # 1", fromInteger 5 == 5 # 1),
    ("fromInteger 0 == 0 # 1", fromInteger 0 == 0 # 1),

    ("negate Zero == Zero", negate Zero == Zero),
    ("negate (1 # 2) == -1 # 2", negate (1 # 2) == -1 # 2),
    ("negate (-3 # 2) == 3 # 2", negate (-3 # 2) == 3 # 2),

    ("abs Zero == Zero", abs Zero == Zero),
    ("abs (1 # 2) == 1 # 2", abs (1 # 2) == 1 # 2),
    ("abs (-2 # 1) == 2 # 1", abs (-2 # 1) == 2 # 1),

    ("Zero - 1 # 2 == -1 # 2", Zero - 1 # 2 == -1 # 2),
    ("-5 # 4 - Zero == Zero", -5 # 4 - Zero == -5 # 4),
    ("4 # 3 - 1 # 2 == 5 # 6", 4 # 3 - 1 # 2 == 5 # 6),
    ("1 # 5 - 2 # 5 == -1 # 5", 1 # 5 - 2 # 5 == -1 # 5),
    ("-2 # 3 - 5 # 4 == -23 # 12", -2 # 3 - 5 # 4 == -23 # 12),
    ("-1 # 2 - -1 # 2 == Zero", -1 # 2 - -1 # 2 == Zero),

    ("Zero / (1 # 2) == Zero", Zero / (1 # 2) == Zero),
    ("Zero / (-4 # 3) == Zero", Zero / (-4 # 3) == Zero),
    ("1 # 2 / (3 # 4) == 2 # 3", 1 # 2 / (3 # 4) == 2 # 3),
    ("-4 # 7 / (1 # 2) == -8 # 7", -4 # 7 / (1 # 2) == -8 # 7),
    ("4 # 3 / (-1 # 1) == -4 # 3", 4 # 3 / (-1 # 1) == -4 # 3),
    ("-1 # 2 / (-1 # 2) == 1 # 1", -1 # 2 / (-1 # 2) == 1 # 1),

    ("recip (12 # 25) == 25 # 12", recip (12 # 25) == 25 # 12),
    ("recip (25 # 12) == 12 # 25", recip (25 # 12) == 12 # 25),
    ("recip (-3 # 2) == -2 # 3", recip (-3 # 2) == -2 # 3)
  ]

total
processTest : (String, Bool) -> String
processTest (name, outcome) = case outcome of
  False => "❌ " ++ name
  True => "✓ " ++ name

export
testRational: IO ()
testRational = do
  for (map processTest testSuite) putStrLn
  x <- pure True
  case any (not . snd) testSuite of
    True => putStrLn "Failure"
    False => putStrLn "Success"

