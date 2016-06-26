module Data.Rational.LTEProperties

||| If two Nats x and y are greater than zero, x + y is also greater than zero.
public export
total
plusGtZ : {x : Nat} -> {y : Nat} -> GT x 0 -> GT y 0 -> GT (plus x y) 0
plusGtZ (LTESucc x) (LTESucc y) = LTESucc LTEZero

||| If two Nats x and y are greater than zero, x * y is also greater than zero.
public export
total
multGtZ : {x : Nat} -> {y : Nat} -> GT x 0 -> GT y 0 -> GT (mult x y) 0
multGtZ {x = Z} (LTESucc _) _ impossible
multGtZ {x = (S _)} {y = Z} _ LTEZero impossible
multGtZ {x = (S _)} {y = Z} _ (LTESucc _) impossible
multGtZ {x = (S k)} {y = (S j)} xGtZ yGtZ = LTESucc LTEZero

