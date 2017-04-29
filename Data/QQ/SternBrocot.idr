module Data.QQ.SternBrocot

import Data.So
import Control.Algebra
import Data.Matrix
import Data.Sign
import Data.ZZ

||| A path in the Stern Brocot tree is constructed by choosing either the left
||| or right branch.
public export
data SBBranch : Type where
  ||| L is the child node representing the smaller rational number.
  L : SBBranch
  ||| R is the child node representing the larger rational number.
  R : SBBranch

||| A non-zero positive rational number can be represented uniquely as a path in
||| the Stern Brocot tree.
public export
QPlus : Type
QPlus = List SBBranch

||| A rational number is either zero, a positive QPlus or a negative QPlus.
public export
data QQ = Zero | Pos QPlus | Neg QPlus

||| Calculate the path in the Stern Brocot tree required to represent the given
||| non-zero positive fraction.
||| @ n The numerator
||| @ d The denominator
||| @ nGtZ Proof that the numerator is greater than zero
||| @ dGtZ Proof that the denominator is greater than zero
export
injectQPlus : (n : Nat) -> (d : Nat) -> .(nGtZ : GT n Z) -> .(dGtZ : GT d Z) -> QPlus
injectQPlus n d nGtZ dGtZ with (cmp n d)
  injectQPlus d d nGtZ dGtZ | CmpEQ = []
  injectQPlus n (n + S diff) nGtZ dGtZ | (CmpLT diff) = L :: assert_total (injectQPlus n (S diff) nGtZ (LTESucc LTEZero))
  injectQPlus (d + S diff) d nGtZ dGtZ | (CmpGT diff) = R :: assert_total (injectQPlus (S diff) d (LTESucc LTEZero) dGtZ)

total
plusGtZ : {x : Nat} -> GT x 0 -> (y : Nat) -> GT (plus x y) 0
plusGtZ {x = Z} LTEZero _ impossible
plusGtZ {x = Z} (LTESucc _) _ impossible
plusGtZ {x = (S k)} prf y = LTESucc LTEZero

total
multGtZ : {x : Nat} -> {y : Nat} -> GT x 0 -> GT y 0 -> GT (mult x y) 0
multGtZ {x = Z} (LTESucc _) _ impossible
multGtZ {x = (S _)} {y = Z} _ LTEZero impossible
multGtZ {x = (S _)} {y = Z} _ (LTESucc _) impossible
multGtZ {x = (S k)} {y = (S j)} xGtZ yGtZ = LTESucc LTEZero

||| Calculate the fraction representation for the given path in the Stern Brocot tree.
||| Outputs a pair of Nats greater than zero.
export
total
extractQPlus : QPlus -> (Subset Nat (\x => GT x 0), Subset Nat (\x => GT x 0))
extractQPlus [] = (Element 1 (LTESucc LTEZero), Element 1 (LTESucc LTEZero))
extractQPlus (L :: rest) = let (Element n pn, Element d pd) = extractQPlus rest in 
  (Element (n * d) (multGtZ pn pd), Element ((n + d) * d) (multGtZ (plusGtZ pn d) pd))
extractQPlus (R :: rest) = let (Element n pn, Element d pd) = extractQPlus rest in
  (Element (n + d) (plusGtZ pn d), (Element d pd))

||| Represent a fraction as a QQ.
||| @ n The numerator
||| @ d The denominator
||| @ dNotZ Proof that the denominator is not zero
export
total
injectQQ : (n : ZZ) -> (d : ZZ) -> (dNotZ : Not (d = Pos Z)) -> QQ
injectQQ n (Pos Z) dNotZ = void (dNotZ Refl)
injectQQ (Pos Z) d dNotZ = Zero
injectQQ (Pos (S j)) (Pos (S k)) dNotZ = Pos (injectQPlus (S j) (S k) (LTESucc LTEZero) (LTESucc LTEZero))
injectQQ (NegS j) (Pos (S k)) dNotZ = Neg (injectQPlus (S j) (S k) (LTESucc LTEZero) (LTESucc LTEZero))
injectQQ (Pos (S j)) (NegS k) dNotZ = Neg (injectQPlus (S j) (S k) (LTESucc LTEZero) (LTESucc LTEZero))
injectQQ (NegS j) (NegS k) dNotZ = Pos (injectQPlus (S j) (S k) (LTESucc LTEZero) (LTESucc LTEZero))

infixl 9 #

||| Represent a fraction as a QQ. Useful for rational literals.
||| @ n The numerator
||| @ d The denominator (must be greater than zero)
||| @ dGtZ Proof that the denominator is greter than zero
export
total
(#) : (n : ZZ) -> (d : Nat) -> {auto dGtZ : GT d Z} -> QQ
(#) _ Z {dGtZ = LTEZero} impossible
(#) _ Z {dGtZ = (LTESucc _)} impossible
(#) n (S k) {dGtZ} = injectQQ n (Pos (S k)) (SIsNotZ . posInjective)

-- The reciprocal of a Stern Brocot path is calculated by switching branch at every node.
export
total
recipImpl : QPlus -> QPlus
recipImpl = map flipBranch where
  flipBranch L = R
  flipBranch R = L

-- L :: _ < [] < R :: _
export
total
compareImpl : QPlus -> QPlus -> Ordering
compareImpl [] [] = EQ
compareImpl [] (L :: _) = GT
compareImpl [] (R :: _) = LT
compareImpl (L :: _) [] = LT 
compareImpl (R :: _) [] = GT
compareImpl (L :: _) (R :: _) = LT
compareImpl (R :: _) (L :: _) = GT
compareImpl (L :: xs) (L :: ys) = compareImpl xs ys
compareImpl (R :: xs) (R :: ys) = compareImpl xs ys

-- Natural numbers are represented by always taking the right branch.
export
total
fromNatImpl : (x : Nat) -> GT x Z -> QPlus
fromNatImpl (S k) (LTESucc LTEZero) = replicate k R

export
total
negateQQ : QQ -> QQ
negateQQ Zero = Zero
negateQQ (Pos q) = Neg q
negateQQ (Neg q) = Pos q

------------------------------------------------------
----- Comparison View
------------------------------------------------------

export
data LteQPlus : QPlus -> QPlus -> Type where
  LteQPlusNilNil : LteQPlus [] []
  LteQPlusNilR : LteQPlus [] (R :: _)
  LteQPlusLR : LteQPlus (L :: _) (R :: _)
  LteQPlusLL : LteQPlus x y -> LteQPlus (L :: x) (L :: y)
  LteQPlusRR : LteQPlus x y -> LteQPlus (R :: x) (R :: y)

export
total
lteQPlusRefl : (q : QPlus) -> LteQPlus q q
lteQPlusRefl [] = LteQPlusNilNil
lteQPlusRefl (L :: bs) = LteQPlusLL (lteQPlusRefl bs)
lteQPlusRefl (R :: bs) = LteQPlusRR (lteQPlusRefl bs)

export
total
lteQPlusFromSub : LteQPlus x y -> LteQPlus (b :: x) (b :: y)
lteQPlusFromSub {b = L} prf = LteQPlusLL prf
lteQPlusFromSub {b = R} prf = LteQPlusRR prf

export
total
lteQPlusTransitive : LteQPlus x y -> LteQPlus y z -> LteQPlus x z
lteQPlusTransitive LteQPlusNilNil LteQPlusNilNil = LteQPlusNilNil
lteQPlusTransitive LteQPlusNilNil LteQPlusNilR = LteQPlusNilR
lteQPlusTransitive LteQPlusNilR (LteQPlusRR _) = LteQPlusNilR
lteQPlusTransitive LteQPlusLR (LteQPlusRR _) = LteQPlusLR
lteQPlusTransitive (LteQPlusLL _) LteQPlusLR = LteQPlusLR
lteQPlusTransitive (LteQPlusLL a) (LteQPlusLL b) = lteQPlusFromSub (lteQPlusTransitive a b)
lteQPlusTransitive (LteQPlusRR a) (LteQPlusRR b) = lteQPlusFromSub (lteQPlusTransitive a b)

--------------------------------------------------------
------- Interface implementations
--------------------------------------------------------

export
Show SBBranch where
  show L = "L"
  show R = "R"

export
Show QQ where
  show Zero = "Zero"
  show (Pos xs) = "(Pos " ++ show xs ++ ")"
  show (Neg xs) = "(Neg " ++ show xs ++ ")"

export
Signed QQ where
  sign Zero = Zero
  sign (Pos xs) = Plus
  sign (Neg xs) = Minus

export
Eq SBBranch where
  (==) L L = True
  (==) R R = True
  (==) _ _ = False

export
Eq QQ where
  (==) Zero Zero = True
  (==) (Pos xs) (Pos ys) = xs == ys
  (==) (Neg xs) (Neg ys) = xs == ys
  (==) _ _ = False

export
Ord QQ where
  compare Zero Zero = EQ
  compare Zero (Pos xs) = LT
  compare Zero (Neg xs) = GT
  compare (Pos xs) Zero = GT
  compare (Neg xs) Zero = LT
  compare (Pos xs) (Neg ys) = GT
  compare (Neg xs) (Pos ys) = LT
  compare (Pos xs) (Pos ys) = compareImpl xs ys
  compare (Neg xs) (Neg ys) = compareImpl xs ys

--------------------------------------------------------
------- Deciable equality
--------------------------------------------------------

export
total
lNotR : L = R -> Void
lNotR Refl impossible

export
DecEq SBBranch where
  decEq L L = Yes Refl
  decEq R R = Yes Refl
  decEq L R = No lNotR
  decEq R L = No (lNotR . sym)

export
total 
posNotZero : {a : QPlus} -> Pos a = Zero -> Void
posNotZero Refl impossible

export
total
posNotNeg : {a : QPlus} -> Pos a = Neg b -> Void
posNotNeg Refl impossible

export
total
negNotZero : {a : QPlus} -> Neg a = Zero -> Void
negNotZero Refl impossible

export
total
posInjective : {a : QPlus} -> Pos a = Pos b -> a = b
posInjective Refl = Refl

export
total
negInjective : {a : QPlus} -> Neg a = Neg b -> a = b
negInjective Refl = Refl

export
DecEq QQ where
  decEq Zero Zero = Yes Refl
  decEq (Pos xs) Zero = No posNotZero
  decEq (Neg xs) Zero = No negNotZero
  decEq Zero (Pos xs) = No (posNotZero . sym)
  decEq Zero (Neg xs) = No (negNotZero . sym)
  decEq (Pos xs) (Neg ys) = No posNotNeg
  decEq (Neg xs) (Pos ys) = No (posNotNeg . sym)
  decEq (Pos xs) (Pos ys) = case decEq xs ys of
    (Yes prf) => Yes (cong prf)
    (No contra) => No (contra . posInjective)
  decEq (Neg xs) (Neg ys) = case decEq xs ys of
    (Yes prf) => Yes (cong prf)
    (No contra) => No (contra . negInjective)

