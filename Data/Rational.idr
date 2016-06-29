module Data.Rational

import Data.Rational.LTEProperties
import Data.Rational.PFraction
import Control.Algebra
import Data.ZZ
import Data.Sign

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
data Rational = Zero | Pos QPlus | Neg QPlus

||| Calculate the path in the Stern Brocot tree required to represent the given
||| non-zero positive fraction.
||| @ n The numerator
||| @ d The denominator
||| @ nGtZ Proof that the numerator is greater than zero
||| @ dGtZ Proof that the denominator is greater than zero
export
total
inject : (n : Nat) -> (d : Nat) -> .(nGtZ : GT n Z) -> .(dGtZ : GT d Z) -> QPlus
inject n d nGtZ dGtZ with (cmp n d)
  inject d d nGtZ dGtZ | CmpEQ = []
  inject n (n + S diff) nGtZ dGtZ | (CmpLT diff) = 
    L :: inject n (assert_smaller (n + S diff) (S diff)) nGtZ (LTESucc LTEZero)
  inject (d + S diff) d nGtZ dGtZ | (CmpGT diff) =
    R :: inject (assert_smaller (d + S diff) (S diff)) d (LTESucc LTEZero) dGtZ

||| Calculate the fraction representation for the given path in the Stern Brocot tree.
export
total
extract : QPlus -> PFraction
extract [] = (Element 1 (LTESucc LTEZero), Element 1 (LTESucc LTEZero))
extract (L :: rest) = let (Element n pn, Element d pd) = extract rest in 
  (Element (n * d) (multGtZ pn pd), Element ((n + d) * d) (multGtZ (plusGtZ pn pd) pd))
extract (R :: rest) = let (Element n pn, Element d pd) = extract rest in
  (Element (n + d) (plusGtZ pn pd), (Element d pd))

infixl 9 #

||| Represent a fraction as a Rational. Useful for rational literals.
||| @ n The numerator
||| @ d The denominator (must be greater than zero)
export
total
(#) : (n : ZZ) -> (d : Nat) -> {auto dGtZ : GT d Z} -> Rational
(#) (Pos Z) d {dGtZ} = Zero
(#) (Pos (S k)) d {dGtZ} = Pos $ inject (S k) d (LTESucc LTEZero) dGtZ
(#) (NegS k) d {dGtZ} = Neg $ inject (S k) d (LTESucc LTEZero) dGtZ

-- The reciprocal of a Stern Brocot path is calculated by switching branch at every node.
total
recipImpl : QPlus -> QPlus
recipImpl = map flipBranch where
  flipBranch L = R
  flipBranch R = L

-- L :: _ < [] < R :: _
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
total
fromNatImpl : (x : Nat) -> GT x Z -> QPlus
fromNatImpl (S k) (LTESucc LTEZero) = replicate k R

-- The difference between two positive rationals is a value from the full field.
total
diffImpl : QPlus -> QPlus -> Rational
diffImpl xs ys = 
  let (Element xn xnGtZ, Element xd xdGtZ) = extract xs in
  let (Element yn ynGtZ, Element yd ydGtZ) = extract ys in
  diffHelper (xn * yd) (multGtZ xnGtZ ydGtZ) (yn * xd) (multGtZ ynGtZ xdGtZ) (xd * yd) (multGtZ xdGtZ ydGtZ)
  where
    diffHelper : (n1 : Nat) -> GT n1 Z -> (n2 : Nat) -> GT n2 Z -> (d : Nat) -> GT d Z -> Rational
    diffHelper n1 n1GtZ n2 n2GtZ d dGtZ with (cmp n1 n2)
      diffHelper n n1GtZ n n2GtZ d dGtZ | CmpEQ = Zero
      diffHelper n1 n1GtZ (n1 + (S y)) n2GtZ d dGtZ | (CmpLT y) =
        Neg (inject (S y) d (LTESucc LTEZero) dGtZ)
      diffHelper (n2 + (S x)) n1GtZ n2 n2GtZ d dGtZ | (CmpGT x) =
        Pos (inject (S x) d (LTESucc LTEZero) dGtZ)

total
showImpl : QPlus -> String
showImpl x = 
  let (Element xn xnGtZ, Element xd xdGtZ) = extract x in
  show xn ++ "/" ++ show xd

total
liftFractionOp : (PFraction -> PFraction -> PFraction) -> QPlus -> QPlus -> QPlus
liftFractionOp f x y =
  let (Element n nGtZ, Element d dGtZ) = f (extract x) (extract y) in 
  inject n d nGtZ dGtZ

------------------------------------------------------
----- Interface instances
------------------------------------------------------

export
Show Rational where
  show Zero = "0"
  show (Pos x) = "+" ++ showImpl x
  show (Neg x) = "-" ++ showImpl x

export
Cast Nat Rational where
  cast Z = Zero
  cast (S k) = Pos $ fromNatImpl (S k) (LTESucc LTEZero)

export
Eq SBBranch where
  L == L = True
  R == R = True
  _ == _ = False

export
Eq Rational where
  Zero == Zero = True
  (Pos x) == (Pos y) = x == y
  (Neg x) == (Neg y) = x == y
  _ == _ = False

export
Ord Rational where
  compare Zero Zero = EQ
  compare Zero (Pos _) = LT
  compare Zero (Neg _) = GT
  compare (Pos _) Zero = GT
  compare (Neg _) Zero = LT
  compare (Pos _) (Neg _) = GT
  compare (Neg _) (Pos _) = LT
  compare (Pos a) (Pos b) = compareImpl a b
  compare (Neg a) (Neg b) = compareImpl a b

export
Signed Rational where
  sign Zero = Zero
  sign (Pos _) = Plus
  sign (Neg _) = Minus

export
Num Rational where
  (+) Zero x = x
  (+) x Zero = x
  (+) (Pos x) (Pos y) = Pos (liftFractionOp plusPFraction x y)
  (+) (Neg x) (Neg y) = Neg (liftFractionOp plusPFraction x y)
  (+) (Pos x) (Neg y) = diffImpl x y
  (+) (Neg x) (Pos y) = diffImpl y x

  (*) Zero _ = Zero
  (*) _ Zero = Zero
  (*) (Pos x) (Pos y) = Pos (liftFractionOp multPFraction x y)
  (*) (Pos x) (Neg y) = Neg (liftFractionOp multPFraction x y)
  (*) (Neg x) (Pos y) = Neg (liftFractionOp multPFraction x y)
  (*) (Neg x) (Neg y) = Pos (liftFractionOp multPFraction x y)
  
  fromInteger x with (compare x 0)
    fromInteger x | EQ = Zero
    fromInteger x | LT = case (fromInteger (negate x)) of
      Z => Zero
      S k => Neg (fromNatImpl (S k) (LTESucc LTEZero))
    fromInteger x | GT = case (fromInteger x) of
      Z => Zero
      S k => Pos (fromNatImpl (S k) (LTESucc LTEZero))

export
Neg Rational where
  negate Zero = Zero
  negate (Pos x) = Neg x
  negate (Neg x) = Pos x

  abs Zero = Zero
  abs (Pos x) = Pos x
  abs (Neg x) = Pos x

  (-) Zero x = negate x
  (-) x Zero = x
  (-) (Pos x) (Pos y) = diffImpl x y
  (-) (Pos x) (Neg y) = Pos (liftFractionOp plusPFraction x y)
  (-) (Neg x) (Pos y) = Neg (liftFractionOp plusPFraction x y)
  (-) (Neg x) (Neg y) = diffImpl y x

export
Fractional Rational where
  (/) Zero _ = Zero
  (/) _ Zero = Zero
  (/) (Pos x) (Pos y) = Pos (liftFractionOp divPFraction x y)
  (/) (Pos x) (Neg y) = Neg (liftFractionOp divPFraction x y)
  (/) (Neg x) (Pos y) = Neg (liftFractionOp divPFraction x y)
  (/) (Neg x) (Neg y) = Pos (liftFractionOp divPFraction x y)

  recip Zero = Zero
  recip (Pos xs) = Pos (recipImpl xs)
  recip (Neg xs) = Neg (recipImpl xs)

export
Semigroup Rational where
  (<+>) = (+)

export
Monoid Rational where
  neutral = Zero

export
Group Rational where
  inverse = negate

export
AbelianGroup Rational where

export
Ring Rational where
  (<.>) = (*)

export
RingWithUnity Rational where
  unity = Pos []

export
Field Rational where
  inverseM Zero notZero = void (notZero Refl)
  inverseM (Pos x) _ = Pos (recipImpl x)
  inverseM (Neg x) _ = Neg (recipImpl x)

------------------------------------------------------
----- Properties
------------------------------------------------------

export
total
lNotR : L = R -> Void
lNotR Refl impossible

export
total
posInjective : the Rational (Pos xs) = the Rational (Pos ys) -> xs = ys
posInjective Refl = Refl

export
total
negInjective : (the Rational (Neg xs)) = the Rational (Neg ys) -> xs = ys
negInjective Refl = Refl

export
total
posNotNeg : the Rational (Pos xs) = the Rational (Neg ys) -> Void
posNotNeg Refl impossible

export
total
posNotZero : Pos xs = Zero -> Void
posNotZero Refl impossible

export
total
negNotZero : the Rational (Neg xs) = Zero -> Void
negNotZero Refl impossible

export 
total
multZeroRightZero : (x : Rational) -> x * Zero = Zero
multZeroRightZero Zero = Refl
multZeroRightZero (Pos _) = Refl
multZeroRightZero (Neg _) = Refl

export
total
multZeroLeftZero : (x : Rational) -> Zero * x = Zero
multZeroLeftZero Zero = Refl
multZeroLeftZero (Pos xs) = Refl
multZeroLeftZero (Neg xs) = Refl

export
total
plusZeroLeftNeutral : (x : Rational) -> Zero + x = x
plusZeroLeftNeutral Zero = Refl
plusZeroLeftNeutral (Pos xs) = Refl
plusZeroLeftNeutral (Neg xs) = Refl

export
total
plusZeroRightNeutral : (x : Rational) -> x + Zero = x
plusZeroRightNeutral Zero = Refl
plusZeroRightNeutral (Pos xs) = Refl
plusZeroRightNeutral (Neg xs) = Refl

------------------------------------------------------
----- Deciable equality
------------------------------------------------------

export
DecEq SBBranch where
  decEq L L = Yes Refl
  decEq R R = Yes Refl
  decEq L R = No lNotR
  decEq R L = No (negEqSym lNotR)

export
DecEq Rational where
  decEq Zero Zero = Yes Refl
  decEq Zero (Pos xs) = No (negEqSym posNotZero)
  decEq Zero (Neg xs) = No (negEqSym negNotZero)
  decEq (Pos xs) Zero = No posNotZero
  decEq (Pos xs) (Neg ys) = No posNotNeg
  decEq (Neg xs) Zero = No negNotZero
  decEq (Neg xs) (Pos ys) = No (negEqSym posNotNeg)
  decEq (Pos xs) (Pos ys) = case decEq xs ys of
    (Yes prf) => Yes (cong prf)
    (No contra) => No (\prf => contra (posInjective prf))
  decEq (Neg xs) (Neg ys) = case decEq xs ys of
    (Yes prf) => Yes (cong prf)
    (No contra) => No (\prf => contra (negInjective prf))

