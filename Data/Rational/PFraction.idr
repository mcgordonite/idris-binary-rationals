module PFraction

import Data.Rational.LTEProperties

||| The subset of natural numbers greater than zero.
public export
PNat : Type
PNat = Subset Nat (\x => GT x 0)

||| The fraction representation of a strictly positive rational number.
public export
PFraction : Type
PFraction = (PNat, PNat)

export
total
multPFraction : PFraction -> PFraction -> PFraction
multPFraction (Element xn xnGtZ, Element xd xdGtZ) (Element yn ynGtZ, Element yd ydGtZ) =
  (Element (xn * yn) (multGtZ xnGtZ ynGtZ), Element (xd * yd) (multGtZ xdGtZ ydGtZ))

export
total
divPFraction : PFraction -> PFraction -> PFraction
divPFraction (Element xn xnGtZ, Element xd xdGtZ) (Element yn ynGtZ, Element yd ydGtZ) =
  (Element (xn * yd) (multGtZ xnGtZ ydGtZ), Element (xd * yn) (multGtZ xdGtZ ynGtZ))

export
total
plusPFraction : PFraction -> PFraction -> PFraction
plusPFraction (Element xn xnGtZ, Element xd xdGtZ) (Element yn ynGtZ, Element yd ydGtZ) =
  (
    Element (xn * yd + yn * xd) (plusGtZ (multGtZ xnGtZ ydGtZ) (multGtZ ynGtZ xdGtZ)),
    Element (xd * yd) (multGtZ xdGtZ ydGtZ)
  )

