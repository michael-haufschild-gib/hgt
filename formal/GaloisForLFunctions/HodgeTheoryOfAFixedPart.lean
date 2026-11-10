import GaloisForLFunctions.HodgeTheoryOfAFixedPart.TheNormalFormOfThePairingOfTheDegreePoints
import GaloisForLFunctions.HodgeTheoryOfAFixedPart.TheHodgeIndexHoldsAtEveryScaleOnShortWindows
import GaloisForLFunctions.HodgeTheoryOfAFixedPart.WeilsFormInTheGaugeOfTheFlatTail
import GaloisForLFunctions.HodgeTheoryOfAFixedPart.RiemannRochOnTheTowerHasTheGluingIndex
import GaloisForLFunctions.HodgeTheoryOfAFixedPart.TheCombOfUnitMassesFixesTheContacts
import GaloisForLFunctions.HodgeTheoryOfAFixedPart.TheIndexOfAWindowIsFiniteAtEveryScale
import GaloisForLFunctions.HodgeTheoryOfAFixedPart.ASeparatedCombIsOneOrbitOfTheFrobeniusMonoid
import GaloisForLFunctions.HodgeTheoryOfAFixedPart.WhatTheSectionsOfTheSquareCertify
import GaloisForLFunctions.HodgeTheoryOfAFixedPart.TheInequalityAtFiniteScaleDecidesTheLimit
import GaloisForLFunctions.HodgeTheoryOfAFixedPart.OneInequalityPerPrimeOnTheComb
import GaloisForLFunctions.HodgeTheoryOfAFixedPart.TheJetsAreASumOfHardySquares
import GaloisForLFunctions.HodgeTheoryOfAFixedPart.TheIndexOfThePairingIsAtMostTheDefectOfASplitting
import GaloisForLFunctions.HodgeTheoryOfAFixedPart.ShortWindowsDoNotSeeTheContacts

/-!
# Hodge theory of a fixed part

Positivity and index theorems for the pairing of the degree points of the arithmetic square.

* The normal form: one matrix on the positive integers, with the jets, the contacts and the
  counterterm of the comb; Zariski's lemma on a comb; the limit on packets.
* The inequality of Castelnuovo and Severi at every finite scale on short windows; the finiteness
  of the index of a window, uniformly in the scale; the passage from finite scale to the limit.
* Weil's form in the gauge of the flat tail, with the remainder of the prime number theorem as
  potential; Chebyshev's identity as a contact energy; the carry cocycle.
* The jets as a sum of positive semidefinite kernels, one for each archimedean weight, and the
  ordered approximations by the number of weights.
* Riemann–Roch and Bézout on the tower of lines; what the sections of the square certify.
* The comb of unit masses as the datum that fixes the contacts; the separated combs stable under
  the Frobenius monoid; short windows as a statement that does not see the contacts.
* One inequality per prime on logarithmic windows with exceptional sets, for a two-bump divisor.
* The index of the pairing against the defect of a splitting; the line law of Lagarias and
  Suzuki as an index-one statement.

See `HodgeTheoryOfAFixedPart/README.md`.
-/
