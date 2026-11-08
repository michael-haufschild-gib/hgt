import GaloisForLFunctions.CountingHolography.TheCountLawAtEveryGenus
import GaloisForLFunctions.CountingHolography.TheCountLawOfATrueCurveAtEveryGenus
import GaloisForLFunctions.CountingHolography.TheRosatiHeightIsTheBornRule
import GaloisForLFunctions.CountingHolography.TheCountLawOfEveryHyperellipticCurve
import GaloisForLFunctions.CountingHolography.TheGenusTwoRung
import GaloisForLFunctions.CountingHolography.TheJacobianCountOfABiellipticGenusTwoCurve
import GaloisForLFunctions.CountingHolography.TheBornRuleOfABlackHole
import GaloisForLFunctions.CountingHolography.TheBornRuleAtGenusTwo
import GaloisForLFunctions.CountingHolography.TheBornRulesOfAnOscillatorBank
import GaloisForLFunctions.CountingHolography.TheBoundarySquareIsTheOscillation
import GaloisForLFunctions.CountingHolography.TheBoundaryAlgebraOfABlackHole
import GaloisForLFunctions.CountingHolography.HeckeSuppliesConservationNotTheLaw
import GaloisForLFunctions.CountingHolography.LinearCountsAreDegenerate
import GaloisForLFunctions.CountingHolography.TheTateLimitOfACount
import GaloisForLFunctions.CountingHolography.TheFareyReadingOfTheHorocycle
import GaloisForLFunctions.CountingHolography.TheHorocycleRateIsTheSquareRootFareyLaw
import GaloisForLFunctions.CountingHolography.ThermalizationFasterThanTheSquareRootIsAZeroFreeStrip
import GaloisForLFunctions.CountingHolography.TheRateOfASharpShell
import GaloisForLFunctions.CountingHolography.TheCountFailsAtTheSecondPlaceOfAHeckeTriangleGroup

/-!
# Counting holography

Quantum numbers of boundary sources on arithmetic quotients of AdS. A count law, the parallelogram law
for the number of open channels of a probe, has a quadratic half, which is the covariance of a form
under the delay and forces the functional equation, and a count half, which is the sign: universal
damping. On a bank of oscillators the Born rules are Krein squares and Wronskians, Hermitian forms on
repeated oscillators, and a count exists iff every oscillator is damped. The boundary algebra
`R[π]/(π² − tπ + q)` with the partner involution `π* = q/π` has the Krein square as its GNS form, and a
positive state exactly when the black hole is damped. The tower count law is
Hasse–Weil at every genus, it holds on every hyperelliptic curve of either parity, in particular on every
genus-two curve (the even-degree Riemann hypothesis is proved here by descent), and the Rosati
height of the probe ring is its equal-weight Born rule. On a bielliptic genus-two curve the count law is
produced by heights alone: the sum of Manin's counts on the two elliptic factors of the Jacobian. Linear
counts never obey the law; the genus-two graph has the first count law for `q ≤ 19` and the tower law
exactly for `q ≤ 3`. Every non-arithmetic Hecke group fails through the count, at a second place of its
invariant trace field. Over `ℤ` RH is the statement that the Krein square
of the integer probes is the Tate limit of a count. On the modular horizon the pseudo-Eisenstein series
of a shell counts cusp images, its horocycle mean is a totient-weighted count of Farey points, and RH
is the square-root law for that count; thermalization faster than the square root by `y^δ` is the
zero-free strip `Re ρ ≤ 1 − 2δ`. A sharp shell thermalizes at rate `y^{1/2} log(1/y)` unconditionally:
its horoball count is a Möbius sum of lattice-point counts of quarter discs. See
`CountingHolography/README.md`.
-/
import GaloisForLFunctions.CountingHolography.TheCountDoorOfACurveAndOfZ
