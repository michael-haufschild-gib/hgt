import GaloisForLFunctions.ArithmeticLefschetzStepanovTheory.TheFrobeniusOfTheTorsionIsGalois
import GaloisForLFunctions.ArithmeticLefschetzStepanovTheory.TheOrderAtTheCommonFixedPointCostsTheDegree
import GaloisForLFunctions.ArithmeticLefschetzStepanovTheory.IntegralityActsOnlyOnTheTorsion
import GaloisForLFunctions.ArithmeticLefschetzStepanovTheory.TheStepanovCountOfTheClosedPoints
import GaloisForLFunctions.ArithmeticLefschetzStepanovTheory.SiegelAuxiliariesOnTheTorsion
import GaloisForLFunctions.ArithmeticLefschetzStepanovTheory.TheZeroEstimateAtTheReturns
import GaloisForLFunctions.ArithmeticLefschetzStepanovTheory.ExactVanishingCostsTheDegree
import GaloisForLFunctions.ArithmeticLefschetzStepanovTheory.TheExcessOrderIsARelationAmongTheLogarithms
import GaloisForLFunctions.ArithmeticLefschetzStepanovTheory.StepanovsConstructionOnTheTorsion
import GaloisForLFunctions.ArithmeticLefschetzStepanovTheory.TheLefschetzNumbersAreStepanovDegrees
import GaloisForLFunctions.ArithmeticLefschetzStepanovTheory.TheStepanovBoundSeparatesZetaFromTheOneOff

/-!
# Arithmetic Lefschetz–Stepanov theory

Stepanov's half of Weil's proof over `Spec ℤ`: which Frobenius, which auxiliaries, which orders of
vanishing and which identity plays the role of `x^q = x`. The exact Frobenius of the integer
auxiliaries is the Adams operation, which is the Galois action on the torsion of the prime torus and
the dilation on the prime orbit; the norm is its integrality amplifier. Exact vanishing on the orbit
is confined to countably many heights; exact order at any point costs the degree; the closed points
of the prime circles are counted at Chebyshev's price. The Lefschetz numbers of the Frobenius
graphs of degree `≤ N` are the degree of the minimal auxiliary vanishing at their fixed points, so
RH is an upper bound on that degree; the bound fails for the integer-norm one-off. Siegel
auxiliaries and a zero estimate uniform in the number of logarithms are the tools. See `ArithmeticLefschetzStepanovTheory/README.md`.
-/
