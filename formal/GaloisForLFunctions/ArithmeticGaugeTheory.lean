import GaloisForLFunctions.ArithmeticGaugeTheory.TheAdditivelyInvariantPoint
import GaloisForLFunctions.ArithmeticGaugeTheory.ApproximateRingEndomorphisms
import GaloisForLFunctions.ArithmeticGaugeTheory.TheDivisorCollapse
import GaloisForLFunctions.ArithmeticGaugeTheory.TheShellDecomposition
import GaloisForLFunctions.ArithmeticGaugeTheory.TheGaugeExponent
import GaloisForLFunctions.ArithmeticGaugeTheory.FactorialRatiosHaveBoundedMultiplicity
import GaloisForLFunctions.ArithmeticGaugeTheory.TheCoherencePrinciple
import GaloisForLFunctions.ArithmeticGaugeTheory.TheArchimedeanLineCarriesTheExponent
import GaloisForLFunctions.ArithmeticGaugeTheory.TheGaugeExponentIsATailInvariant
import GaloisForLFunctions.ArithmeticGaugeTheory.TheAdamsOperations
import GaloisForLFunctions.ArithmeticGaugeTheory.TheMajorArcsOfTheShells
import GaloisForLFunctions.ArithmeticGaugeTheory.AffineInvariantKernelsAreTrivial
import GaloisForLFunctions.ArithmeticGaugeTheory.TheExponentIsNotGaugeInvariant
import GaloisForLFunctions.ArithmeticGaugeTheory.TheLiouvillePointsHaveExponentOne
import GaloisForLFunctions.ArithmeticGaugeTheory.TheGaugeExponentZeroOneLaw
import GaloisForLFunctions.ArithmeticGaugeTheory.TheFiniteGaugePointsSampleHaar
import GaloisForLFunctions.ArithmeticGaugeTheory.TheDirichletPointsCancelThroughPeriodicity
import GaloisForLFunctions.ArithmeticGaugeTheory.TheTypicalExponentIsOneHalf
import GaloisForLFunctions.ArithmeticGaugeTheory.TheSpecialPointsOfTheConstantSourceAreAtypical
import GaloisForLFunctions.ArithmeticGaugeTheory.TheTrivialPointIsNeverBetterThanTypical
import GaloisForLFunctions.ArithmeticGaugeTheory.TheSpecialLocusReadsGRH
import GaloisForLFunctions.ArithmeticGaugeTheory.TheSpecialLocusIsTypicalOnAverage
import GaloisForLFunctions.ArithmeticGaugeTheory.TheLiouvillePointIsTheAntipode
import GaloisForLFunctions.ArithmeticGaugeTheory.TheEscapeStateLeansToTheLiouvillePoint

/-!
# Arithmetic Gauge Theory of the ring ℤ

Umbrella for the study of `ℤ` through its two duals: the gauge torus of unimodular completely
multiplicative functions and the additive structure. Special-point rigidity (the trivial point is
the only additively invariant gauge point); approximate ring endomorphisms and the Frobenius gap;
the divisor collapse `Λ * 1 = log` as a coherent, point-specific gauge-charged statistic; the shell
decomposition of the prime pair form, whose gauge average is its ratio part; the gauge exponent,
at most `1/2` almost surely and equal to the zero abscissa at the trivial point; the
bounded multiplicity of factorial-ratio producers; the coherence principle (nonnegative statistics
are maximal at the trivial point; the pole as coherence; diamagnetism of the prime pair form); the
invariance of the gauge exponent along the archimedean line and under finite prime modifications; the
Adams operations, on whose fixed points the Frobenius equation `x^q = x` lives; the major arcs of the
shells (finite gauge subgroups keep the shells with `q ∣ j`); the triviality of affine-invariant
kernels; the impossibility of gauge-invariant exponent certificates below `3/4`; the exponent one of
the Liouville points; the zero–one law and the typical exponent, which is exactly `1/2`; the large sieve as the statement that
the finite gauge points sample Haar measure; the constant source, typical with exponent `1/2` almost
surely, has exponent `0` or `1` on the whole special locus (typical modulo the pole); the trivial point
is never better than typical, so RH is the equality of its exponent with the typical one; the same holds
at every primitive Dirichlet point, whose Möbius exponent is the zero abscissa of `L(s, χ)`, and on
average over the special locus typicality holds unconditionally at every scale; for the prime source
the Liouville point is the antipode of the trivial point, so the pole separates the twins by sign; the
escape state of the Möbius sums is an Euler product leaning to the Liouville point, blind to zeros. See
`ArithmeticGaugeTheory/README.md`.
-/
