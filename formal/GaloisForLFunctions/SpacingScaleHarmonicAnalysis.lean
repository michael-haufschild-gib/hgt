import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheSelfEnergyOfAnAtomHasConstantOne
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheArchimedeanCrossKernel
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheSelfEnergyOfAnAtomIsExactlyLogarithmic
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheTiltedPrimeRows
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheStabilityLawAtTheSpacingScale
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheDiamagneticInequality
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheSpacingScaleLawIsUniversal
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.UnboundedOverlapIsTheRiemannHypothesis
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheGaugeEntersThroughNonRatioLags
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheAtomicFamilyIsADirichletPolynomial

/-!
# Arithmetic Harmonic Analysis at the Spacing Scale

Umbrella for the harmonic analysis of Weil's form on the atomic family
`f_x = Σ_{n ≤ N} x_n g(· − log n)` at the spacing `δ_N = log(1 + 1/N)` of the atoms: the
self-energy of an atom, exactly logarithmic with constant one; the archimedean cross kernel; the tilted Schur rows of
the prime form, and the stability law at the spacing scale with its gauge blindness and its
universality over all coefficients dominated by `Λ`; the
diamagnetic inequality (`ζ` is the ground state of its gauge orbit); the law that positivity on
the atomic families of one fixed bump — unbounded overlap — is the Riemann hypothesis; the overlap
calculus, in which the gauge enters only through non-ratio lags; and the dictionary between atomic
tests and Dirichlet polynomials sampled at the zeros.
See `SpacingScaleHarmonicAnalysis/README.md`.
-/
