import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheSelfEnergyOfAnAtomHasConstantOne
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheArchimedeanCrossKernel
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheSelfEnergyOfAnAtomIsExactlyLogarithmic
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheRobinConstantOfAnAtom
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheArchimedeanPairingOfTwoAtoms
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheTiltedPrimeRows
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheStabilityLawAtTheSpacingScale
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheDiamagneticInequality
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheSpacingScaleLawIsUniversal
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.UnboundedOverlapIsTheRiemannHypothesis
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheGaugeEntersThroughNonRatioLags
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheAtomicFamilyIsADirichletPolynomial
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.WeilsFormIsContinuousInTheLevyNorm
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheLogLatticeSynthesizesWideTests
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheCriticalExponent
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheGaugeBecomesVisibleAtTheCriticalExponent
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.ThePoleIsTheOnlyNegativeSquareBeyondTheThreshold
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheWeightOfOneZero
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheMarkovFormFailsInsideTheSeparatedRegime
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheUniversalThresholdIsFinite
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheRowsAtBoundedOverlap
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheSecondOrderSynthesis
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheEulerMaclaurinSynthesis
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheOverlapLawAtEveryRoot
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheGaugeAtEveryRoot
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.ThePoleAtEveryRoot
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheGevreyWindow
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheGevreyProfile
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheDenjoyCarlemanProfiles
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheArchimedeanDensityHasQuadraticIncrementControl

/-!
# Arithmetic Harmonic Analysis at the Spacing Scale

Umbrella for the harmonic analysis of Weil's form on the atomic family
`f_x = Σ_{n ≤ N} x_n g(· − log n)` at the spacing `δ_N = log(1 + 1/N)` of the atoms:

* the self-energy of an atom, exactly logarithmic with constant one, its Robin constant, and the
  archimedean pairing and cross kernel of atoms;
* the tilted Schur rows of the prime form and the stability law at a fixed fraction of the spacing,
  gauge blind and universal over all coefficients dominated by `Λ`; the diamagnetic inequality;
* the failure of the Markov form alone at every width `cδ_N`, `c > e/(2π)`, on the pole vector
  (`2c_∞ = 2 log 2 + π/2`): the stability law needs its rank-one pole correction;
* the universal threshold is finite: `c₀ ≤ K_univ < ∞`, by a wide dipole against the sign twist
  aligned with its lag correlations;
* the overlap calculus (the gauge enters only through non-ratio lags), the prime form at bounded
  overlap as row sums — `‖g‖² P_N` plus non-ratio rows `O(K) + O(K (m/N) log N)` — and the
  Dirichlet-polynomial dictionary, with the weight of one zero bounded by the overlap ratio;
* the overlap law: once the overlap ratio beats `√(log N)` — widths `N^{−θ}`, `θ < 1`, or overlap
  `(log N)^{1/2+ε}` — positivity on the atomic families is the Riemann hypothesis (and at every
  fixed width); every twisted explicit formula that fails somewhere fails there; and the Markov
  form has a negative square there unconditionally, and only one iff RH;
* the second-order (trapezoid) synthesis moves the overlap law to the fourth root: overlap
  `(log N)^{1/4+ε}` suffices for `C²` profiles;
* the Euler–Maclaurin synthesis with weights `F(log n − c)/n` is accurate to every order for smooth
  profiles: positivity is RH at overlap `(log N)^ε` for every `ε > 0`, every stable form (Weil's,
  its bounded twists, the Markov form) transfers there, every twist that fails somewhere is seen
  there, and the Markov form has a negative square there unconditionally and only one iff RH;
* for Gevrey profiles of class `s` an Euler–Maclaurin order `2⌈log log k⌉ + 2` brings the window to
  `(log log N)^s`; the explicit profile `c E(1+x)E(1−x)` is Gevrey of class `2`, and the
  Denjoy–Carleman profiles `c E(x^r)|_{1±x}`, `r` odd, are of class `1 + 1/r`: positivity is RH at
  overlap `(log log N)^α` for every `α > 1`.

See `SpacingScaleHarmonicAnalysis/README.md`.
-/
