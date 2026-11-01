import GaloisForLFunctions.SelectivePositivityAndThresholdLaws.LiouvilleOddWindowRefutationAndSelectiveFullPositivity
import GaloisForLFunctions.SelectivePositivityAndThresholdLaws.MoebiusEscapedPairingBoundaryLaw
import GaloisForLFunctions.SelectivePositivityAndThresholdLaws.SerreDualScalingCohomologyAndLargeSieveSections
import GaloisForLFunctions.SelectivePositivityAndThresholdLaws.JacobiHurwitzTorsionInflationAndShortCycleHeights
import GaloisForLFunctions.SelectivePositivityAndThresholdLaws.ParityLobeObstructionAndEscapeLaplaceSplit
import GaloisForLFunctions.SelectivePositivityAndThresholdLaws.TwoPrimeCatalanSeparationAndContinuumTowerObstruction
import GaloisForLFunctions.SelectivePositivityAndThresholdLaws.SemilocalPrimeTwoTrace.AbstractHilbertTraceToolkit
import GaloisForLFunctions.SelectivePositivityAndThresholdLaws.SemilocalPrimeTwoTrace.PrimeValuationShellLogTrace
import GaloisForLFunctions.SelectivePositivityAndThresholdLaws.SemilocalPrimeTwoTrace.HalfLogThreeCutoffAndTraceIdentity
import GaloisForLFunctions.SelectivePositivityAndThresholdLaws.SemilocalPrimeTwoTrace.SemilocalPositivityObstructions
import GaloisForLFunctions.SelectivePositivityAndThresholdLaws.SemilocalPrimeTwoTrace.IntrinsicWeilTraceAndWindowCorollaries
import GaloisForLFunctions.SelectivePositivityAndThresholdLaws.SemilocalPrimeTwoTrace.FinitePrimeSetSemilocalObstruction

/-!
# Selective Positivity and Threshold Laws

Umbrella for the boundary laws, obstructions, and selective positivity theorems across the Nyquist
horizon `½ log 2` and the global square-root threshold `X = T`: two-sided selective full-sector
Weil positivity past `½ log 2` on `[−181/500, 181/500]` (`w(2) = +log 2` coercive vs. smooth odd
and even refutations for `w(2) = −log 2` and `shiftedPairVonMangoldt`), the growing-endpoint
escaped Möbius boundary law across `0 < θ ≤ ½` and unconditional impossibility for `θ > ½`,
sign-independent Serre-dual real-valued scaling cohomology and sub-large-sieve section-growth width
equivalence, torsion-weighted Jacobi–Hurwitz quadratic inflation (`q_P(z) ≥ ½ |z · z|`) versus
unconditional short-cycle subquadratic heights, parity–lobe divergence for parity-blind dispersion
at `λ = 1 + δ > 1` with multi-modulus Ramanujan–stabilizer and escape Laplace pole-residue splits,
archimedean-free Catalan `{2, 3, 4}` separation and negative Liouville ground energy on
`[−23/40, 23/40]`, exponential `−c_0 e^A` divergence of unneutralized continuum prime towers
versus pole-neutralized Sobolev width equivalence, the `{∞, 2}` semilocal logarithmic trace
identity through `½ log 3` together with the four operator-theoretic positivity obstructions and the
intrinsic zero-form operator-trace equivalence (certified through `181/500 > ½ log 2`), and the
multi-prime `{∞} ∪ S` cardinality-uniform `−Θ(e^A)` ground-energy collapse, forced zero crossings,
positive-trace carrier no-go, quantitative visible-prime lower bound, and `(1 + ε)` multiplicative
syndeticity / infinitude-of-primes laws.
See `SelectivePositivityAndThresholdLaws/README.md`.
-/
