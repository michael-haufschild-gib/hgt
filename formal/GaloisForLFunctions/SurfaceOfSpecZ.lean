import GaloisForLFunctions.SurfaceOfSpecZ.TheFrobeniusZonotopeSurface
import GaloisForLFunctions.SurfaceOfSpecZ.TheTwoHalfProducts
import GaloisForLFunctions.SurfaceOfSpecZ.TheArchimedeanPlaceIsNotToric
import GaloisForLFunctions.SurfaceOfSpecZ.ThePrimesAreTheJumpsOfTheHeckeKernel
import GaloisForLFunctions.SurfaceOfSpecZ.NoMetricOnTheProjectiveLineCarriesTheJets
import GaloisForLFunctions.SurfaceOfSpecZ.ThePointCountOfSpecZ
import GaloisForLFunctions.SurfaceOfSpecZ.TheTorsionEnergyAgainstTheJets
import GaloisForLFunctions.SurfaceOfSpecZ.HasseWeilForPairsOfFrobeniusGraphs
import GaloisForLFunctions.SurfaceOfSpecZ.HasseWeilAtTheIntegerDegrees
import GaloisForLFunctions.SurfaceOfSpecZ.CrudeHasseWeilAtTheIntegerDegrees
import GaloisForLFunctions.SurfaceOfSpecZ.SparseDegreesDecideRH
import GaloisForLFunctions.SurfaceOfSpecZ.ThePlaneCountsAtTheIntegerDegrees
import GaloisForLFunctions.SurfaceOfSpecZ.TheArchimedeanFrobeniusIsAHyperbolicGreenFunction
import GaloisForLFunctions.SurfaceOfSpecZ.TheArchimedeanFrobeniusHasInfiniteRank
import GaloisForLFunctions.SurfaceOfSpecZ.TheSignOfWeilsAtomicKernelIsPlastic
import GaloisForLFunctions.SurfaceOfSpecZ.TheArchimedeanSelfEnergyIsLogarithmic
import GaloisForLFunctions.SurfaceOfSpecZ.HasseWeilForPairsOfPrimeDegrees
import GaloisForLFunctions.SurfaceOfSpecZ.TheAtomicGenusIsNLogN
import GaloisForLFunctions.SurfaceOfSpecZ.TheAtomicSurfaceHasGenusNLogN
import GaloisForLFunctions.SurfaceOfSpecZ.ThePrimeChannelOfTheAtomicSurface
import GaloisForLFunctions.SurfaceOfSpecZ.HasseWeilAtThePrimeDegreesBoundsTheWidth
import GaloisForLFunctions.SurfaceOfSpecZ.OneSidedHasseWeilAtTheIntegerDegrees
import GaloisForLFunctions.SurfaceOfSpecZ.TheStepanovSideIsBlindToRealZeros
import GaloisForLFunctions.SurfaceOfSpecZ.TheStepanovCountAtTheSquareDegrees
import GaloisForLFunctions.SurfaceOfSpecZ.TheTraceZetaFunctionAtThePowerDegrees
import GaloisForLFunctions.SurfaceOfSpecZ.BaseChangeAtThePowerDegrees
import GaloisForLFunctions.SurfaceOfSpecZ.HyperbolicQuotientsJetCarriersAndCoupledDamping

/-!
# The surface of `Spec ℤ`

Models of the two-dimensional object whose Riemann–Roch would count the Weil form `Q` on integer
probes. The `𝔽₁`-model: power-map graphs on `ℙ¹ × ℙ¹` realize the pole plane of the scaling
surface, and their torus part, the Frobenius zonotopes, carries a Castelnuovo–Severi defect that is a
sum of squares of integer counts, equal after normalization to the first archimedean channel of
Weil's form. The off-diagonal of Weil's form between atoms at `log m` and `log n` is assembled
from one `𝔽₁`-cusp (`ℙ¹ × ℙ¹`), the archimedean jets of the trivial zeros, and the gcd-twisted
torsion intersection on `ℙ¹_ℤ`. No metric on `ℙ¹_ℤ` supplies the archimedean part (its Green
pairings of torsion orbits are the prime channel with opposite sign plus rank two, the jets have rank
at least three on coprime orders; toric pairings of coprime orbits depend on the product of the
orders, Weil's on the ratio), and no
continuous Hecke kernel supplies the whole: the primes are jump discontinuities at the logarithms of
prime powers. Over `𝔽_{1ⁿ}` the surface has `Λ(n) + 1 + 1/(n² − 1)` points (prime, cusp, jets) where
`ℙ¹` has `n + 1`; the trace is of size `n`, so no finite genus passes the Hasse–Weil test on two-term
probes: atomic Frobenius graphs force infinite genus, and smoothing performs the prime number theorem.
On a dyadic block of degrees `[N, 2N)` the genus the atoms need is of exact order `N log N`: no torsion
orbits meet inside the block, and the jets make the defect a negative harmonic matrix. On all degrees
`≤ N` the atomic surface satisfies the Hodge index unconditionally with genus `4N(1 + log N)`: the jets
cost `N log N`, the pole `N log N` through Cauchy–Schwarz, the primes only `O(N)`; in fact the prime
channel, a Hecke operator, has spectral radius between `(log N)/4 − O(1)` and `log N + O(1)` (Mertens).
Off the diagonal Weil's kernel is the archimedean compensation (pole plane minus cusp and jets) plus
the Abel limit of the positive torsion energy of `ℙ¹_ℤ`. Smoothed by the cubic spline, the Frobenius
graphs form a curve of finite genus exactly under RH: Hasse–Weil on every plane `⟨Γ_1, Γ_n⟩`, `n ∈ ℕ`,
is RH, as Hasse–Weil for all powers of Frobenius is RH for a curve. A crude bound with any constant
at the integer degrees already is RH (the self-improvement is free; the exponent of a crude bound is
the zero width), and any set of degrees with gaps `O(√x)`, such as the squares, decides RH. One
side of the crude bound suffices, as for Bombieri–Stepanov: RH holds iff the traces at the integer
degrees are bounded below (an upper bound on the smoothed point counts), and iff they are bounded
above; Pringsheim's theorem becomes Landau's. The Stepanov side needs exactly that `ζ` has no real
zeros in the strip: without real zeros it decides the line for every configuration, and on the real
pair `{¼, ¾}` it holds while the pair is off the line, as a real Frobenius eigenvalue above `√q` passes
an upper bound on point counts and needs the twist. As Bombieri needs only the even extensions, the
square degrees suffice: an upper bound on the smoothed point counts at the degrees `n²` is RH. Base
change holds as for curves: for every `k` the degrees `nᵏ` decide RH from one side, through the trace
zeta function `Σ_z e_z ζ(s − kz)`, whose poles `1 + kz` are the zeros moved by the base change. The count
door is decided plane by plane: RH holds iff each plane `⟨Γ_1, Γ_n⟩` carries an `ℕ`-valued binary count
whose Tate limit is its defect. The prime degrees alone decide RH through their pairs `⟨Γ_p, Γ_q⟩`; on the planes `⟨Γ_1, Γ_p⟩`
they bound the zero width by the excess `θ − ½` of the prime-gap exponent, `1/12` by Huxley. In hyperbolic three-space `ℍ³`, only pointwise rotations around the vertical degree geodesic preserve the off-diagonal archimedean Frobenius, any discrete finite-covolume quotient triggers a thin–thick folding dichotomy while parabolic cusps diverge harmonically at `s = ½`, the pure trivial-zero jets have infinite rank on coprime primes and are carried by a dilation-covariant causal monomial bundle on `L²(0, ∞)`, and counterterm-free positive damping requires coherent archimedean–torsion correlation locking (impossible on atomic degrees below `N log N`, equivalent to RH on smoothed Frobenius graphs, and impossible on either channel alone).
-/
