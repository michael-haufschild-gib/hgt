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
Off the diagonal Weil's kernel is the archimedean compensation (pole plane minus cusp and jets) plus
the Abel limit of the positive torsion energy of `ℙ¹_ℤ`. Smoothed by the cubic spline, the Frobenius
graphs form a curve of finite genus exactly under RH: Hasse–Weil on every plane `⟨Γ_1, Γ_n⟩`, `n ∈ ℕ`,
is RH, as Hasse–Weil for all powers of Frobenius is RH for a curve. A crude bound with any constant
at the integer degrees already is RH (the self-improvement is free; the exponent of a crude bound is
the zero width), and any set of degrees with gaps `O(√x)`, such as the squares, decides RH. The count
door is decided plane by plane: RH holds iff each plane `⟨Γ_1, Γ_n⟩` carries an `ℕ`-valued binary count
whose Tate limit is its defect.
-/
