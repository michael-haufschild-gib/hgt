import GaloisForLFunctions.SurfaceOfSpecZ.TheFrobeniusZonotopeSurface
import GaloisForLFunctions.SurfaceOfSpecZ.TheTwoHalfProducts
import GaloisForLFunctions.SurfaceOfSpecZ.TheArchimedeanPlaceIsNotToric
import GaloisForLFunctions.SurfaceOfSpecZ.ThePrimesAreTheJumpsOfTheHeckeKernel
import GaloisForLFunctions.SurfaceOfSpecZ.NoMetricOnTheProjectiveLineCarriesTheJets
import GaloisForLFunctions.SurfaceOfSpecZ.ThePointCountOfSpecZ

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
-/
