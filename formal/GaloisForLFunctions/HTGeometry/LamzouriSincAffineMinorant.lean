import GaloisForLFunctions.HilbertMetric.LamzouriFiniteMultiplicity
import GaloisForLFunctions.HTGeometry.JuliaDefectSpectralEquilibrium
import GaloisForLFunctions.HTGeometry.CharacteristicEquilibriumDefect

/-!
# Lamzouri affine minorants for squared-sinc Gram kernels

Squared sinc is a normalized even positive-definite kernel in the corpus.
Its anchored Gram-capacity bound combines with Lamzouri's tangent-line
minorant to control every finite weighted sinc packet.
-/

open Finset
open scoped BigOperators

namespace HTGeometry

/-- Every tangent line to squared anchored sinc correlation lies below the
full coherent squared-sinc pair energy. -/
theorem sincSq_anchorCorrelation_affineMinorant
    (A : ℝ) {N : ℕ} (x w : Fin N → ℝ) (t : ℝ) :
    2 * t * (∑ i, w i * Real.sinc (A * x i) ^ 2) - t ^ 2 ≤
      ∑ i, ∑ j, w i * Real.sinc (A * (x j - x i)) ^ 2 * w j := by
  have hgram := anchorCorrelation_sq_le_gramEnergy_of_positiveDefinite
    (fun y : ℝ => Real.sinc (A * y) ^ 2)
    (GaloisForLFunctions.HTGeometry.positiveDefiniteOnReal_sinc_sq A)
    (by simp)
    (by intro y; rw [mul_neg, Real.sinc_neg]) x w
  have hquad :=
    GaloisForLFunctions.HilbertMetric.lamzouriQuadratic_affineMinorant
      (∑ i, w i * Real.sinc (A * x i) ^ 2) t
  simpa only [mul_assoc, mul_comm, mul_left_comm] using hquad.trans hgram

end HTGeometry
