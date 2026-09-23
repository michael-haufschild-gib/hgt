import GaloisForLFunctions.HilbertMetric.LamzouriFiniteMultiplicity
import GaloisForLFunctions.HTGeometry.CharacteristicDefectGramCapacity

/-!
# Lamzouri affine minorants for the Julia defect Gram kernel

The Julia defect attenuation kernel has an unconditional anchored Gram
capacity inequality.  Composing it with Lamzouri's tangent-line minorant for
a square turns every anchored packet correlation into an affine lower bound
for the full coherent pair energy.
-/

open Finset
open scoped BigOperators

namespace HTGeometry

/-- Every tangent line to the anchored-correlation square lies below the full
Julia defect Gram energy. -/
theorem juliaDefectAttenuationKernel_anchorCorrelation_affineMinorant
    {N : ℕ} (x w : Fin N → ℝ) (t : ℝ) :
    2 * t * (∑ i, w i * juliaDefectAttenuationKernel (x i)) - t ^ (2 : ℕ) ≤
      ∑ i, ∑ j,
        w i * juliaDefectAttenuationKernel (x j - x i) * w j := by
  have hquad :=
    GaloisForLFunctions.HilbertMetric.lamzouriQuadratic_affineMinorant
      (∑ i, w i * juliaDefectAttenuationKernel (x i)) t
  have hgram :=
    juliaDefectAttenuationKernel_anchorCorrelation_sq_le_gramEnergy x w
  simpa only [mul_assoc, mul_comm, mul_left_comm] using hquad.trans hgram

end HTGeometry
