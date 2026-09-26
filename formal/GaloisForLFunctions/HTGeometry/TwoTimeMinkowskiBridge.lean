import GaloisForLFunctions.HTGeometry.TwoTimeQuadratic
import GaloisForLFunctions.HTGeometry.HLSKinematics

/-!
# A negative two-plane inside Minkowski space

The two-negative-direction form is the restriction of the Minkowski quadratic
form to two spatial axes. This identifies its signature without assigning it
a causal light cone.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped Matrix

/-- Embed a two-coordinate pair in the first two spatial axes of Minkowski space. -/
def twoTimeSpatialEmbedding (p : ℝ × ℝ) : HLSMinkowskiVector :=
  ![0, p.1, p.2, 0]

/-- The restricted Minkowski form is exactly the two-negative-direction form. -/
theorem hlsMinkowskiForm_twoTimeSpatialEmbedding (p : ℝ × ℝ) :
    hlsMinkowskiForm (twoTimeSpatialEmbedding p) = twoTimeQuadratic p := by
  rw [hlsMinkowskiForm_apply]
  simp [twoTimeSpatialEmbedding, twoTimeQuadratic]
  ring

/-- This embedded plane has no nonzero null vector. -/
theorem hlsMinkowskiForm_twoTimeSpatialEmbedding_eq_zero_iff (p : ℝ × ℝ) :
    hlsMinkowskiForm (twoTimeSpatialEmbedding p) = 0 ↔ p = (0, 0) := by
  rw [hlsMinkowskiForm_twoTimeSpatialEmbedding, twoTimeQuadratic_eq_zero_iff]

end GaloisForLFunctions.HTGeometry
