import Mathlib.Analysis.InnerProductSpace.Orthonormal

/-!
# An operator's value on a normalized vector

Dividing a vector by its norm divides every operator's value on it by the same number, since the
operator is linear and the scalar is a positive real.  So an estimate proved for a vector transfers
to its normalization at the cost of one division by the norm.

This is the bridge between estimates stated for a family's members and hypotheses stated for the
orthonormal family they generate.
-/

noncomputable section

namespace RHTower

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- **Normalization divides.**  An operator's value on the normalization of a nonzero vector is its
value on the vector, divided by the vector's norm. -/
theorem norm_apply_normalize (S : E →L[𝕜] F) {v : E} (hv : v ≠ 0) :
    ‖S (((‖v‖ : 𝕜))⁻¹ • v)‖ = ‖S v‖ / ‖v‖ := by
  have hpos : (0 : ℝ) < ‖v‖ := norm_pos_iff.mpr hv
  rw [map_smul, norm_smul, norm_inv, RCLike.norm_ofReal, abs_of_pos hpos]
  ring

end RHTower
