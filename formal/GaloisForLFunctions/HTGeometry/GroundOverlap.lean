import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# The normalized overlap with a fixed direction

The squared cosine of the angle between a fixed vector and a moving one is invariant under nonzero
real rescaling of the moving vector, and equals one exactly when the moving vector is a unimodular
multiple of the fixed one.  These two facts are what turn a leading-order expansion into a statement
about the limiting *direction* rather than the limiting vector.
-/

open Complex

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem norm_inner_real_smul_right (r : ℝ) (u v : E) :
    ‖(inner ℂ u (r • v) : ℂ)‖ = |r| * ‖(inner ℂ u v : ℂ)‖ := by
  rw [← Complex.coe_smul, inner_smul_right, norm_mul, Complex.norm_real, Real.norm_eq_abs]

theorem norm_inner_self_eq (u : E) : ‖(inner ℂ u u : ℂ)‖ = ‖u‖ ^ 2 := by
  rw [inner_self_eq_norm_sq_to_K, norm_pow]
  simp

/-- The normalized squared overlap of a vector with a fixed direction. -/
def groundOverlap (u v : E) : ℝ := ‖(inner ℂ u v : ℂ)‖ ^ 2 / (‖u‖ ^ 2 * ‖v‖ ^ 2)

theorem groundOverlap_real_smul {r : ℝ} (hr : r ≠ 0) (u v : E) :
    groundOverlap u (r • v) = groundOverlap u v := by
  have hr' : |r| ≠ 0 := abs_ne_zero.mpr hr
  rw [groundOverlap, groundOverlap, norm_inner_real_smul_right, norm_smul, Real.norm_eq_abs,
    mul_pow, mul_pow]
  field_simp

theorem groundOverlap_unimodular_smul {c : ℂ} (hc : ‖c‖ = 1) {u : E} (hu : u ≠ 0) :
    groundOverlap u (c • u) = 1 := by
  have hnu : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
  rw [groundOverlap, inner_smul_right, norm_mul, hc, one_mul, norm_smul, hc, one_mul,
    norm_inner_self_eq]
  field_simp

end GaloisForLFunctions.HTGeometry
