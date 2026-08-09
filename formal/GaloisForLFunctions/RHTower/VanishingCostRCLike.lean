import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# The vanishing cost over an arbitrary RCLike field

`BoundaryInteriorVanishingCost` proves that in a *real* inner product space the distance from a vector
`f` to the hyperplane annihilated by `v ≠ 0` is exactly `|⟪v,f⟫|/‖v‖`.  The statement and proof are
insensitive to the scalar field: Cauchy--Schwarz gives the lower bound and the explicit orthogonal
projection attains it over any `RCLike` field.

The complex case is the one the Nyman--Beurling lane needs.  There the annihilating functional is a
*complex* point evaluation, and its kernel is a complex hyperplane — not the kernel of the real part of
the inner product, which is a strictly larger set.  So the real statement cannot be used, and this file
supplies the version that can.

The real statements in `BoundaryInteriorVanishingCost` are re-derived from these.
-/

open scoped InnerProductSpace

noncomputable section

namespace RHTower

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- **Lower bound.**  Every vector annihilated by `v` is at distance at least `‖⟪v,f⟫‖/‖v‖` from
`f`. -/
theorem dist_innerKer_ge (v f : H) (hv : v ≠ 0) {g : H} (hg : inner 𝕜 v g = 0) :
    ‖inner 𝕜 v f‖ / ‖v‖ ≤ ‖f - g‖ := by
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  rw [div_le_iff₀ hvpos]
  have hinner : inner 𝕜 v (f - g) = inner 𝕜 v f := by
    rw [inner_sub_right, hg, sub_zero]
  calc ‖inner 𝕜 v f‖ = ‖inner 𝕜 v (f - g)‖ := by rw [hinner]
    _ ≤ ‖v‖ * ‖f - g‖ := norm_inner_le_norm v (f - g)
    _ = ‖f - g‖ * ‖v‖ := by ring

/-- **The bound is attained.**  The explicit orthogonal projection realises the distance. -/
theorem dist_innerKer_attained (v f : H) (hv : v ≠ 0) :
    ∃ g : H, inner 𝕜 v g = 0 ∧ ‖f - g‖ = ‖inner 𝕜 v f‖ / ‖v‖ := by
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hv2 : inner 𝕜 v v = ((‖v‖ ^ 2 : ℝ) : 𝕜) := by
    rw [inner_self_eq_norm_sq_to_K]; push_cast; ring
  have hvne : ((‖v‖ ^ 2 : ℝ) : 𝕜) ≠ 0 := by
    simp only [ne_eq, RCLike.ofReal_eq_zero]
    positivity
  refine ⟨f - (inner 𝕜 v f / ((‖v‖ ^ 2 : ℝ) : 𝕜)) • v, ?_, ?_⟩
  · rw [inner_sub_right, inner_smul_right, hv2, div_mul_cancel₀ _ hvne, sub_self]
  · rw [sub_sub_cancel, norm_smul, norm_div, RCLike.norm_ofReal,
      abs_of_pos (by positivity : (0 : ℝ) < ‖v‖ ^ 2)]
    rw [div_mul_eq_mul_div, sq]
    rw [mul_comm ‖v‖ ‖v‖, ← div_div, mul_div_assoc, div_self (ne_of_gt hvpos), mul_one]

/-- **The exact vanishing cost, over any `RCLike` field.**  The distance from `f` to the hyperplane of
vectors annihilated by `v` is exactly `‖⟪v,f⟫‖/‖v‖`. -/
theorem innerKer_vanishing_cost (v f : H) (hv : v ≠ 0) :
    (∀ g : H, inner 𝕜 v g = 0 → ‖inner 𝕜 v f‖ / ‖v‖ ≤ ‖f - g‖) ∧
      ∃ g : H, inner 𝕜 v g = 0 ∧ ‖f - g‖ = ‖inner 𝕜 v f‖ / ‖v‖ :=
  ⟨fun _g hg => dist_innerKer_ge v f hv hg, dist_innerKer_attained v f hv⟩

/-- A strictly positive lower bound whenever the detector does not annihilate `f`: the explicit form a
convergence contradiction consumes. -/
theorem dist_innerKer_pos (v f : H) (hv : v ≠ 0) (hf : inner 𝕜 v f ≠ 0) :
    0 < ‖inner 𝕜 v f‖ / ‖v‖ := by
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  exact div_pos (norm_pos_iff.mpr hf) hvpos

end RHTower

end
