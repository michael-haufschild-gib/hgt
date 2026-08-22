import GaloisForLFunctions.HTGeometry.CFCSqrtPerturbation

/-!
# Norm balls and Loewner intervals around the identity

For a self-adjoint `a`, the norm ball `‖a - 1‖ ≤ δ` sits inside the Loewner interval
`[(1-δ)·1, (1+δ)·1]`, and the operator norm of the inverse is controlled by the lower Loewner
bound.  These translations are what turn the qualitative "near the identity" of the Wasserstein
existence theorem into explicit constants.
-/

open scoped Ring

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions.HTGeometry.BuresWasserstein

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- A self-adjoint element in a norm ball around `1` is Loewner-dominated. -/
lemma le_smul_one_of_norm_sub_one_le {a : A} (ha : IsSelfAdjoint a) {δ : ℝ}
    (h : ‖a - 1‖ ≤ δ) : a ≤ (1 + δ) • (1 : A) := by
  have hsa : IsSelfAdjoint (a - 1) := ha.sub (IsSelfAdjoint.one A)
  have h1 : a - 1 ≤ ‖a - 1‖ • (1 : A) := by
    have := hsa.le_algebraMap_norm_self
    rwa [Algebra.algebraMap_eq_smul_one] at this
  have h2 : a - 1 ≤ δ • (1 : A) :=
    h1.trans (smul_le_smul_of_nonneg_right h (zero_le_one (α := A)))
  have h3 : a ≤ 1 + δ • (1 : A) := by
    have h4 := add_le_add_right h2 (1 : A)
    simpa [sub_add_cancel, add_comm] using h4
  rw [add_smul, one_smul]
  exact h3

/-- A self-adjoint element in a norm ball around `1` Loewner-dominates. -/
lemma smul_one_le_of_norm_sub_one_le {a : A} (ha : IsSelfAdjoint a) {δ : ℝ}
    (h : ‖a - 1‖ ≤ δ) : (1 - δ) • (1 : A) ≤ a := by
  have hsa : IsSelfAdjoint ((1 : A) - a) := (IsSelfAdjoint.one A).sub ha
  have h1 : (1 : A) - a ≤ ‖(1 : A) - a‖ • (1 : A) := by
    have h0 := hsa.le_algebraMap_norm_self
    rwa [Algebra.algebraMap_eq_smul_one] at h0
  have hnorm : ‖(1 : A) - a‖ = ‖a - 1‖ := by rw [← norm_neg (a - 1), neg_sub]
  have h2 : (1 : A) - a ≤ δ • (1 : A) := by
    rw [hnorm] at h1
    exact h1.trans (smul_le_smul_of_nonneg_right h (zero_le_one (α := A)))
  have h3 : (1 : A) - δ • (1 : A) ≤ a := by
    have h4 := sub_le_sub_left h2 (1 : A)
    simpa using h4
  rw [sub_smul, one_smul]
  exact h3

/-- A self-adjoint perturbation shifts a Loewner lower bound by at most its norm. -/
lemma smul_one_le_of_norm_sub_le {X Y : A} (hsa : IsSelfAdjoint (X - Y)) {m r : ℝ}
    (hr : ‖X - Y‖ ≤ r) (hY : m • (1 : A) ≤ Y) : (m - r) • (1 : A) ≤ X := by
  have h1 : -(X - Y) ≤ ‖X - Y‖ • (1 : A) := by
    have h := (hsa.neg).le_algebraMap_norm_self
    rwa [Algebra.algebraMap_eq_smul_one, norm_neg] at h
  have h2 : -(X - Y) ≤ r • (1 : A) :=
    h1.trans (smul_le_smul_of_nonneg_right hr (zero_le_one (α := A)))
  have h2' : Y - X ≤ r • (1 : A) := by rw [← neg_sub]; exact h2
  have h3 : Y - r • (1 : A) ≤ X := by
    rw [sub_le_iff_le_add, add_comm]
    exact sub_le_iff_le_add.mp h2'
  refine le_trans ?_ h3
  rw [sub_smul]
  exact sub_le_sub_right hY _

/-- A self-adjoint perturbation shifts a Loewner upper bound by at most its norm. -/
lemma le_smul_one_of_norm_sub_le {X Y : A} (hsa : IsSelfAdjoint (X - Y)) {M r : ℝ}
    (hr : ‖X - Y‖ ≤ r) (hY : Y ≤ M • (1 : A)) : X ≤ (M + r) • (1 : A) := by
  have h1 : X - Y ≤ ‖X - Y‖ • (1 : A) := by
    have h := hsa.le_algebraMap_norm_self
    rwa [Algebra.algebraMap_eq_smul_one] at h
  have h2 : X - Y ≤ r • (1 : A) :=
    h1.trans (smul_le_smul_of_nonneg_right hr (zero_le_one (α := A)))
  have h3 : X ≤ r • (1 : A) + Y := sub_le_iff_le_add.mp h2
  refine h3.trans ?_
  rw [add_smul, add_comm (r • (1 : A)) Y]
  exact add_le_add_left hY _

/-- An element dominating a positive multiple of the unit is strictly positive. -/
lemma isStrictlyPositive_of_smul_one_le {x : A} {m : ℝ} (hm : 0 < m)
    (h : m • (1 : A) ≤ x) : IsStrictlyPositive x := by
  refine (CStarAlgebra.isUnit_of_le _ h
    (IsStrictlyPositive.smul hm isStrictlyPositive_one)).isStrictlyPositive ?_
  exact le_trans (smul_nonneg hm.le zero_le_one) h

/-- A self-adjoint element within distance `< 1` of the identity is strictly positive. -/
lemma isStrictlyPositive_of_norm_sub_one_le {x : A} (hx : IsSelfAdjoint x) {δ : ℝ}
    (hδ1 : δ < 1) (h : ‖x - 1‖ ≤ δ) : IsStrictlyPositive x := by
  have hlow : (1 - δ) • (1 : A) ≤ x := smul_one_le_of_norm_sub_one_le hx h
  have hpos : (0 : ℝ) < 1 - δ := by linarith
  refine (CStarAlgebra.isUnit_of_le _ hlow
    (IsStrictlyPositive.smul hpos isStrictlyPositive_one)).isStrictlyPositive ?_
  exact le_trans (smul_nonneg hpos.le zero_le_one) hlow

/-- The operator norm of the inverse is bounded by the reciprocal of the lower Loewner bound. -/
lemma norm_ringInverse_le_of_smul_one_le {a : A} (ha : IsStrictlyPositive a) {m : ℝ}
    (hm : 0 < m) (h : m • (1 : A) ≤ a) : ‖(a⁻¹ʳ : A)‖ ≤ m⁻¹ :=
  norm_le_of_le_smul_one ha.ringInverse.nonneg (inv_pos.mpr hm).le
    (ringInverse_le_of_smul_one_le hm h)

/-- The operator norm is bounded by the upper Loewner bound. -/
lemma norm_le_of_norm_sub_one_le {a : A} (ha : IsSelfAdjoint a) {δ : ℝ} (hδ : 0 ≤ δ)
    (h : ‖a - 1‖ ≤ δ) (hnn : 0 ≤ a) : ‖a‖ ≤ 1 + δ :=
  norm_le_of_le_smul_one hnn (by linarith) (le_smul_one_of_norm_sub_one_le ha h)

end

end GaloisForLFunctions.HTGeometry
