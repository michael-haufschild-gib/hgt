import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

/-!
# Boundary Weyl thresholds have no formal order

For a positive definite form `B` and a boundary functional `α`, the rank-one form `B - t α* α` is
positive semidefinite exactly when `t ≤ 1 / E_B(α)`, where `E_B(α)` is the dual energy.

Given two boundary functionals that are not scalar multiples of one another and any prescribed
positive energies `r_α`, `r_β`, there is a positive definite form realizing both.  Hence the two
Weyl thresholds admit no formal inequality in either direction: boundary location alone does not
order the Schur threshold.
-/

noncomputable section

namespace RHTower

open scoped InnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- **Dual pair.**  Two functionals that are not scalar multiples admit a vector normalized for the
first and killed by the second. -/
theorem exists_dual_vector {α β : V →ₗ[ℂ] ℂ} {z : V} (hz : β z = 1)
    (hindep : ∀ c : ℂ, α ≠ c • β) : ∃ u : V, α u = 1 ∧ β u = 0 := by
  by_cases hall : ∀ y : V, β y = 0 → α y = 0
  · exfalso
    refine hindep (α z) ?_
    refine LinearMap.ext fun v => ?_
    have hy : β (v - (β v) • z) = 0 := by
      simp [map_sub, map_smul, hz]
    have := hall _ hy
    rw [map_sub, map_smul, smul_eq_mul] at this
    have hval : α v = β v * α z := by linear_combination this
    simpa [LinearMap.smul_apply, smul_eq_mul, mul_comm] using hval
  · push Not at hall
    obtain ⟨y, hβy, hαy⟩ := hall
    refine ⟨(α y)⁻¹ • y, ?_, ?_⟩
    · rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hαy]
    · rw [map_smul, smul_eq_mul, hβy, mul_zero]

/-- The positive definite bulk form realizing prescribed dual energies. -/
def boundaryBulkForm (α β : V →ₗ[ℂ] ℂ) (u w : V) (ra rb : ℝ) (v : V) : ℝ :=
  ‖α v‖ ^ (2 : ℕ) / ra + ‖β v‖ ^ (2 : ℕ) / rb + ‖v - (α v) • u - (β v) • w‖ ^ (2 : ℕ)

theorem boundaryBulkForm_nonneg (α β : V →ₗ[ℂ] ℂ) (u w : V) {ra rb : ℝ}
    (hra : 0 < ra) (hrb : 0 < rb) (v : V) : 0 ≤ boundaryBulkForm α β u w ra rb v := by
  unfold boundaryBulkForm
  have h1 : 0 ≤ ‖α v‖ ^ (2 : ℕ) / ra := by positivity
  have h2 : 0 ≤ ‖β v‖ ^ (2 : ℕ) / rb := by positivity
  have h3 : 0 ≤ ‖v - (α v) • u - (β v) • w‖ ^ (2 : ℕ) := sq_nonneg _
  linarith

/-- **Positive definiteness.** -/
theorem boundaryBulkForm_pos (α β : V →ₗ[ℂ] ℂ) (u w : V) {ra rb : ℝ}
    (hra : 0 < ra) (hrb : 0 < rb) {v : V} (hv : v ≠ 0) :
    0 < boundaryBulkForm α β u w ra rb v := by
  rcases lt_or_eq_of_le (boundaryBulkForm_nonneg α β u w hra hrb v) with h | h
  · exact h
  · exfalso
    have h1 : 0 ≤ ‖α v‖ ^ (2 : ℕ) / ra := by positivity
    have h2 : 0 ≤ ‖β v‖ ^ (2 : ℕ) / rb := by positivity
    have h3 : 0 ≤ ‖v - (α v) • u - (β v) • w‖ ^ (2 : ℕ) := sq_nonneg _
    have hsum : ‖α v‖ ^ (2 : ℕ) / ra + ‖β v‖ ^ (2 : ℕ) / rb + ‖v - (α v) • u - (β v) • w‖ ^ (2 : ℕ) = 0 := by
      unfold boundaryBulkForm at h
      linarith
    have hA : ‖α v‖ ^ (2 : ℕ) / ra = 0 := by linarith
    have hB : ‖β v‖ ^ (2 : ℕ) / rb = 0 := by linarith
    have hC : ‖v - (α v) • u - (β v) • w‖ ^ (2 : ℕ) = 0 := by linarith
    have hαv : α v = 0 := by
      have hsq : ‖α v‖ ^ (2 : ℕ) = 0 := by
        field_simp at hA
        linarith [hA]
      have : ‖α v‖ = 0 := by nlinarith [norm_nonneg (α v)]
      exact norm_eq_zero.mp this
    have hβv : β v = 0 := by
      have hsq : ‖β v‖ ^ (2 : ℕ) = 0 := by
        field_simp at hB
        linarith [hB]
      have : ‖β v‖ = 0 := by nlinarith [norm_nonneg (β v)]
      exact norm_eq_zero.mp this
    have hzero : v - (α v) • u - (β v) • w = 0 := by
      have : ‖v - (α v) • u - (β v) • w‖ = 0 := by nlinarith [norm_nonneg (v - (α v) • u - (β v) • w)]
      exact norm_eq_zero.mp this
    rw [hαv, hβv] at hzero
    simp at hzero
    exact hv hzero

/-- The value of the bulk form at the first dual vector. -/
theorem boundaryBulkForm_at_u (α β : V →ₗ[ℂ] ℂ) {u w : V} (hαu : α u = 1) (hβu : β u = 0)
    (ra rb : ℝ) : boundaryBulkForm α β u w ra rb u = 1 / ra := by
  unfold boundaryBulkForm
  rw [hαu, hβu]
  simp

theorem boundaryBulkForm_at_w (α β : V →ₗ[ℂ] ℂ) {u w : V} (hαw : α w = 0) (hβw : β w = 1)
    (ra rb : ℝ) : boundaryBulkForm α β u w ra rb w = 1 / rb := by
  unfold boundaryBulkForm
  rw [hαw, hβw]
  simp

/-- **Schur threshold at the first boundary.**  The rank-one form `B - t α* α` is positive
semidefinite exactly for `t ≤ 1 / r_α`. -/
theorem boundaryThreshold_alpha (α β : V →ₗ[ℂ] ℂ) {u w : V} (hαu : α u = 1) (hβu : β u = 0)
    {ra rb : ℝ} (hrb : 0 < rb) (t : ℝ) :
    (∀ v : V, t * ‖α v‖ ^ (2 : ℕ) ≤ boundaryBulkForm α β u w ra rb v) ↔ t ≤ 1 / ra := by
  constructor
  · intro h
    have hu := h u
    rw [boundaryBulkForm_at_u α β hαu hβu ra rb, hαu] at hu
    simpa using hu
  · intro ht v
    have hstep : t * ‖α v‖ ^ (2 : ℕ) ≤ (1 / ra) * ‖α v‖ ^ (2 : ℕ) :=
      mul_le_mul_of_nonneg_right ht (sq_nonneg _)
    have hrest : (1 / ra) * ‖α v‖ ^ (2 : ℕ) ≤ boundaryBulkForm α β u w ra rb v := by
      unfold boundaryBulkForm
      have h2 : 0 ≤ ‖β v‖ ^ (2 : ℕ) / rb := by positivity
      have h3 : 0 ≤ ‖v - (α v) • u - (β v) • w‖ ^ (2 : ℕ) := sq_nonneg _
      have heq : (1 / ra) * ‖α v‖ ^ (2 : ℕ) = ‖α v‖ ^ (2 : ℕ) / ra := by ring
      linarith [heq]
    linarith

theorem boundaryThreshold_beta (α β : V →ₗ[ℂ] ℂ) {u w : V} (hαw : α w = 0) (hβw : β w = 1)
    {ra rb : ℝ} (hra : 0 < ra) (t : ℝ) :
    (∀ v : V, t * ‖β v‖ ^ (2 : ℕ) ≤ boundaryBulkForm α β u w ra rb v) ↔ t ≤ 1 / rb := by
  constructor
  · intro h
    have hw := h w
    rw [boundaryBulkForm_at_w α β hαw hβw ra rb, hβw] at hw
    simpa using hw
  · intro ht v
    have hstep : t * ‖β v‖ ^ (2 : ℕ) ≤ (1 / rb) * ‖β v‖ ^ (2 : ℕ) :=
      mul_le_mul_of_nonneg_right ht (sq_nonneg _)
    have hrest : (1 / rb) * ‖β v‖ ^ (2 : ℕ) ≤ boundaryBulkForm α β u w ra rb v := by
      unfold boundaryBulkForm
      have h1 : 0 ≤ ‖α v‖ ^ (2 : ℕ) / ra := by positivity
      have h3 : 0 ≤ ‖v - (α v) • u - (β v) • w‖ ^ (2 : ℕ) := sq_nonneg _
      have heq : (1 / rb) * ‖β v‖ ^ (2 : ℕ) = ‖β v‖ ^ (2 : ℕ) / rb := by ring
      linarith [heq]
    linarith

/-- **No formal order of the two Weyl thresholds.**  Every pair of positive dual energies is
realized by a positive definite bulk form, so either threshold can be the smaller one. -/
theorem boundaryWeylThreshold_not_monotone (α β : V →ₗ[ℂ] ℂ) {u w : V}
    (hαu : α u = 1) (hβu : β u = 0) (hαw : α w = 0) (hβw : β w = 1)
    (ra rb : ℝ) (hra : 0 < ra) (hrb : 0 < rb) :
    (∀ v : V, v ≠ 0 → 0 < boundaryBulkForm α β u w ra rb v) ∧
      (∀ t : ℝ, (∀ v : V, t * ‖α v‖ ^ (2 : ℕ) ≤ boundaryBulkForm α β u w ra rb v) ↔ t ≤ 1 / ra) ∧
      (∀ t : ℝ, (∀ v : V, t * ‖β v‖ ^ (2 : ℕ) ≤ boundaryBulkForm α β u w ra rb v) ↔ t ≤ 1 / rb) :=
  ⟨fun _ hv => boundaryBulkForm_pos α β u w hra hrb hv,
    boundaryThreshold_alpha α β hαu hβu hrb,
    boundaryThreshold_beta α β hαw hβw hra⟩

end RHTower
