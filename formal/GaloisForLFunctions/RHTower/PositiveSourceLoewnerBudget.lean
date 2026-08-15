import GaloisForLFunctions.RHTower.SourceRecession
import Mathlib.LinearAlgebra.BilinearForm.Properties

/-!
# Positive source weights and fixed Loewner budgets

For arbitrary source types, this module separates cone positivity from a fixed
Loewner upper budget.  Unbounded finitely supported nonnegative weights force
every positive-semidefinite source kernel to vanish.  Under a positive total
mass cap, the budget is equivalent to pointwise domination at that cap.
-/

namespace GaloisForLFunctions

noncomputable section

variable {X V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The bilinear form assembled from finitely supported source weights. -/
def positiveSourceWeighted (K : X → LinearMap.BilinForm ℝ V) (w : X →₀ ℝ) :
    LinearMap.BilinForm ℝ V :=
  w.sum fun x a => a • K x

/-- Total mass of a finitely supported real source weight. -/
def positiveSourceMass (w : X →₀ ℝ) : ℝ :=
  w.sum fun _ a => a

/-- Loewner order for real bilinear forms, expressed by a positive-semidefinite remainder. -/
def sourceLoewnerLE (A B : LinearMap.BilinForm ℝ V) : Prop :=
  (B - A).IsPosSemidef

theorem positiveSourceWeighted_zero (K : X → LinearMap.BilinForm ℝ V) :
    positiveSourceWeighted K 0 = 0 := by
  simp [positiveSourceWeighted]

theorem positiveSourceMass_zero : positiveSourceMass (0 : X →₀ ℝ) = 0 := by
  simp [positiveSourceMass]

theorem positiveSourceWeighted_add (K : X → LinearMap.BilinForm ℝ V)
    (w z : X →₀ ℝ) :
    positiveSourceWeighted K (w + z) =
      positiveSourceWeighted K w + positiveSourceWeighted K z := by
  classical
  unfold positiveSourceWeighted
  apply Finsupp.sum_add_index
  · intro a _
    simp
  · intro a _ b c
    exact add_smul b c (K a)

theorem positiveSourceMass_add (w z : X →₀ ℝ) :
    positiveSourceMass (w + z) = positiveSourceMass w + positiveSourceMass z := by
  classical
  unfold positiveSourceMass
  apply Finsupp.sum_add_index
  · intro a _
    simp
  · intro _ _ b c
    ring

theorem positiveSourceWeighted_smul (K : X → LinearMap.BilinForm ℝ V)
    (c : ℝ) (w : X →₀ ℝ) :
    positiveSourceWeighted K (c • w) = c • positiveSourceWeighted K w := by
  unfold positiveSourceWeighted
  rw [Finsupp.sum_smul_index (fun i => by simp)]
  rw [Finsupp.smul_sum]
  simp [mul_smul]

theorem positiveSourceMass_smul (c : ℝ) (w : X →₀ ℝ) :
    positiveSourceMass (c • w) = c * positiveSourceMass w := by
  unfold positiveSourceMass
  rw [Finsupp.sum_smul_index (fun _ => by simp)]
  change w.sum (fun _ a => c * a) = c • w.sum (fun _ a => a)
  rw [Finsupp.smul_sum]
  rfl

theorem positiveSourceWeighted_single (K : X → LinearMap.BilinForm ℝ V) (x : X) (a : ℝ) :
    positiveSourceWeighted K (Finsupp.single x a) = a • K x := by
  classical
  unfold positiveSourceWeighted
  rw [Finsupp.sum_single_index]
  simp

theorem positiveSourceMass_single (x : X) (a : ℝ) :
    positiveSourceMass (Finsupp.single x a) = a := by
  classical
  unfold positiveSourceMass
  rw [Finsupp.sum_single_index]
  simp

/-- An unrestricted nonnegative source cone cannot fit below one fixed budget
unless every pointwise positive-semidefinite source kernel is zero. -/
theorem positiveSource_unbounded_budget_forces_zero
    (B : LinearMap.BilinForm ℝ V) (K : X → LinearMap.BilinForm ℝ V)
    (hK : ∀ x, (K x).IsPosSemidef)
    (hbudget : ∀ w : X →₀ ℝ, (∀ x, 0 ≤ w x) →
      sourceLoewnerLE (positiveSourceWeighted K w) B) :
    ∀ x, K x = 0 := by
  intro x
  have hrec : ∀ v : V, 0 ≤ -(K x v v) :=
    source_budget_one_sided_recession_nonnegative (fun v => B v v) (fun _ => 0)
      (fun v => -(K x v v)) (by
        intro t ht v
        have hw : ∀ y, 0 ≤ (Finsupp.single x t : X →₀ ℝ) y := by
          intro y
          by_cases h : y = x
          · subst y
            simp [ht]
          · simp [h]
        have h := hbudget (Finsupp.single x t) hw
        change (B - positiveSourceWeighted K (Finsupp.single x t)).IsPosSemidef at h
        rw [positiveSourceWeighted_single] at h
        have hdiag := h.isNonneg.nonneg v
        have hrewrite : (B - t • K x) v v = B v v + t * -(K x v v) := by
          simp only [LinearMap.sub_apply, LinearMap.smul_apply]
          ring
        rw [hrewrite] at hdiag
        simpa using hdiag)
  apply LinearMap.BilinForm.ext_of_isSymm (hK x).isSymm LinearMap.BilinForm.isSymm_zero
  intro v
  have hpos : 0 ≤ K x v v := by
    simpa using (hK x).isNonneg.nonneg v
  have hneg := hrec v
  have hzero : K x v v = 0 := by linarith
  simp [hzero]

theorem positiveSourceWeighted_isSymm (K : X → LinearMap.BilinForm ℝ V)
    (hK : ∀ x, (K x).IsSymm) (w : X →₀ ℝ) :
    (positiveSourceWeighted K w).IsSymm := by
  classical
  induction w using Finsupp.induction with
  | zero => simp [positiveSourceWeighted_zero]
  | single_add x a w hx ha hw =>
      rw [positiveSourceWeighted_add, positiveSourceWeighted_single]
      exact (hK x).smul a |>.add hw

theorem positiveSourceWeighted_isPosSemidef (K : X → LinearMap.BilinForm ℝ V)
    (hK : ∀ x, (K x).IsPosSemidef) (w : X →₀ ℝ)
    (hw : ∀ x, 0 ≤ w x) :
    (positiveSourceWeighted K w).IsPosSemidef := by
  classical
  revert hw
  induction w using Finsupp.induction with
  | zero =>
      intro _
      simp [positiveSourceWeighted_zero]
  | single_add x a w hx ha ih =>
      intro hw
      have hxzero : w x = 0 := by simpa using hx
      have ha_nonneg : 0 ≤ a := by
        have h := hw x
        simpa [Finsupp.add_apply, hxzero] using h
      have hw_nonneg : ∀ y, 0 ≤ w y := by
        intro y
        have h := hw y
        by_cases hxy : y = x
        · subst y
          rw [hxzero]
        · simp [Finsupp.add_apply, hxy] at h
          exact h
      rw [positiveSourceWeighted_add, positiveSourceWeighted_single]
      exact ((hK x).smul ha_nonneg).add (ih hw_nonneg)

theorem positiveSourceWeighted_sub_smul (B : LinearMap.BilinForm ℝ V)
    (K : X → LinearMap.BilinForm ℝ V) (C : ℝ) (w : X →₀ ℝ) :
    positiveSourceWeighted (fun x => B - C • K x) w =
      positiveSourceMass w • B - C • positiveSourceWeighted K w := by
  classical
  induction w using Finsupp.induction with
  | zero =>
      simp only [positiveSourceWeighted_zero, positiveSourceMass_zero, zero_smul, smul_zero]
      exact (sub_zero (0 : LinearMap.BilinForm ℝ V)).symm
  | single_add x a w hx ha ih =>
      rw [positiveSourceWeighted_add, positiveSourceWeighted_single,
        positiveSourceMass_add, positiveSourceMass_single,
        positiveSourceWeighted_add, positiveSourceWeighted_single, ih]
      ext v u
      simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply]
      ring

/-- Exact normalized decomposition of the fixed budget remainder. -/
theorem normalizedSource_decomposition (B : LinearMap.BilinForm ℝ V)
    (K : X → LinearMap.BilinForm ℝ V) (C : ℝ) (hC : C ≠ 0) (w : X →₀ ℝ) :
    B - positiveSourceWeighted K w =
      (1 - C⁻¹ * positiveSourceMass w) • B +
        positiveSourceWeighted (fun x => B - C • K x) (C⁻¹ • w) := by
  rw [positiveSourceWeighted_smul, positiveSourceWeighted_sub_smul]
  ext v u
  simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply]
  change (B v) u - (positiveSourceWeighted K w v) u =
    (1 - C⁻¹ * positiveSourceMass w) * (B v) u +
      C⁻¹ * (positiveSourceMass w * (B v) u - C * (positiveSourceWeighted K w v) u)
  calc
    (B v) u - (positiveSourceWeighted K w v) u =
        (B v) u - (C⁻¹ * C) * (positiveSourceWeighted K w v) u := by
          rw [inv_mul_cancel₀ hC]
          ring
    _ = (1 - C⁻¹ * positiveSourceMass w) * (B v) u +
        C⁻¹ * (positiveSourceMass w * (B v) u - C * (positiveSourceWeighted K w v) u) := by
          ring

theorem positiveSource_normalized_budget_of_pointwise
    (B : LinearMap.BilinForm ℝ V) (K : X → LinearMap.BilinForm ℝ V) (C : ℝ)
    (hC : 0 < C) (hB : B.IsPosSemidef)
    (hpoint : ∀ x, sourceLoewnerLE (C • K x) B)
    (w : X →₀ ℝ) (hw : ∀ x, 0 ≤ w x) (hmass : positiveSourceMass w ≤ C) :
    sourceLoewnerLE (positiveSourceWeighted K w) B := by
  have hCne : C ≠ 0 := ne_of_gt hC
  have hCinv_nonneg : 0 ≤ C⁻¹ := inv_nonneg.mpr hC.le
  have hCinvC : C⁻¹ * C = 1 := inv_mul_cancel₀ hCne
  have hscaled_mass : C⁻¹ * positiveSourceMass w ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left hmass hCinv_nonneg
    simpa [hCinvC] using h
  have hBcoeff : ((1 - C⁻¹ * positiveSourceMass w) • B).IsPosSemidef :=
    hB.smul (sub_nonneg.mpr hscaled_mass)
  have hscaled_nonneg : ∀ x, 0 ≤ (C⁻¹ • w : X →₀ ℝ) x := by
    intro x
    simpa [smul_eq_mul] using mul_nonneg hCinv_nonneg (hw x)
  have hpoint' : ∀ x, (B - C • K x).IsPosSemidef := by
    intro x
    exact hpoint x
  have hsum := positiveSourceWeighted_isPosSemidef
    (fun x => B - C • K x) hpoint' (C⁻¹ • w) hscaled_nonneg
  unfold sourceLoewnerLE
  rw [normalizedSource_decomposition B K C hCne w]
  exact hBcoeff.add hsum

theorem positiveSource_pointwise_of_normalized_budget
    (B : LinearMap.BilinForm ℝ V) (K : X → LinearMap.BilinForm ℝ V) (C : ℝ)
    (hC : 0 < C)
    (hbudget : ∀ w : X →₀ ℝ, (∀ x, 0 ≤ w x) → positiveSourceMass w ≤ C →
      sourceLoewnerLE (positiveSourceWeighted K w) B) :
    ∀ x, sourceLoewnerLE (C • K x) B := by
  intro x
  have hw : ∀ y, 0 ≤ (Finsupp.single x C : X →₀ ℝ) y := by
    intro y
    by_cases hxy : y = x
    · subst y
      simp [hC.le]
    · simp [hxy]
  have hmass : positiveSourceMass (Finsupp.single x C : X →₀ ℝ) ≤ C := by
    rw [positiveSourceMass_single]
  have h := hbudget (Finsupp.single x C) hw hmass
  simpa only [positiveSourceWeighted_single] using h

/-- A positive mass cap turns uniform source budgeting exactly into pointwise
Loewner domination at that cap. -/
theorem positiveSource_normalized_budget_iff
    (B : LinearMap.BilinForm ℝ V) (K : X → LinearMap.BilinForm ℝ V) (C : ℝ)
    (hC : 0 < C) (hB : B.IsPosSemidef) :
    (∀ w : X →₀ ℝ, (∀ x, 0 ≤ w x) → positiveSourceMass w ≤ C →
      sourceLoewnerLE (positiveSourceWeighted K w) B) ↔
      ∀ x, sourceLoewnerLE (C • K x) B := by
  constructor
  · exact positiveSource_pointwise_of_normalized_budget B K C hC
  · intro hpoint w hw hmass
    exact positiveSource_normalized_budget_of_pointwise B K C hC hB hpoint w hw hmass

end

end GaloisForLFunctions
