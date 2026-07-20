import GaloisForLFunctions.RHTower.ProjectiveWeightedCoherence

/-!
# Exact projective reverse-water-filling optimizer

This file proves the finite convex optimization statement behind weighted
projective coherence.  The water-filled coordinate scales are feasible and
minimize the logarithmic resolution cost among all feasible anisotropic
resolutions.
-/

open scoped BigOperators

noncomputable section

namespace RHTower

/-- The coordinate scale selected by a projective water level. -/
def projectiveWaterScale {d : ℕ} (w : Fin d → ℝ) (k : Fin d)
    (lam : ℝ) (j : Fin d) : ℝ :=
  if j = k then 1 else max 1 (lam * w j)

/-- Feasibility for the projective reciprocal-mass constraint. -/
def ProjectiveWaterFeasible {d : ℕ} (w : Fin d → ℝ) (k : Fin d)
    (eta : ℝ) (x : Fin d → ℝ) : Prop :=
  (∀ j, 1 ≤ x j) ∧
    (∑ j, if j = k then 0 else w j / x j) ≤ eta

/-- Logarithmic projective resolution cost. -/
def projectiveCoordinateEntropy {d : ℕ} (k : Fin d)
    (x : Fin d → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ j, if j = k then 0 else Real.log (x j)

/-- Reciprocal mass at the water-filled scale is exactly the clipped mass. -/
theorem div_max_one_mul_eq_min_inv
    {a lam : ℝ} (ha : 0 ≤ a) (hlam : 0 < lam) :
    a / max 1 (lam * a) = min a lam⁻¹ := by
  by_cases h : lam * a ≤ 1
  · have hainv : a ≤ lam⁻¹ := by
      simpa using (le_inv_mul_iff₀ hlam).2 h
    rw [max_eq_left h, min_eq_left hainv, div_one]
  · have hactive : 1 ≤ lam * a := (le_of_lt (lt_of_not_ge h))
    have ha0 : 0 < a := by
      by_contra ha0
      have : a = 0 := le_antisymm (le_of_not_gt ha0) ha
      subst a
      norm_num at hactive
    have hinv : lam⁻¹ ≤ a := by
      exact (inv_le_iff_one_le_mul₀' hlam).2 hactive
    rw [max_eq_right hactive, min_eq_right hinv]
    field_simp

/-- The logarithmic cost lies above its water-level supporting line. -/
theorem log_max_one_mul_add_water_support_le_log
    {a lam x : ℝ} (ha : 0 ≤ a) (hlam : 0 < lam) (hx : 1 ≤ x) :
    Real.log (max 1 (lam * a)) +
        lam * (min a lam⁻¹ - a / x) ≤ Real.log x := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  by_cases h : lam * a ≤ 1
  · have hainv : a ≤ lam⁻¹ := by
      simpa using (le_inv_mul_iff₀ hlam).2 h
    rw [max_eq_left h, min_eq_left hainv, Real.log_one, zero_add]
    have hinv : x⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hx
    have hgap : 0 ≤ 1 - x⁻¹ := sub_nonneg.mpr hinv
    have hlamA0 : 0 ≤ lam * a := mul_nonneg hlam.le ha
    have hscaled : (lam * a) * (1 - x⁻¹) ≤ 1 - x⁻¹ := by
      nlinarith
    have hlog := Real.one_sub_inv_le_log_of_pos hx0
    calc
      lam * (a - a / x) = (lam * a) * (1 - x⁻¹) := by
        field_simp
      _ ≤ 1 - x⁻¹ := hscaled
      _ ≤ Real.log x := hlog
  · have hactive : 1 ≤ lam * a := le_of_lt (lt_of_not_ge h)
    have ha0 : 0 < a := by
      by_contra ha0
      have : a = 0 := le_antisymm (le_of_not_gt ha0) ha
      subst a
      norm_num at hactive
    have hinv : lam⁻¹ ≤ a := by
      exact (inv_le_iff_one_le_mul₀' hlam).2 hactive
    rw [max_eq_right hactive, min_eq_right hinv]
    have hratio : 0 < (lam * a) / x := div_pos (mul_pos hlam ha0) hx0
    have hlog := Real.log_le_sub_one_of_pos hratio
    rw [Real.log_div (mul_pos hlam ha0).ne' hx0.ne'] at hlog
    rw [mul_sub, mul_inv_cancel₀ hlam.ne']
    calc
      Real.log (lam * a) + (1 - lam * (a / x)) =
          Real.log (lam * a) + (1 - (lam * a) / x) := by ring
      _ ≤ Real.log x := by linarith

theorem projectiveWaterScale_ge_one
    {d : ℕ} (w : Fin d → ℝ) (k : Fin d) (lam : ℝ) :
    ∀ j, 1 ≤ projectiveWaterScale w k lam j := by
  intro j
  by_cases hj : j = k
  · simp [projectiveWaterScale, hj]
  · simp [projectiveWaterScale, hj]

theorem projectiveWaterScale_reciprocalMass
    {d : ℕ} (w : Fin d → ℝ) (k : Fin d) (lam : ℝ)
    (hw : ∀ j, 0 ≤ w j) (hlam : 0 < lam) :
    (∑ j, if j = k then 0 else
        w j / projectiveWaterScale w k lam j) =
      projectiveWaterMass w k lam := by
  rw [projectiveWaterMass]
  apply Finset.sum_congr rfl
  intro j _hj
  by_cases hjk : j = k
  · simp [hjk]
  · simp only [hjk, ↓reduceIte, projectiveWaterScale]
    exact div_max_one_mul_eq_min_inv (hw j) hlam

theorem projectiveWaterScale_feasible
    {d : ℕ} (w : Fin d → ℝ) (k : Fin d) {lam eta : ℝ}
    (hw : ∀ j, 0 ≤ w j) (hlam : 0 < lam)
    (hlevel : projectiveWaterMass w k lam = eta) :
    ProjectiveWaterFeasible w k eta
      (projectiveWaterScale w k lam) := by
  constructor
  · exact projectiveWaterScale_ge_one w k lam
  · rw [projectiveWaterScale_reciprocalMass w k lam hw hlam, hlevel]

theorem projectiveCoordinateEntropy_waterScale
    {d : ℕ} (w : Fin d → ℝ) (k : Fin d) (lam : ℝ) :
    projectiveCoordinateEntropy k (projectiveWaterScale w k lam) =
      projectiveWaterEntropyAt w k lam := by
  rw [projectiveCoordinateEntropy, projectiveWaterEntropyAt]
  congr 1
  apply Finset.sum_congr rfl
  intro j _hj
  by_cases hjk : j = k
  · simp [hjk]
  · simp [projectiveWaterScale, hjk]

/-- **Exact reverse-water-filling optimality.**  At a positive level solving
the reciprocal-mass equation, the water-filled scales minimize logarithmic
projective resolution cost among all feasible coordinate scales. -/
theorem projectiveWaterEntropyAt_le_of_feasible
    {d : ℕ} (w : Fin d → ℝ) (k : Fin d) {lam eta : ℝ}
    (hw : ∀ j, 0 ≤ w j) (hlam : 0 < lam)
    (hlevel : projectiveWaterMass w k lam = eta)
    (x : Fin d → ℝ) (hx : ProjectiveWaterFeasible w k eta x) :
    projectiveWaterEntropyAt w k lam ≤
      projectiveCoordinateEntropy k x := by
  have hterm : ∀ j,
      (if j = k then 0 else Real.log (max 1 (lam * w j))) +
          lam * ((if j = k then 0 else min (w j) lam⁻¹) -
            (if j = k then 0 else w j / x j)) ≤
        if j = k then 0 else Real.log (x j) := by
    intro j
    by_cases hjk : j = k
    · simp [hjk]
    · simpa only [hjk, ↓reduceIte] using
        log_max_one_mul_add_water_support_le_log
          (hw j) hlam (hx.1 j)
  have hsum := Finset.sum_le_sum (s := Finset.univ)
    (fun j _hj ↦ hterm j)
  have hmassRewrite :
      (∑ j, if j = k then 0 else min (w j) lam⁻¹) = eta := by
    simpa only [projectiveWaterMass] using hlevel
  have hconstraint :
      (∑ j, if j = k then 0 else w j / x j) ≤ eta := hx.2
  have hlogs :
      (∑ j, if j = k then 0 else Real.log (max 1 (lam * w j))) ≤
        ∑ j, if j = k then 0 else Real.log (x j) := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum,
      Finset.sum_sub_distrib] at hsum
    rw [hmassRewrite] at hsum
    have hcorrection :
        0 ≤ lam * (eta - ∑ j, if j = k then 0 else w j / x j) :=
      mul_nonneg hlam.le (sub_nonneg.mpr hconstraint)
    linarith
  rw [projectiveWaterEntropyAt, projectiveCoordinateEntropy]
  exact mul_le_mul_of_nonneg_left hlogs (by norm_num)

/-- The water-filled scale is feasible and attains the minimum cost. -/
theorem projectiveWaterScale_isMinimizer
    {d : ℕ} (w : Fin d → ℝ) (k : Fin d) {lam eta : ℝ}
    (hw : ∀ j, 0 ≤ w j) (hlam : 0 < lam)
    (hlevel : projectiveWaterMass w k lam = eta) :
    ProjectiveWaterFeasible w k eta
        (projectiveWaterScale w k lam) ∧
      ∀ x, ProjectiveWaterFeasible w k eta x →
        projectiveCoordinateEntropy k
            (projectiveWaterScale w k lam) ≤
          projectiveCoordinateEntropy k x := by
  constructor
  · exact projectiveWaterScale_feasible w k hw hlam hlevel
  · intro x hx
    rw [projectiveCoordinateEntropy_waterScale]
    exact projectiveWaterEntropyAt_le_of_feasible
      w k hw hlam hlevel x hx

end RHTower
