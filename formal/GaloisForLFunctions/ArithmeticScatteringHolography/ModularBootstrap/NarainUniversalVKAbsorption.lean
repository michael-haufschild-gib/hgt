import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainVKAbsorption

/-!
# Universal arithmetic saving after the fixed width ceiling disappears

Every positive fixed ceiling eventually exceeds the shrinking arithmetic
width. The doubled-height comparison and polynomial absorption then give
the explicit exponent one over 128, independent of target parameters.
-/

open RHTower Filter Topology
open GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap

/-- Every fixed positive ceiling becomes inactive in the shrinking arithmetic width. -/
theorem eventually_narainVKWidth_eq_raw {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ L : ℝ in atTop, narainVKWidth δ L = vkHadamardWidth (2 * L + 1) / 8 := by
  let A : ℝ := Real.exp (max (Real.exp 1) ((10 ^ 8 * min δ 1) ^ (-(3 : ℝ) / 2)))
  filter_upwards [eventually_ge_atTop (max A 0)] with L hL
  have hA : A ≤ L := (le_max_left _ _).trans hL
  have hL0 : 0 ≤ L := (le_max_right _ _).trans hL
  have hw : vkHadamardWidth (2 * L + 1) ≤ min δ 1 :=
    vkHadamardWidth_le (lt_min hδ zero_lt_one) (by change A ≤ _; linarith only [hA, hL0])
  rw [narainVKWidth, min_eq_right hw]

/-- The retained fraction of the arithmetic profile is eventually independent of the fixed ceiling. -/
theorem eventually_narainVKWidth_ge_universal {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ L : ℝ in atTop, vkHadamardWidth L / 64 ≤ narainVKWidth δ L := by
  filter_upwards [eventually_narainVKWidth_eq_raw hδ,
    eventually_ge_atTop (Real.exp (Real.exp 1))] with L heq hL
  rw [heq]
  have h := vkHadamardWidth_double_add_one_ge hL
  linarith only [h]

/-- Polynomial contour losses preserve the explicit universal exponent one over 128. -/
theorem exists_narainVK_saving_universal {δ : ℝ} (hδ : 0 < δ) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ L : ℝ in atTop,
      (1 + L) ^ N * narainVKCost L *
        (Real.exp (-(narainVKWidth δ L * L)) + Real.exp (-(Real.pi * L / 4))) ≤
          C * Real.exp (-(L * vkHadamardWidth L / 128)) := by
  let D : ℝ := 2 ^ N * 3 ^ (7 : ℕ) * 2 ^ (14 : ℕ)
  have hD : 0 < D := by dsimp only [D]; positivity
  refine ⟨2 * D, by positivity, ?_⟩
  filter_upwards [eventually_narainVKCost_polynomial N,
    eventually_pow_le_exp_narainVKWidth hδ (N + 14),
    eventually_narainVKWidth_ge_universal hδ,
    eventually_ge_atTop (Real.exp (Real.exp 1))] with L hcost hpow hwidth hL
  have hL0 : 0 < L := (Real.exp_pos _).trans_le hL
  have hd8 : narainVKWidth δ L ≤ 1 / 8 := by
    unfold narainVKWidth
    exact div_le_div_of_nonneg_right ((min_le_left _ _).trans (min_le_right δ 1)) (by norm_num)
  have htail : Real.exp (-(Real.pi * L / 4)) ≤ Real.exp (-(narainVKWidth δ L * L)) := by
    apply Real.exp_le_exp.mpr
    nlinarith only [hd8, Real.pi_gt_three, hL0]
  have hexp : Real.exp (narainVKWidth δ L * L / 2) *
      Real.exp (-(narainVKWidth δ L * L)) = Real.exp (-(narainVKWidth δ L * L / 2)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hprofile : Real.exp (-(narainVKWidth δ L * L / 2)) ≤
      Real.exp (-(L * vkHadamardWidth L / 128)) := by
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_right hwidth (show 0 ≤ L / 2 by positivity)
    nlinarith only [h]
  change (1 + L) ^ N * narainVKCost L ≤ D * L ^ (N + 14) at hcost
  calc
    _ ≤ (D * L ^ (N + 14)) *
        (Real.exp (-(narainVKWidth δ L * L)) + Real.exp (-(narainVKWidth δ L * L))) :=
      mul_le_mul hcost (add_le_add le_rfl htail) (by positivity) (by positivity)
    _ = 2 * D * L ^ (N + 14) * Real.exp (-(narainVKWidth δ L * L)) := by ring
    _ ≤ 2 * D * Real.exp (narainVKWidth δ L * L / 2) *
        Real.exp (-(narainVKWidth δ L * L)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (by positivity)) (Real.exp_nonneg _)
    _ = 2 * D * Real.exp (-(narainVKWidth δ L * L / 2)) := by rw [mul_assoc, hexp]
    _ ≤ _ := mul_le_mul_of_nonneg_left hprofile (by positivity)

#print axioms eventually_narainVKWidth_eq_raw
#print axioms eventually_narainVKWidth_ge_universal
#print axioms exists_narainVK_saving_universal
end GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
