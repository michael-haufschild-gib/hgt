import GaloisForLFunctions.RHTower.WardAnnulusCrossKernelWindowMass
import GaloisForLFunctions.HTGeometry.HalfPlanePolePhase
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Baseline cancellation buys no cross-kernel budget

The window mass of a finite Lorentzian cross kernel is an arctangent sum, and every arctangent of a
nonnegative argument lies in `[0, π/2)`.  Hence the mass on any symmetric window is at most `2π`
times the *positive part* of the coefficient family, with no contribution from the negative
coefficients.  Cancelling the width-independent baseline sets the total mass to zero but leaves the
window budget exactly where it was for the positive part alone.

For a two-width annulus the budget at the maximal positivity radius `√(β₀ β₁)` is computed in
closed form: it is `8 arctan √(β₁/β₀) − 2π`, strictly below the single-Lorentzian mass `2π` and
increasing to it only as the width ratio diverges.
-/

open MeasureTheory intervalIntegral
open scoped BigOperators

namespace RHTower

noncomputable section

/-- **Window budget ceiling.**  The cross-kernel mass on a symmetric window is at most `2π` times
the positive part of the coefficient family, whatever the negative coefficients do. -/
theorem intervalIntegral_annulusCrossKernel_le_positivePart {ι : Type*} (S : Finset ι)
    (c b : ι → ℝ) {A ρ : ℝ} (hb : ∀ i ∈ S, 0 < A + b i) (hρ : 0 ≤ ρ) :
    (∫ D in (-ρ)..ρ, annulusCrossKernel S c b A D) ≤
      2 * Real.pi * ∑ i ∈ S, max (c i) 0 := by
  rw [intervalIntegral_annulusCrossKernel S c b hb ρ, Finset.mul_sum]
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i hi => ?_
  have hβ := hb i hi
  have harg : 0 ≤ ρ / (A + b i) := div_nonneg hρ hβ.le
  have hnn : 0 ≤ Real.arctan (ρ / (A + b i)) := Real.arctan_nonneg.mpr harg
  have hlt : Real.arctan (ρ / (A + b i)) < Real.pi / 2 := Real.arctan_lt_pi_div_two _
  have hstep : c i * Real.arctan (ρ / (A + b i)) ≤
      max (c i) 0 * Real.arctan (ρ / (A + b i)) :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) hnn
  have hmax : 0 ≤ max (c i) 0 := le_max_right _ _
  nlinarith [hstep, hmax, hlt, hnn]

/-- With zero total coefficient the ceiling is attained by the positive part alone: baseline
cancellation removes the total mass but not the window budget. -/
theorem intervalIntegral_annulusCrossKernel_le_of_sum_eq_zero {ι : Type*} (S : Finset ι)
    (c b : ι → ℝ) {A ρ : ℝ} (hb : ∀ i ∈ S, 0 < A + b i) (hρ : 0 ≤ ρ)
    (hzero : ∑ i ∈ S, c i = 0) :
    (∫ D in (-ρ)..ρ, annulusCrossKernel S c b A D) ≤
      Real.pi * ∑ i ∈ S, |c i| := by
  have h := intervalIntegral_annulusCrossKernel_le_positivePart S c b hb hρ
  have hsum : 2 * ∑ i ∈ S, max (c i) 0 = ∑ i ∈ S, |c i| := by
    have habs : ∀ i ∈ S, |c i| = 2 * max (c i) 0 - c i := by
      intro i _
      rcases le_total 0 (c i) with hci | hci
      · rw [abs_of_nonneg hci, max_eq_left hci]; ring
      · rw [abs_of_nonpos hci, max_eq_right hci]; ring
    rw [Finset.sum_congr rfl habs, Finset.sum_sub_distrib, hzero, ← Finset.mul_sum]
    ring
  nlinarith [h, hsum, Real.pi_pos]

/-- **Exact two-width budget at the maximal positivity radius.**  Writing the two widths as
`ρ / r` and `ρ * r`, their product is `ρ ^ 2`, so `ρ` is exactly the positivity radius, and the
window budget there is `8 arctan r - 2π`: strictly below the single-Lorentzian mass `2π`, and
reaching it only as the width ratio `r ^ 2` diverges. -/
theorem intervalIntegral_annulusCrossKernel_two_at_radius {A b₀ b₁ ρ r : ℝ}
    (hρ : 0 < ρ) (hr : 0 < r) (h₀ : A + b₀ = ρ / r) (h₁ : A + b₁ = ρ * r) :
    (∫ D in (-ρ)..ρ, annulusCrossKernel Finset.univ ![(1 : ℝ), -1] ![b₀, b₁] A D) =
      8 * Real.arctan r - 2 * Real.pi := by
  have hb₀ : 0 < A + b₀ := by rw [h₀]; positivity
  have hb₁ : 0 < A + b₁ := by rw [h₁]; positivity
  have hb : ∀ i : Fin 2, i ∈ (Finset.univ : Finset (Fin 2)) → 0 < A + ![b₀, b₁] i := by
    intro i _
    fin_cases i
    · simpa using hb₀
    · simpa using hb₁
  rw [intervalIntegral_annulusCrossKernel Finset.univ _ _ hb]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  have e₀ : ρ / (A + b₀) = r := by
    rw [h₀]
    field_simp
  have e₁ : ρ / (A + b₁) = r⁻¹ := by
    rw [h₁]
    field_simp
  rw [e₀, e₁, Real.arctan_inv_of_pos hr]
  ring

/-- Diagonal quantum of the two-width annulus at widths `ρ / r` and `ρ * r`. -/
theorem annulusCrossKernel_two_at_zero {A b₀ b₁ ρ r : ℝ}
    (hρ : 0 < ρ) (hr : 0 < r) (h₀ : A + b₀ = ρ / r) (h₁ : A + b₁ = ρ * r) :
    annulusCrossKernel Finset.univ ![(1 : ℝ), -1] ![b₀, b₁] A 0 =
      2 * r / ρ - 2 / (ρ * r) := by
  simp only [annulusCrossKernel, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [h₀, h₁]
  have hρ' : ρ ≠ 0 := ne_of_gt hρ
  have hr' : r ≠ 0 := ne_of_gt hr
  field_simp
  ring

/-- **Deficit law.**  At the maximal positivity radius the available positive cross mass is at
least the smaller width times the diagonal quantum, once the width ratio is at least four.
Multiplying by the mean zero density therefore charges each zero a cross cost proportional to
`(smaller width) * (density)` against a diagonal gain of one quantum: Euler safety, which keeps the
smaller width bounded below, leaves a deficit of the order of that density. -/
theorem smallWidth_mul_quantum_le_windowBudget {A b₀ b₁ ρ r : ℝ}
    (hρ : 0 < ρ) (hr : 2 ≤ r) (h₀ : A + b₀ = ρ / r) (h₁ : A + b₁ = ρ * r) :
    (ρ / r) * annulusCrossKernel Finset.univ ![(1 : ℝ), -1] ![b₀, b₁] A 0 ≤
      ∫ D in (-ρ)..ρ, annulusCrossKernel Finset.univ ![(1 : ℝ), -1] ![b₀, b₁] A D := by
  have hr0 : (0 : ℝ) < r := by linarith
  rw [annulusCrossKernel_two_at_zero hρ hr0 h₀ h₁,
    intervalIntegral_annulusCrossKernel_two_at_radius hρ hr0 h₀ h₁]
  have hρ' : ρ ≠ 0 := ne_of_gt hρ
  have hr' : r ≠ 0 := ne_of_gt hr0
  have hleft : (ρ / r) * (2 * r / ρ - 2 / (ρ * r)) = 2 - 2 / r ^ (2 : ℕ) := by
    field_simp
  rw [hleft]
  have hinv : Real.arctan r⁻¹ = Real.pi / 2 - Real.arctan r := Real.arctan_inv_of_pos hr0
  have hlt : Real.arctan r⁻¹ < r⁻¹ :=
    GaloisForLFunctions.HTGeometry.arctan_lt_self (by positivity)
  have hinv_le : r⁻¹ ≤ 1 / 2 := by
    rw [inv_le_comm₀ hr0 (by norm_num)]
    linarith
  have harc : Real.pi / 2 - 1 / 2 ≤ Real.arctan r := by
    have : Real.pi / 2 - Real.arctan r < r⁻¹ := by rw [← hinv]; exact hlt
    linarith [hinv_le]
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hsq : (0 : ℝ) < r ^ (2 : ℕ) := by positivity
  have hpos : 0 ≤ 2 / r ^ (2 : ℕ) := by positivity
  linarith [harc, hpi, hpos]

end

end RHTower
