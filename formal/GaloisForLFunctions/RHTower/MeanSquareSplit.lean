import Mathlib

/-!
# Splitting a mean square into two pieces and their cross

Levinson's mollified mean square is the mean square of `A·Ψ + χ·B·Ψ` (direct plus dual), so it
splits into the two mean squares plus twice the real part of the cross.  This file records the
elementary splitting inequality in exactly the form the assembly consumes: two mean-square upper
bounds and one cross bound give an upper bound for the whole.
-/

open Complex MeasureTheory intervalIntegral Set

noncomputable section

namespace RHTower

/-- **The two-term mean-square split.** -/
theorem integral_normSq_add_le_of_cross
    {a b P₁ P₂ X : ℝ} {D₁ D₂ : ℝ → ℂ}
    (hc₁ : Continuous D₁) (hc₂ : Continuous D₂)
    (h₁ : (∫ τ in a..b, ‖D₁ τ‖ ^ 2) ≤ P₁)
    (h₂ : (∫ τ in a..b, ‖D₂ τ‖ ^ 2) ≤ P₂)
    (hX : ‖∫ τ in a..b, D₁ τ * (starRingEnd ℂ) (D₂ τ)‖ ≤ X) :
    (∫ τ in a..b, ‖D₁ τ + D₂ τ‖ ^ 2) ≤ P₁ + P₂ + 2 * X := by
  classical
  have hpt : ∀ τ : ℝ, ‖D₁ τ + D₂ τ‖ ^ 2
      = ‖D₁ τ‖ ^ 2 + ‖D₂ τ‖ ^ 2 + 2 * (D₁ τ * (starRingEnd ℂ) (D₂ τ)).re := by
    intro τ
    have h := Complex.normSq_add (D₁ τ) (D₂ τ)
    have e1 : Complex.normSq (D₁ τ + D₂ τ) = ‖D₁ τ + D₂ τ‖ ^ 2 :=
      Complex.normSq_eq_norm_sq _
    have e2 : Complex.normSq (D₁ τ) = ‖D₁ τ‖ ^ 2 := Complex.normSq_eq_norm_sq _
    have e3 : Complex.normSq (D₂ τ) = ‖D₂ τ‖ ^ 2 := Complex.normSq_eq_norm_sq _
    rw [e1, e2, e3] at h
    rw [h]
  have hi1 : IntervalIntegrable (fun τ : ℝ => ‖D₁ τ‖ ^ 2) volume a b :=
    (hc₁.norm.pow 2).intervalIntegrable a b
  have hi2 : IntervalIntegrable (fun τ : ℝ => ‖D₂ τ‖ ^ 2) volume a b :=
    (hc₂.norm.pow 2).intervalIntegrable a b
  have hcprod : Continuous fun τ : ℝ => D₁ τ * (starRingEnd ℂ) (D₂ τ) :=
    hc₁.mul (Complex.continuous_conj.comp hc₂)
  have hi3 : IntervalIntegrable
      (fun τ : ℝ => 2 * (D₁ τ * (starRingEnd ℂ) (D₂ τ)).re) volume a b :=
    ((Complex.continuous_re.comp hcprod).const_mul 2).intervalIntegrable a b
  have hicprod : IntervalIntegrable (fun τ : ℝ => D₁ τ * (starRingEnd ℂ) (D₂ τ)) volume a b :=
    hcprod.intervalIntegrable a b
  rw [intervalIntegral.integral_congr (fun τ _ => hpt τ)]
  rw [intervalIntegral.integral_add (hi1.add hi2) hi3,
    intervalIntegral.integral_add hi1 hi2]
  have hre : (∫ τ in a..b, 2 * (D₁ τ * (starRingEnd ℂ) (D₂ τ)).re)
      = 2 * (∫ τ in a..b, D₁ τ * (starRingEnd ℂ) (D₂ τ)).re := by
    rw [intervalIntegral.integral_const_mul]
    congr 1
    have hcomm := ContinuousLinearMap.intervalIntegral_comp_comm Complex.reCLM hicprod
    simpa using hcomm
  rw [hre]
  have hbound : (∫ τ in a..b, D₁ τ * (starRingEnd ℂ) (D₂ τ)).re ≤ X :=
    le_trans (Complex.re_le_norm _) hX
  linarith


/-- **Absorbing a small perturbation.**  Young's inequality `‖u+v‖² ≤ (1+η)‖u‖² + (1+1/η)‖v‖²`
integrates to the form the assembly uses for the approximate-functional-equation error and the pole
residue: a mean square that is `o(L)` costs only `η` of relative loss. -/
theorem integral_normSq_add_le_young
    {a b P Q η : ℝ} (hab : a ≤ b) (hη : 0 < η) {D E : ℝ → ℂ}
    (hcD : Continuous D) (hcE : Continuous E)
    (hP : (∫ τ in a..b, ‖D τ‖ ^ 2) ≤ P)
    (hQ : (∫ τ in a..b, ‖E τ‖ ^ 2) ≤ Q) :
    (∫ τ in a..b, ‖D τ + E τ‖ ^ 2) ≤ (1 + η) * P + (1 + 1 / η) * Q := by
  classical
  have hiD : IntervalIntegrable (fun τ : ℝ => ‖D τ‖ ^ 2) volume a b :=
    (hcD.norm.pow 2).intervalIntegrable a b
  have hiE : IntervalIntegrable (fun τ : ℝ => ‖E τ‖ ^ 2) volume a b :=
    (hcE.norm.pow 2).intervalIntegrable a b
  have hiS : IntervalIntegrable (fun τ : ℝ => ‖D τ + E τ‖ ^ 2) volume a b :=
    ((hcD.add hcE).norm.pow 2).intervalIntegrable a b
  have hpt : ∀ τ ∈ Set.Icc a b,
      ‖D τ + E τ‖ ^ 2 ≤ (1 + η) * ‖D τ‖ ^ 2 + (1 + 1 / η) * ‖E τ‖ ^ 2 := by
    intro τ _
    have htri : ‖D τ + E τ‖ ≤ ‖D τ‖ + ‖E τ‖ := norm_add_le _ _
    have hnn : (0 : ℝ) ≤ ‖D τ‖ + ‖E τ‖ := by positivity
    have hsq : ‖D τ + E τ‖ ^ 2 ≤ (‖D τ‖ + ‖E τ‖) ^ 2 := by
      exact pow_le_pow_left₀ (norm_nonneg _) htri 2
    have hyoung : 2 * (‖D τ‖ * ‖E τ‖) ≤ η * ‖D τ‖ ^ 2 + (1 / η) * ‖E τ‖ ^ 2 := by
      have hkey : 0 ≤ (Real.sqrt η * ‖D τ‖ - (1 / Real.sqrt η) * ‖E τ‖) ^ 2 := sq_nonneg _
      have hsq1 : Real.sqrt η ^ 2 = η := Real.sq_sqrt hη.le
      have hspos : 0 < Real.sqrt η := Real.sqrt_pos.mpr hη
      have hinv : (1 / Real.sqrt η) ^ 2 = 1 / η := by
        rw [div_pow, one_pow, hsq1]
      have hcross : Real.sqrt η * ‖D τ‖ * ((1 / Real.sqrt η) * ‖E τ‖) = ‖D τ‖ * ‖E τ‖ := by
        field_simp
      nlinarith [hkey, hsq1, hinv, hcross]
    nlinarith [hsq, hyoung]
  have hmono : (∫ τ in a..b, ‖D τ + E τ‖ ^ 2)
      ≤ ∫ τ in a..b, ((1 + η) * ‖D τ‖ ^ 2 + (1 + 1 / η) * ‖E τ‖ ^ 2) := by
    refine intervalIntegral.integral_mono_on hab hiS
      (((hiD.const_mul (1 + η)).add (hiE.const_mul (1 + 1 / η)))) hpt
  rw [intervalIntegral.integral_add (hiD.const_mul (1 + η)) (hiE.const_mul (1 + 1 / η)),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hmono
  have h1 : (1 + η) * (∫ τ in a..b, ‖D τ‖ ^ 2) ≤ (1 + η) * P :=
    mul_le_mul_of_nonneg_left hP (by linarith)
  have h2 : (1 + 1 / η) * (∫ τ in a..b, ‖E τ‖ ^ 2) ≤ (1 + 1 / η) * Q :=
    mul_le_mul_of_nonneg_left hQ (by positivity)
  linarith

end RHTower

end
