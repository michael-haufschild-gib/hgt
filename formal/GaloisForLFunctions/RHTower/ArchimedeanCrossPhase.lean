import GaloisForLFunctions.RHTower.DirichletCrossOscillatoryBound
import GaloisForLFunctions.RHTower.HardyPhaseCellCancellation
import GaloisForLFunctions.RHTower.TrigammaVerticalLowerBound

/-!
# The archimedean cross phase of the mollified second moment

The cross term of Levinson's mollified mean square carries the Riemann–Siegel phase `2θ(τ)` of
`χ`.  Its derivative is `2·gammaHardyPhaseRate τ = log(τ/2π) + O(1/τ)` and is strictly increasing,
so the first-derivative test applies with the frequency lower bound of `log_freq_lower_bound`.

The result: as long as the total Dirichlet length `x` satisfies `2π·x·K ≤ a` — which for
`x ≍ T^{1/2+θ}` and `a ≍ T` means `K ≍ T^{1/2−θ}` — the whole cross term is at most
`(ℓ¹ mass)·(ℓ¹ mass)·2/(log K − O(1/a))`.
-/

open Complex MeasureTheory Set intervalIntegral
open scoped Interval

noncomputable section

namespace RHTower

/-- **The archimedean cross bound.** -/
theorem norm_integral_archimedeanCross_le
    {a b x K : ℝ} (ha : 4 ≤ a) (hab : a ≤ b) (hK : 0 < K)
    (e f : ℕ → ℂ) (S T : Finset ℕ)
    (hS : ∀ m ∈ S, 1 ≤ m ∧ (m : ℝ) ≤ x) (hT : ∀ n ∈ T, 1 ≤ n)
    (hgap : 2 * Real.pi * x * K ≤ a)
    (hlam : 0 < Real.log K - (33 / (8 * a ^ 2) + Real.pi / a)) :
    ‖∫ τ in a..b,
        (∑ m ∈ S, e m * Complex.exp (((-(Real.log m) * τ : ℝ) : ℂ) * I))
          * (starRingEnd ℂ) (∑ n ∈ T, f n * Complex.exp (((-(Real.log n) * τ : ℝ) : ℂ) * I))
          * Complex.exp ((((2 * gammaHardyTheta τ : ℝ)) : ℂ) * I)‖
      ≤ (∑ m ∈ S, ‖e m‖) * (∑ n ∈ T, ‖f n‖) *
          (2 / (Real.log K - (33 / (8 * a ^ 2) + Real.pi / a))) := by
  classical
  set lam : ℝ := Real.log K - (33 / (8 * a ^ 2) + Real.pi / a) with hlamdef
  have huIcc : Set.uIcc a b = Set.Icc a b := uIcc_of_le hab
  have hmemA : ∀ τ ∈ Set.uIcc a b, a ≤ τ := by
    intro τ hτ
    rw [huIcc] at hτ
    exact hτ.1
  have hmem : ∀ τ ∈ Set.uIcc a b, 4 ≤ τ := by
    intro τ hτ
    linarith [hmemA τ hτ]
  refine norm_integral_dirichletCross_cexp_le (lam := lam) hab hlam e f S T
    (g := fun τ => 2 * gammaHardyTheta τ)
    (g' := fun τ => 2 * gammaHardyPhaseRate τ)
    (g'' := fun τ => 2 * deriv gammaHardyPhaseRate τ) ?_ ?_ ?_ ?_ ?_
  · intro τ _
    exact (hasDerivAt_gammaHardyTheta τ).const_mul 2
  · intro τ _
    have hd := hasDerivAt_gammaHardyPhaseRate τ
    have hval : deriv gammaHardyPhaseRate τ = -(deriv Complex.digamma (linePt τ / 2)).im / 4 :=
      hd.deriv
    rw [hval]
    exact hd.const_mul 2
  · exact (continuous_deriv_gammaHardyPhaseRate.const_mul 2).continuousOn
  · intro τ hτ
    have hτ0 : (0 : ℝ) < τ := by linarith [hmem τ hτ]
    have hpos := deriv_gammaHardyPhaseRate_pos hτ0
    linarith
  · intro m hm n hn τ hτ
    obtain ⟨hm1, hmx⟩ := hS m hm
    have hτ4 : (4 : ℝ) ≤ τ := hmem τ hτ
    have hτ0 : (0 : ℝ) < τ := by linarith
    have hfreq : Real.log K
        ≤ Real.log (τ / (2 * Real.pi)) + (Real.log n - Real.log m) := by
      refine log_freq_lower_bound hm1 (hT n hn) hmx hK ?_
      linarith [hgap, hmemA τ hτ]
    have hrate := gammaHardyPhaseRate_sub_log_conductor_bound hτ0
    have habs := abs_le.mp hrate
    have hmono1 : (33 : ℝ) / (16 * τ ^ 2) ≤ 33 / (16 * a ^ 2) := by
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      nlinarith [ha, hmemA τ hτ]
    have hmono2 : Real.pi / (2 * τ) ≤ Real.pi / (2 * a) := by
      apply div_le_div_of_nonneg_left Real.pi_pos.le (by positivity)
      linarith [hmemA τ hτ]
    have hstep : Real.log (τ / (2 * Real.pi)) - (33 / (8 * a ^ 2) + Real.pi / a)
        ≤ 2 * gammaHardyPhaseRate τ := by
      have h2 : (2 : ℝ) * (33 / (16 * a ^ 2) + Real.pi / (2 * a))
          = 33 / (8 * a ^ 2) + Real.pi / a := by
        field_simp
        ring
      linarith [habs.1, hmono1, hmono2, h2]
    rw [hlamdef]
    linarith [hfreq, hstep]

end RHTower

end
