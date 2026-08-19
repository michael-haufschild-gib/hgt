import GaloisForLFunctions.HTGeometry.GammaVerticalStripDecay
import GaloisForLFunctions.HTGeometry.GammaScaleVerticalDecay

/-!
# A quantitative exponential bound for a scaled Gamma factor

`Γ(λ(σ+it)+μ)` sits on the vertical line of abscissa `λσ + Re μ` at height `λt + Im μ`, so the
corpus's uniform strip decay gives it an exponential bound with rate proportional to the scale.  The
rate is what lets an exponentially small Gamma product beat the algebraic-logarithmic growth of the
coefficient field.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology

noncomputable section

/-- **A scaled shifted Gamma factor is exponentially small along a vertical line.** -/
theorem exists_exponential_bound_gammaScale {lam σ : ℝ} (hlam : 0 < lam) {μ : ℂ}
    (hσ : 0 < lam * σ + μ.re) :
    ∃ (C δ : ℝ) (N : ℕ), 0 ≤ C ∧ 0 < δ ∧ ∀ᶠ t : ℝ in atTop,
      ‖Complex.Gamma ((lam : ℂ) * ((σ : ℂ) + (t : ℂ) * Complex.I) + μ)‖
        ≤ C * t ^ N * Real.exp (-(δ * t)) := by
  obtain ⟨C, N, hC0, hC⟩ :=
    exists_bound_norm_Gamma_vertical_strip (a := lam * σ + μ.re) hσ (lam * σ + μ.re)
  refine ⟨C * (2 * lam) ^ N, Real.pi * lam / 4, N, by positivity, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop ((2 * |μ.im| + 2) / lam), eventually_ge_atTop (1 : ℝ)]
    with t ht ht1
  have htpos : (0 : ℝ) < t := by linarith
  have ht' : 2 * |μ.im| + 2 ≤ t * lam := by
    rw [div_le_iff₀ hlam] at ht
    exact ht
  have habs0 : (0 : ℝ) ≤ |μ.im| := abs_nonneg _
  have hlow : |μ.im| ≤ lam * t / 2 := by nlinarith
  have hhalf : lam * t / 2 ≤ lam * t + μ.im := by
    have := neg_abs_le μ.im
    linarith
  have habs : lam * t / 2 ≤ |lam * t + μ.im| := le_trans hhalf (le_abs_self _)
  have habs' : |lam * t + μ.im| ≤ 2 * lam * t := by
    have h1 : |lam * t + μ.im| ≤ |lam * t| + |μ.im| := abs_add_le _ _
    have h2 : |lam * t| = lam * t := abs_of_pos (by positivity)
    rw [h2] at h1
    linarith
  have hone : (1 : ℝ) ≤ |lam * t + μ.im| := by nlinarith
  have hb := hC (lam * σ + μ.re) (lam * t + μ.im) le_rfl le_rfl hone
  rw [gammaScale_arg_eq]
  refine hb.trans ?_
  have hexp : Real.exp (-(Real.pi * |lam * t + μ.im| / 2))
      ≤ Real.exp (-(Real.pi * lam / 4 * t)) := by
    refine Real.exp_le_exp.mpr ?_
    have hpi := Real.pi_pos
    nlinarith [habs]
  have hpow : C * |lam * t + μ.im| ^ N ≤ C * (2 * lam) ^ N * t ^ N := by
    have h1 : |lam * t + μ.im| ^ N ≤ (2 * lam * t) ^ N :=
      pow_le_pow_left₀ (abs_nonneg _) habs' N
    have h2 : (2 * lam * t) ^ N = (2 * lam) ^ N * t ^ N := by
      rw [mul_pow]
    rw [h2] at h1
    have := mul_le_mul_of_nonneg_left h1 hC0
    linarith [this]
  have hnn : (0 : ℝ) ≤ C * |lam * t + μ.im| ^ N := by positivity
  have hfin := mul_le_mul hpow hexp (Real.exp_nonneg _) (by positivity)
  linarith [hfin]

end

end GaloisForLFunctions.HTGeometry
