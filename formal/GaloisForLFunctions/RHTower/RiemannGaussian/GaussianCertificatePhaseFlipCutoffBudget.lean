import GaloisForLFunctions.RHTower.RiemannGaussian.GaussianCertificatePhaseFlipDigammaBound

/-!
# Deterministic cutoff cost of a Gaussian phase-flip certificate

The phase-flip law forces a compact certificate to pay an elementary peak.
The preceding module bounds its digamma payment.  Here the remaining finite
prime slope mass is bounded using only the pointwise unconditional estimate
`Λ(n) ≤ log n`.  Thus the certificate's cutoff itself has a fully explicit
budget: `cutoff * log(cutoff)^2`.
-/

open Filter Set

namespace RiemannGaussian
noncomputable section

/-- The logarithmic slope mass of every finite initial prime-power block
is bounded by its deterministic cutoff budget. -/
theorem gaussianPrimePhaseSlopeMass_range_le_cutoff_log_sq
    (cutoff : ℕ) :
    gaussianPrimePhaseSlopeMass (Finset.range cutoff) ≤
      (cutoff : ℝ) * Real.log cutoff ^ 2 := by
  unfold gaussianPrimePhaseSlopeMass
  calc
    ∑ n ∈ Finset.range cutoff,
        ArithmeticFunction.vonMangoldt n / Real.sqrt n * |Real.log n| ≤
      ∑ _n ∈ Finset.range cutoff, Real.log cutoff ^ 2 := by
        apply Finset.sum_le_sum
        intro n hn
        rw [Finset.mem_range] at hn
        by_cases hn0 : n = 0
        · subst n
          norm_num
          exact sq_nonneg (Real.log (cutoff : ℝ))
        · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
          have hn1Nat : 1 ≤ n := hnpos
          have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn1Nat
          have hnposReal : 0 < (n : ℝ) := by exact_mod_cast hnpos
          have hncutNat : n ≤ cutoff := Nat.le_of_lt hn
          have hncut : (n : ℝ) ≤ cutoff := by exact_mod_cast hncutNat
          have hcutpos : 0 < (cutoff : ℝ) := lt_of_lt_of_le hnposReal hncut
          have hlogn : 0 ≤ Real.log n := Real.log_nonneg hn1
          have hlogle : Real.log n ≤ Real.log cutoff :=
            Real.log_le_log hnposReal hncut
          have hsqrt : 1 ≤ Real.sqrt (n : ℝ) := by
            rw [← Real.sqrt_one]
            exact Real.sqrt_le_sqrt hn1
          have hΛ : 0 ≤ ArithmeticFunction.vonMangoldt n := by positivity
          have hdiv : ArithmeticFunction.vonMangoldt n / Real.sqrt n ≤
              ArithmeticFunction.vonMangoldt n := by
            rw [div_eq_mul_inv]
            exact mul_le_of_le_one_right hΛ (inv_le_one_of_one_le₀ hsqrt)
          have hfirst : ArithmeticFunction.vonMangoldt n / Real.sqrt n * |Real.log n| ≤
              ArithmeticFunction.vonMangoldt n * Real.log n := by
            rw [abs_of_nonneg hlogn]
            exact mul_le_mul_of_nonneg_right hdiv hlogn
          calc
            ArithmeticFunction.vonMangoldt n / Real.sqrt n * |Real.log n| ≤
                ArithmeticFunction.vonMangoldt n * Real.log n := hfirst
            _ ≤ Real.log n * Real.log n := by
                exact mul_le_mul_of_nonneg_right ArithmeticFunction.vonMangoldt_le_log hlogn
            _ ≤ Real.log cutoff ^ 2 := by nlinarith
    _ = (cutoff : ℝ) * Real.log cutoff ^ 2 := by simp


/-- A compact phase-flip Gaussian certificate must fund its elementary
peak through an explicit deterministic cutoff budget. -/
theorem GaussianArithmeticWidthCertificate.phaseFlipPeak_sub_explicitDigamma_le_cutoff_log_budget
    {ε : ℝ} (certificate : GaussianArithmeticWidthCertificate ε)
    (hphaseRadius : Real.pi / ε ≤ certificate.compactRadius) :
    4 * Real.exp (ε / 4) +
        4 * Real.exp (ε / 4 - Real.pi ^ 2 / ε) -
      2 / Real.sqrt (Real.pi * ε) *
        ((3 / 2 : ℝ) * |Real.pi / ε| +
          (2 / (1 - Real.exp (-2))) * (2 * Real.exp (-(1 / 2 : ℝ)))) ≤
      2 * Real.pi / (ε * Real.sqrt (Real.pi * ε)) *
        ((certificate.cutoff : ℝ) * Real.log certificate.cutoff ^ 2) := by
  calc
    4 * Real.exp (ε / 4) +
          4 * Real.exp (ε / 4 - Real.pi ^ 2 / ε) -
        2 / Real.sqrt (Real.pi * ε) *
          ((3 / 2 : ℝ) * |Real.pi / ε| +
            (2 / (1 - Real.exp (-2))) * (2 * Real.exp (-(1 / 2 : ℝ)))) ≤
        2 * Real.pi / (ε * Real.sqrt (Real.pi * ε)) *
          gaussianPrimePhaseSlopeMass (Finset.range certificate.cutoff) :=
      certificate.phaseFlipPeak_sub_explicitDigamma_le_slopeMass hphaseRadius
    _ ≤ 2 * Real.pi / (ε * Real.sqrt (Real.pi * ε)) *
        ((certificate.cutoff : ℝ) * Real.log certificate.cutoff ^ 2) := by
      apply mul_le_mul_of_nonneg_left
      · exact gaussianPrimePhaseSlopeMass_range_le_cutoff_log_sq certificate.cutoff
      · have hden : 0 < ε * Real.sqrt (Real.pi * ε) := by
          apply mul_pos certificate.width_pos
          exact Real.sqrt_pos.2 (mul_pos Real.pi_pos certificate.width_pos)
        exact div_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) hden.le


/-- Cancelling the positive Gaussian normalization gives a direct lower bound
on the deterministic cutoff budget of every compact phase-flip certificate. -/
theorem GaussianArithmeticWidthCertificate.phaseFlip_cutoff_log_budget_lower
    {ε : ℝ} (certificate : GaussianArithmeticWidthCertificate ε)
    (hphaseRadius : Real.pi / ε ≤ certificate.compactRadius) :
    (ε * Real.sqrt (Real.pi * ε) / (2 * Real.pi)) *
        (4 * Real.exp (ε / 4) +
          4 * Real.exp (ε / 4 - Real.pi ^ 2 / ε) -
          2 / Real.sqrt (Real.pi * ε) *
            ((3 / 2 : ℝ) * |Real.pi / ε| +
              (2 / (1 - Real.exp (-2))) * (2 * Real.exp (-(1 / 2 : ℝ))))) ≤
      (certificate.cutoff : ℝ) * Real.log certificate.cutoff ^ 2 := by
  have hbudget := certificate.phaseFlipPeak_sub_explicitDigamma_le_cutoff_log_budget
    hphaseRadius
  have hscale : 0 ≤ ε * Real.sqrt (Real.pi * ε) / (2 * Real.pi) := by
    have hsqrt : 0 ≤ Real.sqrt (Real.pi * ε) := Real.sqrt_nonneg _
    exact div_nonneg (mul_nonneg certificate.width_pos.le hsqrt)
      (mul_nonneg (by norm_num) Real.pi_pos.le)
  have hmul := mul_le_mul_of_nonneg_left hbudget hscale
  calc
    (ε * Real.sqrt (Real.pi * ε) / (2 * Real.pi)) *
        (4 * Real.exp (ε / 4) +
          4 * Real.exp (ε / 4 - Real.pi ^ 2 / ε) -
          2 / Real.sqrt (Real.pi * ε) *
            ((3 / 2 : ℝ) * |Real.pi / ε| +
              (2 / (1 - Real.exp (-2))) * (2 * Real.exp (-(1 / 2 : ℝ))))) ≤
        (ε * Real.sqrt (Real.pi * ε) / (2 * Real.pi)) *
          (2 * Real.pi / (ε * Real.sqrt (Real.pi * ε)) *
            ((certificate.cutoff : ℝ) * Real.log certificate.cutoff ^ 2)) := hmul
    _ = (certificate.cutoff : ℝ) * Real.log certificate.cutoff ^ 2 := by
      have hden : ε * Real.sqrt (Real.pi * ε) ≠ 0 := by
        apply ne_of_gt
        apply mul_pos certificate.width_pos
        exact Real.sqrt_pos.2 (mul_pos Real.pi_pos certificate.width_pos)
      have hpi : 2 * Real.pi ≠ 0 := by positivity
      have hcancel :
          ε * Real.sqrt (Real.pi * ε) / (2 * Real.pi) *
              (2 * Real.pi / (ε * Real.sqrt (Real.pi * ε))) = 1 := by
        calc
          ε * Real.sqrt (Real.pi * ε) / (2 * Real.pi) *
              (2 * Real.pi / (ε * Real.sqrt (Real.pi * ε))) =
              (ε * Real.sqrt (Real.pi * ε)) /
                (ε * Real.sqrt (Real.pi * ε)) :=
            div_mul_div_cancel₀ hpi
          _ = 1 := div_self hden
      calc
        ε * Real.sqrt (Real.pi * ε) / (2 * Real.pi) *
            (2 * Real.pi / (ε * Real.sqrt (Real.pi * ε)) *
              ((certificate.cutoff : ℝ) * Real.log certificate.cutoff ^ 2)) =
            (ε * Real.sqrt (Real.pi * ε) / (2 * Real.pi) *
              (2 * Real.pi / (ε * Real.sqrt (Real.pi * ε)))) *
                ((certificate.cutoff : ℝ) * Real.log certificate.cutoff ^ 2) := by ring
        _ = (certificate.cutoff : ℝ) * Real.log certificate.cutoff ^ 2 := by
          rw [hcancel, one_mul]

end
end RiemannGaussian
