import GaloisForLFunctions.RHTower.Sieve.InghamUniformDetectorZeroFreeTruncation

open Complex Filter Metric Set ArithmeticFunction Finset

namespace RHTower.Sieve

noncomputable section

/-- Uniform zero density on the full Gabriel strip: the zero-free edge converts the
inverse-gap degree seven into a fixed logarithmic degree fourteen. -/
theorem exists_eventually_zetaLittlewoodZeroCountAbove_le_uniformPolylog :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ᶠ X : ℕ in Filter.atTop,
      ∀ {sigma : ℝ}, 7 / 10 ≤ sigma → sigma < 1 →
      zetaLittlewoodZeroCountAbove (inghamUniformGabrielCenter sigma) 4
          ((X : ℝ) - 2) sigma ≤
        K * (1 + Real.log (X : ℝ)) ^ (14 : ℕ) *
          (1 +
            (X : ℝ) ^ inghamUniformGabrielConservativeExponent sigma *
              (1 + Real.log (X : ℝ)) ^ (2 : ℕ) +
            (1 + Real.log (X : ℝ)) ^ (2 : ℕ)) := by
  obtain ⟨K, hK, hdensity⟩ :=
    exists_eventually_zetaLittlewoodZeroCountAbove_le_gapPolynomial
  obtain ⟨L0, hL0, hzero⟩ :=
    exists_zetaLittlewoodZeroCountAbove_eq_zero_near_one
  have hlogEvent :
      ∀ᶠ X : ℕ in Filter.atTop, L0 ≤ Real.log (X : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop L0
  refine ⟨K, hK, ?_⟩
  filter_upwards [hdensity, hlogEvent, eventually_ge_atTop (10 : ℕ)] with
    X hdensityX hlog hX
  intro sigma hsigma0 hsigma1
  let L : ℝ := Real.log (X : ℝ)
  let Log : ℝ := 1 + L
  let d : ℝ := 1 - sigma
  let Tail : ℝ :=
    1 +
      (X : ℝ) ^ inghamUniformGabrielConservativeExponent sigma * Log ^ (2 : ℕ) +
      Log ^ (2 : ℕ)
  have hL1 : 1 ≤ L := by dsimp only [L]; exact hL0.trans hlog
  have hL0' : 0 < L := lt_of_lt_of_le zero_lt_one hL1
  have hLog0 : 0 ≤ Log := by dsimp only [Log]; linarith
  have hd : 0 < d := by dsimp only [d]; linarith
  have hTail0 : 0 ≤ Tail := by
    dsimp only [Tail]
    positivity
  by_cases hnear : 1 - 1 / L ^ (2 : ℕ) ≤ sigma
  · have hz :
        zetaLittlewoodZeroCountAbove (inghamUniformGabrielCenter sigma) 4
            ((X : ℝ) - 2) sigma = 0 := by
      apply hzero hX hlog
      simpa only [L] using hnear
    rw [hz]
    exact mul_nonneg (mul_nonneg hK (pow_nonneg hLog0 _)) hTail0
  · have hgap : 1 / L ^ (2 : ℕ) < d := by
      dsimp only [d]
      linarith
    have hLsqpos : 0 < L ^ (2 : ℕ) := pow_pos hL0' _
    have hinv : 1 / d < L ^ (2 : ℕ) := by
      have hrecip := one_div_lt_one_div_of_lt (one_div_pos.mpr hLsqpos) hgap
      field_simp at hrecip ⊢
      exact hrecip
    have hgapLog : 1 + 1 / d ≤ Log ^ (2 : ℕ) := by
      have hLsq_le : 1 + L ^ (2 : ℕ) ≤ (1 + L) ^ (2 : ℕ) := by
        nlinarith
      dsimp only [Log]
      linarith
    have hgapPow : (1 + 1 / d) ^ (7 : ℕ) ≤ Log ^ (14 : ℕ) := by
      have hbase0 : 0 ≤ 1 + 1 / d := by positivity
      calc
        (1 + 1 / d) ^ (7 : ℕ) ≤ (Log ^ (2 : ℕ)) ^ (7 : ℕ) :=
          pow_le_pow_left₀ hbase0 hgapLog _
        _ = Log ^ (14 : ℕ) := by ring
    have hdensity' := hdensityX hsigma0 hsigma1
    have hcoeff :
        K * (1 + 1 / d) ^ (7 : ℕ) ≤ K * Log ^ (14 : ℕ) :=
      mul_le_mul_of_nonneg_left hgapPow hK
    have hbound := mul_le_mul_of_nonneg_right hcoeff hTail0
    simpa only [d, Log, Tail] using hdensity'.trans hbound

end

end RHTower.Sieve
