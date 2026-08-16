import GaloisForLFunctions.RHTower.Sieve.InghamUniformDetectorGapPolynomial

open Complex Filter Metric Set ArithmeticFunction Finset

namespace RHTower.Sieve

noncomputable section

/-- Uniform zero density with fixed inverse-gap and logarithmic degrees. -/
theorem exists_eventually_zetaLittlewoodZeroCountAbove_le_gapPolynomial :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ᶠ X : ℕ in Filter.atTop,
      ∀ {sigma : ℝ}, 7 / 10 ≤ sigma → sigma < 1 →
      zetaLittlewoodZeroCountAbove (inghamUniformGabrielCenter sigma) 4
          ((X : ℝ) - 2) sigma ≤
        K * (1 + 1 / (1 - sigma)) ^ (7 : ℕ) *
          (1 +
            (X : ℝ) ^ inghamUniformGabrielConservativeExponent sigma *
              (1 + Real.log (X : ℝ)) ^ (2 : ℕ) +
            (1 + Real.log (X : ℝ)) ^ (2 : ℕ)) := by
  obtain ⟨K0, hK0, hcount⟩ :=
    exists_eventually_zetaLittlewoodZeroCountAbove_le_uniformGabrielExplicit
  obtain ⟨C0, hC0, hfactor⟩ :=
    exists_uniformGabrielExplicitFactor_le_gapPower
  let C : ℝ := C0 + 1
  let K : ℝ := K0 * C
  have hC : 0 ≤ C := by dsimp only [C]; linarith
  have hC1 : 1 ≤ C := by dsimp only [C]; linarith
  have hC0C : C0 ≤ C := by dsimp only [C]; linarith
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  refine ⟨K, hK, ?_⟩
  filter_upwards [hcount, eventually_ge_atTop (10 : ℕ)] with X hcountAll hX
  intro sigma hsigma0 hsigma1
  have hcountX := hcountAll hsigma0 hsigma1
  let d : ℝ := 1 - sigma
  let g : ℝ := 1 + 1 / d
  let Q : ℝ :=
    ((1 + 1 / (1 - inghamUniformGabrielCenter sigma)) * Real.exp 1) ^
        (2 : ℕ) *
      (1 + inghamMovingRightTranslatedExplicitConstant
        ((9 / 100 : ℝ) * (1 - sigma)))
  let XP : ℝ := (X : ℝ) ^ inghamUniformGabrielConservativeExponent sigma
  let Log : ℝ := 1 + Real.log (X : ℝ)
  let L : ℝ := Log ^ (2 * inghamUniformGabrielCriticalShare sigma)
  let B : ℝ := Log ^ (2 : ℕ)
  have hd : 0 < d := by dsimp only [d]; positivity
  have hinv0 : 0 ≤ 1 / d := by positivity
  have hg1 : 1 ≤ g := by dsimp only [g]; linarith
  have hg0 : 0 ≤ g := le_trans (by norm_num) hg1
  have hg7 : 0 ≤ g ^ (7 : ℕ) := pow_nonneg hg0 _
  have hinvle : 1 / d ≤ g := by dsimp only [g]; linarith
  have hinvle7 : 1 / d ≤ g ^ (7 : ℕ) := by
    exact hinvle.trans (by
      simpa only [pow_one] using
        (pow_le_pow_right₀ hg1 (by norm_num : (1 : ℕ) ≤ 7)))
  have hfactor' : (1 / d) * Q ≤ C0 * g ^ (7 : ℕ) := by
    simpa only [d, g, Q] using hfactor hsigma0 hsigma1
  have hXR1 : (1 : ℝ) ≤ X := by exact_mod_cast (show 1 ≤ X by omega)
  have hLog1 : 1 ≤ Log := by
    dsimp only [Log]
    linarith [Real.log_nonneg hXR1]
  have hLog0 : 0 ≤ Log := le_trans (by norm_num) hLog1
  have hshare2 : 2 * inghamUniformGabrielCriticalShare sigma ≤ 2 := by
    nlinarith [inghamUniformGabrielCriticalShare_le_one hsigma0 hsigma1.le]
  have hLB : L ≤ B := by
    dsimp only [L, B]
    simpa only [Real.rpow_two] using
      (Real.rpow_le_rpow_of_exponent_le hLog1 hshare2)
  have hXP0 : 0 ≤ XP := by dsimp only [XP]; positivity
  have hL0 : 0 ≤ L := by dsimp only [L]; positivity
  have hB0 : 0 ≤ B := by dsimp only [B]; positivity
  have hXPL : XP * L ≤ XP * B := mul_le_mul_of_nonneg_left hLB hXP0
  have hQ0 : 0 ≤ Q := by
    dsimp only [Q, inghamMovingRightTranslatedExplicitConstant]
    have hgap : 0 < 1 - inghamUniformGabrielCenter sigma := by
      unfold inghamUniformGabrielCenter
      nlinarith
    positivity
  have hbase :
      (1 / d) * (1 + Q * XP * L + B) ≤
        C * g ^ (7 : ℕ) * (1 + XP * B + B) := by
    calc
      (1 / d) * (1 + Q * XP * L + B) =
          (1 / d) + ((1 / d) * Q) * (XP * L) + (1 / d) * B := by ring
      _ ≤ g ^ (7 : ℕ) + (C0 * g ^ (7 : ℕ)) * (XP * B) +
          g ^ (7 : ℕ) * B := by
        exact add_le_add
          (add_le_add hinvle7
            (mul_le_mul hfactor' hXPL
              (mul_nonneg hXP0 hL0)
              (mul_nonneg hC0 hg7)))
          (mul_le_mul_of_nonneg_right hinvle7 hB0)
      _ ≤ (C * g ^ (7 : ℕ)) + (C * g ^ (7 : ℕ)) * (XP * B) +
          (C * g ^ (7 : ℕ)) * B := by
        have hone : g ^ (7 : ℕ) ≤ C * g ^ (7 : ℕ) := by
          simpa only [one_mul] using mul_le_mul_of_nonneg_right hC1 hg7
        have hCfac : C0 * g ^ (7 : ℕ) ≤ C * g ^ (7 : ℕ) :=
          mul_le_mul_of_nonneg_right hC0C hg7
        exact add_le_add (add_le_add hone
          (mul_le_mul_of_nonneg_right hCfac (mul_nonneg hXP0 hB0)))
          (mul_le_mul_of_nonneg_right hone hB0)
      _ = C * g ^ (7 : ℕ) * (1 + XP * B + B) := by ring
  calc
    zetaLittlewoodZeroCountAbove (inghamUniformGabrielCenter sigma) 4
          ((X : ℝ) - 2) sigma ≤
        K0 * (1 / d) * (1 + Q * XP * L + B) := by
      simpa only [d, Q, XP, Log, L, B] using hcountX
    _ = K0 * ((1 / d) * (1 + Q * XP * L + B)) := by ring
    _ ≤ K0 * (C * g ^ (7 : ℕ) * (1 + XP * B + B)) :=
      mul_le_mul_of_nonneg_left hbase hK0
    _ = K * (1 + 1 / (1 - sigma)) ^ (7 : ℕ) *
          (1 +
            (X : ℝ) ^ inghamUniformGabrielConservativeExponent sigma *
              (1 + Real.log (X : ℝ)) ^ (2 : ℕ) +
            (1 + Real.log (X : ℝ)) ^ (2 : ℕ)) := by
      dsimp only [K, g, XP, B, Log]
      ring

end

end RHTower.Sieve
