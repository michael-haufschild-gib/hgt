import GaloisForLFunctions.RHTower.Sieve.RouteTTailBudget

/-!
# The three tail regimes as logarithmic thresholds

Each of the three regimes of `Sieve/RouteTTailBudget` compares a power of the block top with a
polylogarithmic prefactor.  Taking logarithms turns each into a single linear threshold, which is
the form the schedule discharges: the block top only enters through `log i`, and the whole
inequality reads "the prefactor's logarithm is below the saving".
-/

namespace RHTower.Sieve

noncomputable section

/-- **The contour regime as a threshold.** -/
theorem contour_regime_at {C i a P ρ₀ B : ℝ} (hi : 1 ≤ i)
    (hCP : 0 < 9 * C * P) (hB : 0 < B) (hρ : 1 / B ≤ ρ₀)
    (hkey : Real.log (9 * C * P * B) ≤ a * Real.log i) :
    9 * C * (i ^ (-a) * P) ≤ ρ₀ := by
  have hi0 : (0 : ℝ) < i := by linarith
  have hpow : i ^ (-a) = Real.exp (-(a * Real.log i)) := by
    rw [Real.rpow_def_of_pos hi0]
    congr 1
    ring
  have hprod : (0 : ℝ) < 9 * C * P * B := mul_pos hCP hB
  have hexp : Real.exp (-(a * Real.log i)) ≤ Real.exp (-(Real.log (9 * C * P * B))) :=
    Real.exp_le_exp.2 (by linarith)
  have hval : Real.exp (-(Real.log (9 * C * P * B))) = 1 / (9 * C * P * B) := by
    rw [Real.exp_neg, Real.exp_log hprod, one_div]
  have hstep : 9 * C * (i ^ (-a) * P) = (9 * C * P) * Real.exp (-(a * Real.log i)) := by
    rw [hpow]; ring
  rw [hstep]
  have hmul := mul_le_mul_of_nonneg_left hexp hCP.le
  rw [hval] at hmul
  have hCP0 : (0 : ℝ) < C * P := by linarith
  have hCPne : C * P ≠ 0 := ne_of_gt hCP0
  have hcollapse : (9 * C * P) * (1 / (9 * C * P * B)) = 1 / B := by
    field_simp
    exact div_self hCPne
  rw [hcollapse] at hmul
  linarith

/-- **The truncation regime as a threshold.** -/
theorem trunc_regime_at {C i v Q tt ρ₀ B : ℝ} (hi : 1 ≤ i)
    (hpos : 0 < 9 * C * (3 : ℝ) ^ v * Q) (htt : 0 < tt) (hB : 0 < B) (hρ : 1 / B ≤ ρ₀)
    (hkey : v * Real.log i + Real.log (9 * C * (3 : ℝ) ^ v * Q * B) ≤ Real.log tt) :
    9 * C * ((3 : ℝ) ^ v * i ^ v * Q) / tt ≤ ρ₀ := by
  have hi0 : (0 : ℝ) < i := by linarith
  have hpow : i ^ v = Real.exp (v * Real.log i) := by
    rw [Real.rpow_def_of_pos hi0]
    congr 1
    ring
  have hprod : (0 : ℝ) < 9 * C * (3 : ℝ) ^ v * Q * B := mul_pos hpos hB
  have hexp : Real.exp (v * Real.log i + Real.log (9 * C * (3 : ℝ) ^ v * Q * B))
      ≤ Real.exp (Real.log tt) := Real.exp_le_exp.2 hkey
  rw [Real.exp_log htt, Real.exp_add, Real.exp_log hprod] at hexp
  have hstep : 9 * C * ((3 : ℝ) ^ v * i ^ v * Q)
      = (9 * C * (3 : ℝ) ^ v * Q) * Real.exp (v * Real.log i) := by
    rw [hpow]; ring
  rw [hstep, div_le_iff₀ htt]
  have hkey2 : (9 * C * (3 : ℝ) ^ v * Q) * Real.exp (v * Real.log i) * B ≤ tt := by
    nlinarith [hexp]
  have hBne : B ≠ 0 := ne_of_gt hB
  have hinvB : (0 : ℝ) < 1 / B := by positivity
  have h2 := mul_le_mul_of_nonneg_right hkey2 hinvB.le
  have h3 : (9 * C * (3 : ℝ) ^ v * Q) * Real.exp (v * Real.log i) * B * (1 / B)
      = (9 * C * (3 : ℝ) ^ v * Q) * Real.exp (v * Real.log i) := by field_simp
  rw [h3] at h2
  have h4 : tt * (1 / B) ≤ tt * ρ₀ := mul_le_mul_of_nonneg_left hρ htt.le
  linarith [h2, h4]

/-- **The Chebyshev regime as a threshold.** -/
theorem cheb_regime_at {i ρ₀ B : ℝ} (hi : 1 ≤ i) (hB : 0 < B) (hρ : 1 / B ≤ ρ₀)
    (hkey : Real.log (24 * B) ≤ Real.log i / 4) :
    24 * (i : ℝ) ^ (-((1 : ℝ) / 4)) ≤ ρ₀ := by
  have hC : (0 : ℝ) < 9 * (24 / 9) * 1 := by norm_num
  have hbase := contour_regime_at (C := 24 / 9) (i := i) (a := (1 : ℝ) / 4) (P := 1)
    (ρ₀ := ρ₀) (B := B) hi (by norm_num) hB hρ ?_
  · have hval : 9 * (24 / 9 : ℝ) * (i ^ (-((1 : ℝ) / 4)) * 1) = 24 * i ^ (-((1 : ℝ) / 4)) := by
      ring
    rw [hval] at hbase
    exact hbase
  · have hval : (9 : ℝ) * (24 / 9) * 1 * B = 24 * B := by ring
    rw [hval]
    linarith [hkey]

end

end RHTower.Sieve
