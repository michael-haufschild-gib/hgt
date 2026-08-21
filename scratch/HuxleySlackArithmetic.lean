import GaloisForLFunctions.RHTower.Sieve.HuxleyDensityHypothesis

example {eps sigma : ℝ} (heps : 0 < eps) (hepss : eps ≤ 1 / 1000)
    (hsh : sigma ≤ 7 / 32 - 5 * eps) :
    eps ^ 2 +
        (3 * eps ^ 2 + (1 + ((9 : ℝ) / 11 - 10 * eps) * (6 * sigma - 2))) ≤
      2 * sigma - eps ^ 2 / 5 := by
  have ha : 0 ≤ (32 : ℝ) / 11 - 60 * eps := by linarith
  have hdist : 0 ≤ (7 : ℝ) / 32 - 5 * eps - sigma := by linarith
  have hmon : 0 ≤ ((32 : ℝ) / 11 - 60 * eps) *
      ((7 : ℝ) / 32 - 5 * eps - sigma) := mul_nonneg ha hdist
  have hbracket : 0 ≤ (675 : ℝ) / 88 - (1521 : ℝ) / 5 * eps := by
    linarith
  have hbase : 0 ≤ eps * ((675 : ℝ) / 88 - (1521 : ℝ) / 5 * eps) :=
    mul_nonneg heps.le hbracket
  nlinarith
