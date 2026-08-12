import GaloisForLFunctions.RHTower.Sieve.VinogradovCoordinateKernelBound

namespace RHTower.Sieve

noncomputable section

/-- Source-shaped denominator-window bound for one rational coordinate.
The proof expands before estimating, preserving cancellation of `q` in
the mixed term `(G/q) * (q log q)`.  Bounding the two factors separately
would introduce a fatal extra `P/R`. -/
theorem vinogradovRationalCoordinateCost_le_window
    {Q b q R k : ℕ} (hQ : 1 ≤ Q) (hb : 1 ≤ b) (hR : 0 < R)
    (hRq : R ≤ q) (j : Fin k)
    (hqR : q * R ≤ (Q ^ (j.val + 1)) ^ 2) :
    vinogradovRationalCoordinateCost Q Q b q j ≤
      32 * (b : ℝ) ^ 2 * (1 + Real.log ((q : ℝ) + 1)) *
        (((Q ^ (j.val + 1) : ℕ) : ℝ) ^ 2 / (R : ℝ) +
          ((Q ^ (j.val + 1) : ℕ) : ℝ)) := by
  let P : ℕ := Q ^ (j.val + 1)
  let L : ℝ := 1 + Real.log ((q : ℝ) + 1)
  have hq : 0 < q := lt_of_lt_of_le hR hRq
  have hPR : (0 : ℝ) < R := by exact_mod_cast hR
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  have hbR : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hPnat : 1 ≤ P := by
    unfold P
    exact one_le_pow₀ hQ
  have hP : (1 : ℝ) ≤ P := by exact_mod_cast hPnat
  have hL : 1 ≤ L := by
    unfold L
    have hlog : 0 ≤ Real.log ((q : ℝ) + 1) := by
      apply Real.log_nonneg
      norm_num
    linarith
  have hqUpper : (q : ℝ) ≤ (P : ℝ) ^ 2 / (R : ℝ) := by
    rw [le_div_iff₀ hPR]
    exact_mod_cast hqR
  have hinv : 1 / (q : ℝ) ≤ 1 / (R : ℝ) := by
    rw [one_div_le_one_div hqpos hPR]
    exact_mod_cast hRq
  have hA : 2 * (b : ℝ) * P / (q : ℝ) ≤
      2 * (b : ℝ) * P / (R : ℝ) := by
    simp only [div_eq_mul_inv]
    gcongr
  have hH : (2 * b * P + 1 : ℕ) ≤ 3 * b * P := by
    nlinarith
  have hHR : ((2 * b * P + 1 : ℕ) : ℝ) ≤ 3 * (b : ℝ) * P := by
    exact_mod_cast hH
  have hraw := vinogradovRationalCoordinateCost_le_explicit
    (X := Q) (Y := Q) (b := b) hq j
  have hraw' : vinogradovRationalCoordinateCost Q Q b q j ≤
      4 * (2 * (b : ℝ) * P / (q : ℝ) + 1) *
        ((2 * (b : ℝ) * P + 1) + 2 * (q : ℝ) * L) := by
    simpa [vinogradovFejerCoordinateBound, vinogradovFejerLength, P, L]
      using hraw
  have hT1 :
      (2 * (b : ℝ) * P / (q : ℝ)) * ((2 * b * P + 1 : ℕ) : ℝ) ≤
        6 * (b : ℝ) ^ 2 * (P : ℝ) ^ 2 / (R : ℝ) := by
    calc
      _ ≤ (2 * (b : ℝ) * P / (R : ℝ)) * (3 * (b : ℝ) * P) := by
        exact mul_le_mul hA hHR (by positivity) (by positivity)
      _ = 6 * (b : ℝ) ^ 2 * (P : ℝ) ^ 2 / (R : ℝ) := by ring
  have hT2 :
      (2 * (b : ℝ) * P / (q : ℝ)) * (2 * (q : ℝ) * L) =
        4 * (b : ℝ) * P * L := by
    field_simp
    ring
  have hT2' : 4 * (b : ℝ) * P * L ≤
      4 * (b : ℝ) ^ 2 * P * L := by
    have hbSq : (b : ℝ) ≤ (b : ℝ) ^ 2 := by nlinarith
    gcongr
  have hT3 : ((2 * b * P + 1 : ℕ) : ℝ) ≤
      3 * (b : ℝ) ^ 2 * P * L := by
    calc
      _ ≤ 3 * (b : ℝ) * P := hHR
      _ ≤ 3 * (b : ℝ) ^ 2 * P * L := by
        nlinarith [sq_nonneg ((b : ℝ) - 1)]
  have hT4 : 2 * (q : ℝ) * L ≤
      2 * (b : ℝ) ^ 2 * ((P : ℝ) ^ 2 / (R : ℝ)) * L := by
    have hb2 : (1 : ℝ) ≤ (b : ℝ) ^ 2 := by nlinarith
    calc
      _ ≤ 2 * ((P : ℝ) ^ 2 / (R : ℝ)) * L := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hqUpper (by norm_num)) (by linarith)
      _ ≤ 2 * (b : ℝ) ^ 2 * ((P : ℝ) ^ 2 / (R : ℝ)) * L := by
        have hdiv : 0 ≤ (P : ℝ) ^ 2 / (R : ℝ) := by positivity
        nlinarith
  calc
    vinogradovRationalCoordinateCost Q Q b q j ≤
        4 * (2 * (b : ℝ) * P / (q : ℝ) + 1) *
          ((2 * (b : ℝ) * P + 1) + 2 * (q : ℝ) * L) := hraw'
    _ = 4 *
        ((2 * (b : ℝ) * P / (q : ℝ)) * ((2 * b * P + 1 : ℕ) : ℝ) +
          (2 * (b : ℝ) * P / (q : ℝ)) * (2 * (q : ℝ) * L) +
          ((2 * b * P + 1 : ℕ) : ℝ) + 2 * (q : ℝ) * L) := by
      push_cast
      ring
    _ ≤ 4 *
        (6 * (b : ℝ) ^ 2 * (P : ℝ) ^ 2 / (R : ℝ) +
          4 * (b : ℝ) ^ 2 * P * L +
          3 * (b : ℝ) ^ 2 * P * L +
          2 * (b : ℝ) ^ 2 * ((P : ℝ) ^ 2 / (R : ℝ)) * L) := by
      rw [hT2]
      nlinarith
    _ ≤ 32 * (b : ℝ) ^ 2 * L *
        ((P : ℝ) ^ 2 / (R : ℝ) + (P : ℝ)) := by
      have hdiv : 0 ≤ (P : ℝ) ^ 2 / (R : ℝ) := by positivity
      have habsorb : 6 * (b : ℝ) ^ 2 * ((P : ℝ) ^ 2 / (R : ℝ)) ≤
          6 * (b : ℝ) ^ 2 * ((P : ℝ) ^ 2 / (R : ℝ)) * L := by
        gcongr
      nlinarith
    _ = 32 * (b : ℝ) ^ 2 * (1 + Real.log ((q : ℝ) + 1)) *
        (((Q ^ (j.val + 1) : ℕ) : ℝ) ^ 2 / (R : ℝ) +
          ((Q ^ (j.val + 1) : ℕ) : ℝ)) := by rfl

end

end RHTower.Sieve
