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
    convert hraw using 1 <;>
      simp [vinogradovFejerCoordinateBound, vinogradovFejerLength, P, L] <;>
      ring
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
    have hL0 : 0 ≤ L := le_trans (by norm_num) hL
    have hdiv : 0 ≤ (P : ℝ) ^ 2 / (R : ℝ) := by positivity
    have hscale : (P : ℝ) ^ 2 / (R : ℝ) ≤
        (b : ℝ) ^ 2 * ((P : ℝ) ^ 2 / (R : ℝ)) := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hb2 hdiv
    have hscale2 : 2 * ((P : ℝ) ^ 2 / (R : ℝ)) ≤
        2 * (b : ℝ) ^ 2 * ((P : ℝ) ^ 2 / (R : ℝ)) := by
      calc
        _ ≤ 2 * ((b : ℝ) ^ 2 * ((P : ℝ) ^ 2 / (R : ℝ))) :=
          mul_le_mul_of_nonneg_left hscale (by norm_num)
        _ = 2 * (b : ℝ) ^ 2 * ((P : ℝ) ^ 2 / (R : ℝ)) := by ring
    calc
      _ ≤ 2 * ((P : ℝ) ^ 2 / (R : ℝ)) * L := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hqUpper (by norm_num)) (by linarith)
      _ ≤ 2 * (b : ℝ) ^ 2 * ((P : ℝ) ^ 2 / (R : ℝ)) * L := by
        exact mul_le_mul_of_nonneg_right hscale2 hL0
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
      exact mul_le_mul_of_nonneg_left
        (add_le_add (add_le_add (add_le_add hT1 hT2') hT3) hT4) (by norm_num)
    _ ≤ 32 * (b : ℝ) ^ 2 * L *
        ((P : ℝ) ^ 2 / (R : ℝ) + (P : ℝ)) := by
      have hdiv : 0 ≤ (P : ℝ) ^ 2 / (R : ℝ) := by positivity
      have habsorb : 6 * (b : ℝ) ^ 2 * ((P : ℝ) ^ 2 / (R : ℝ)) ≤
          6 * (b : ℝ) ^ 2 * ((P : ℝ) ^ 2 / (R : ℝ)) * L := by
        have hC : 0 ≤ 6 * (b : ℝ) ^ 2 * ((P : ℝ) ^ 2 / (R : ℝ)) := by
          positivity
        calc
          _ = (6 * (b : ℝ) ^ 2 * ((P : ℝ) ^ 2 / (R : ℝ))) * 1 := by ring
          _ ≤ (6 * (b : ℝ) ^ 2 * ((P : ℝ) ^ 2 / (R : ℝ))) * L :=
            mul_le_mul_of_nonneg_left hL hC
      have habsorb' : 6 * (b : ℝ) ^ 2 * (P : ℝ) ^ 2 / (R : ℝ) ≤
          6 * (b : ℝ) ^ 2 * ((P : ℝ) ^ 2 / (R : ℝ)) * L := by
        convert habsorb using 1 <;> ring
      calc
        4 *
            (6 * (b : ℝ) ^ 2 * (P : ℝ) ^ 2 / (R : ℝ) +
              4 * (b : ℝ) ^ 2 * P * L +
              3 * (b : ℝ) ^ 2 * P * L +
              2 * (b : ℝ) ^ 2 * ((P : ℝ) ^ 2 / (R : ℝ)) * L) ≤
            4 *
              (6 * (b : ℝ) ^ 2 * ((P : ℝ) ^ 2 / (R : ℝ)) * L +
                4 * (b : ℝ) ^ 2 * P * L +
                3 * (b : ℝ) ^ 2 * P * L +
                2 * (b : ℝ) ^ 2 * ((P : ℝ) ^ 2 / (R : ℝ)) * L) := by
          exact mul_le_mul_of_nonneg_left
            (add_le_add (add_le_add (add_le_add habsorb' le_rfl) le_rfl) le_rfl)
            (by norm_num)
        _ = 4 *
            (8 * (b : ℝ) ^ 2 * ((P : ℝ) ^ 2 / (R : ℝ)) * L +
              7 * (b : ℝ) ^ 2 * P * L) := by ring
        _ ≤ 4 *
            (8 * (b : ℝ) ^ 2 * ((P : ℝ) ^ 2 / (R : ℝ)) * L +
              8 * (b : ℝ) ^ 2 * P * L) := by
          have hC : 0 ≤ (b : ℝ) ^ 2 * P * L := by positivity
          nlinarith
        _ = 32 * (b : ℝ) ^ 2 * L *
            ((P : ℝ) ^ 2 / (R : ℝ) + (P : ℝ)) := by ring
    _ = 32 * (b : ℝ) ^ 2 * (1 + Real.log ((q : ℝ) + 1)) *
        (((Q ^ (j.val + 1) : ℕ) : ℝ) ^ 2 / (R : ℝ) +
          ((Q ^ (j.val + 1) : ℕ) : ℝ)) := by rfl

def vinogradovCoordinateSavingExponent {k : ℕ} (j : Fin k) : ℕ :=
  (j.val + 1) / 200

theorem vinogradovTrivialCoordinateCost_le_naturalScale
    {Q b k : ℕ} (hQ : 1 ≤ Q) (hb : 1 ≤ b) (j : Fin k) :
    vinogradovTrivialCoordinateCost Q Q b j ≤
      24 * (b : ℝ) ^ 2 * ((Q ^ (j.val + 1) : ℕ) : ℝ) ^ 2 := by
  let P : ℕ := Q ^ (j.val + 1)
  have hP : 1 ≤ P := by
    unfold P
    exact one_le_pow₀ hQ
  have hleft : b * P + 1 ≤ 2 * b * P := by nlinarith
  have hright : 2 * b * P + 1 ≤ 3 * b * P := by nlinarith
  have hdef : vinogradovTrivialCoordinateCost Q Q b j =
      4 * ((b * P + 1 : ℕ) : ℝ) * ((2 * b * P + 1 : ℕ) : ℝ) := by
    unfold vinogradovTrivialCoordinateCost
    rw [show vinogradovFejerCoordinateBound Q b j = b * P by rfl]
    unfold vinogradovFejerLength
    rw [show vinogradovFejerCoordinateBound Q b j = b * P by rfl]
    congr 2
    ring
  rw [hdef]
  calc
    _ ≤ 4 * ((2 * b * P : ℕ) : ℝ) * ((3 * b * P : ℕ) : ℝ) := by
      have hleftR : ((b * P + 1 : ℕ) : ℝ) ≤ ((2 * b * P : ℕ) : ℝ) := by
        exact_mod_cast hleft
      have hrightR : ((2 * b * P + 1 : ℕ) : ℝ) ≤ ((3 * b * P : ℕ) : ℝ) := by
        exact_mod_cast hright
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left hleftR (by norm_num)) hrightR
        (by positivity) (by positivity)
    _ = 24 * (b : ℝ) ^ 2 * ((Q ^ (j.val + 1) : ℕ) : ℝ) ^ 2 := by
      unfold P
      push_cast
      ring

/-- After absorbing the explicit large-sieve logarithm into half of the
denominator reserve, one useful coordinate saves the exact power
`Q^floor((j+1)/200)` against its natural `Q^(2(j+1))` scale. -/
theorem vinogradovRationalCoordinateCost_le_powerSaving
    {Q b q k : ℕ} (hQ : 1 ≤ Q) (hb : 1 ≤ b) (j : Fin k)
    (hRq : Q ^ (2 * vinogradovCoordinateSavingExponent j) ≤ q)
    (hqR : q * Q ^ (2 * vinogradovCoordinateSavingExponent j) ≤
      (Q ^ (j.val + 1)) ^ 2)
    (habsorb :
      32 * (b : ℝ) ^ 2 * (1 + Real.log ((q : ℝ) + 1)) ≤
        (Q : ℝ) ^ vinogradovCoordinateSavingExponent j) :
    vinogradovRationalCoordinateCost Q Q b q j ≤
      2 * ((Q ^ (j.val + 1) : ℕ) : ℝ) ^ 2 /
        (Q : ℝ) ^ vinogradovCoordinateSavingExponent j := by
  let e : ℕ := vinogradovCoordinateSavingExponent j
  let P : ℕ := Q ^ (j.val + 1)
  let R : ℕ := Q ^ (2 * e)
  have hR : 0 < R := by
    unfold R
    exact pow_pos (by omega) _
  have hwindow := vinogradovRationalCoordinateCost_le_window
    hQ hb hR hRq j hqR
  have he : 2 * e ≤ j.val + 1 := by
    unfold e vinogradovCoordinateSavingExponent
    omega
  have hRP : R ≤ P := by
    unfold R P
    exact Nat.pow_le_pow_right (by omega) he
  have hPR : (0 : ℝ) < R := by exact_mod_cast hR
  have hP : (0 : ℝ) < P := by
    exact_mod_cast pow_pos (by omega : 0 < Q) (j.val + 1)
  have hPle : (P : ℝ) ≤ (P : ℝ) ^ 2 / (R : ℝ) := by
    rw [le_div_iff₀ hPR]
    have hRPR : (R : ℝ) ≤ P := by exact_mod_cast hRP
    nlinarith
  have hbracket : (P : ℝ) ^ 2 / (R : ℝ) + (P : ℝ) ≤
      2 * ((P : ℝ) ^ 2 / (R : ℝ)) := by linarith
  have hscale :
      32 * (b : ℝ) ^ 2 * (1 + Real.log ((q : ℝ) + 1)) *
          ((P : ℝ) ^ 2 / (R : ℝ) + (P : ℝ)) ≤
        ((Q : ℝ) ^ e) * (2 * ((P : ℝ) ^ 2 / (R : ℝ))) := by
    exact mul_le_mul habsorb hbracket (by positivity) (by positivity)
  calc
    vinogradovRationalCoordinateCost Q Q b q j ≤
        32 * (b : ℝ) ^ 2 * (1 + Real.log ((q : ℝ) + 1)) *
          ((P : ℝ) ^ 2 / (R : ℝ) + (P : ℝ)) := by
      simpa [P, R] using hwindow
    _ ≤ ((Q : ℝ) ^ e) * (2 * ((P : ℝ) ^ 2 / (R : ℝ))) := hscale
    _ = 2 * ((P : ℝ) ^ 2) / ((Q : ℝ) ^ e) := by
      have hQpos : (0 : ℝ) < Q := by exact_mod_cast (by omega : 0 < Q)
      unfold R
      push_cast
      rw [pow_mul]
      field_simp
      ring
    _ = 2 * ((Q ^ (j.val + 1) : ℕ) : ℝ) ^ 2 /
        (Q : ℝ) ^ vinogradovCoordinateSavingExponent j := by rfl

end

end RHTower.Sieve
