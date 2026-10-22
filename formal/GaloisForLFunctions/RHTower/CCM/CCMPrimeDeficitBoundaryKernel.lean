import GaloisForLFunctions.RHTower.CCM.CCMPrimeDeficitDivisorSourceEntry

/-!
# Local control of the actual source at a shortened square-root cutoff

At terminal radius `(m+k)^2`, two indices beyond `m` can interact only
in a strip of at most `3k` indices. For `3k <= m`, the source in that
strip is before its second entry and has size at most `3k/m`.
-/

noncomputable section

namespace RHTower

private theorem square_shift_exp (m k a b : ℕ) (hm : 0 < m) (ha : 0 < a) (hb : 0 < b) :
    Real.exp (2 * Real.log (m + k : ℕ) - Real.log (a * b : ℕ)) =
      ((m : ℝ) + k) ^ 2 / ((a : ℝ) * b) := by
  have hN : (0 : ℝ) < (m + k : ℕ) := by exact_mod_cast (show 0 < m + k by omega)
  have hab : (0 : ℝ) < (a * b : ℕ) := by exact_mod_cast Nat.mul_pos ha hb
  rw [Real.exp_sub, two_mul, Real.exp_add, Real.exp_log hN, Real.exp_log hab,
    Nat.cast_add, Nat.cast_mul]
  ring

theorem ccmPrimeDeficitDivisorSource_square_window_far_zero
    {m k a b : ℕ} (hm : 0 < m) (hk : 3 * k ≤ m)
    (ha : m + 3 * k < a) (hb : m < b)
    {T : ℝ} (hT : T ≤ 2 * Real.log (m + k : ℕ)) :
    ccmPrimeDeficitDivisorSource (T - Real.log (a * b : ℕ)) = 0 := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have haR : (m : ℝ) + 3 * k < a := by exact_mod_cast ha
  have hbR : (m : ℝ) < b := by exact_mod_cast hb
  have hapos : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
  have hbpos : (0 : ℝ) < b := hmR.trans hbR
  have hkm : (k : ℝ) ≤ m := by exact_mod_cast (show k ≤ m by omega)
  have hpoly : ((m : ℝ) + k) ^ 2 ≤ ((m : ℝ) + 3 * k) * m := by
    nlinarith only [mul_le_mul_of_nonneg_right hkm (Nat.cast_nonneg k)]
  have hprod : ((m : ℝ) + k) ^ 2 < (a : ℝ) * b := hpoly.trans_lt
    ((mul_lt_mul_of_pos_right haR hmR).trans (mul_lt_mul_of_pos_left hbR hapos))
  have hs : T - Real.log (a * b : ℕ) < 0 := by
    apply Real.exp_lt_one_iff.mp
    apply lt_of_le_of_lt (Real.exp_le_exp.mpr (sub_le_sub_right hT _))
    rw [square_shift_exp m k a b hm (by omega) (by omega)]
    exact (div_lt_one (mul_pos hapos hbpos)).mpr hprod
  exact ccmPrimeDeficitDivisorSource_of_nonpos hs.le

theorem ccmPrimeDeficitDivisorSource_square_far_zero
    {m k a b : ℕ} (hm : 0 < m) (hk : 3 * k ≤ m)
    (ha : m + 3 * k < a) (hb : m < b) :
    ccmPrimeDeficitDivisorSource
      (2 * Real.log (m + k : ℕ) - Real.log (a * b : ℕ)) = 0 :=
  ccmPrimeDeficitDivisorSource_square_window_far_zero hm hk ha hb le_rfl

theorem abs_ccmPrimeDeficitDivisorSource_square_window_near_le
    {m k a b : ℕ} (hm : 0 < m) (hk : 3 * k ≤ m) (ha : m < a) (hb : m < b)
    {T : ℝ} (hT : T ≤ 2 * Real.log (m + k : ℕ)) :
    |ccmPrimeDeficitDivisorSource (T - Real.log (a * b : ℕ))| ≤ 3 * (k : ℝ) / m := by
  let s := T - Real.log (a * b : ℕ)
  change |ccmPrimeDeficitDivisorSource s| ≤ _
  by_cases hs : s ≤ 0
  · rw [ccmPrimeDeficitDivisorSource_of_nonpos hs, abs_zero]
    positivity
  have hspos : 0 < s := lt_of_not_ge hs
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hkR : 3 * (k : ℝ) ≤ m := by exact_mod_cast hk
  have hkm : (k : ℝ) ≤ m := by exact_mod_cast (show k ≤ m by omega)
  have hma : (m : ℝ) ≤ a := by exact_mod_cast (Nat.le_of_lt ha)
  have hmb : (m : ℝ) ≤ b := by exact_mod_cast (Nat.le_of_lt hb)
  have hapos : (0 : ℝ) < a := hmR.trans_le hma
  have hbpos : (0 : ℝ) < b := hmR.trans_le hmb
  have habpos : (0 : ℝ) < (a : ℝ) * b := mul_pos hapos hbpos
  have hab : (m : ℝ) ^ 2 ≤ (a : ℝ) * b := by
    simpa only [pow_two] using mul_le_mul hma hmb hmR.le (Nat.cast_nonneg a)
  have h1 : 3 * (m : ℝ) * k ≤ (m : ℝ) ^ 2 := by
    nlinarith only [mul_le_mul_of_nonneg_left hkR hmR.le]
  have h2 : 3 * (k : ℝ) ^ 2 ≤ (m : ℝ) * k := by
    nlinarith only [mul_le_mul_of_nonneg_right hkR (Nat.cast_nonneg k)]
  have hx : ((m : ℝ) + k) ^ 2 < 2 * (m : ℝ) ^ 2 := by
    nlinarith only [h1, h2, sq_pos_of_pos hmR]
  have he : Real.exp s ≤ ((m : ℝ) + k) ^ 2 / ((a : ℝ) * b) := by
    calc
      _ ≤ Real.exp (2 * Real.log (m + k : ℕ) - Real.log (a * b : ℕ)) :=
        Real.exp_le_exp.mpr (sub_le_sub_right hT _)
      _ = _ := square_shift_exp m k a b hm (by omega) (by omega)
  have hstop : s < Real.log 2 := by
    apply (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 2)).mpr
    apply lt_of_le_of_lt he
    rw [div_lt_iff₀ habpos]
    nlinarith only [hx, hab]
  rw [ccmPrimeDeficitDivisorSource_before_two hspos.le hstop,
    abs_of_nonneg (sub_nonneg.mpr (Real.one_le_exp_iff.mpr hspos.le)), sub_le_iff_le_add]
  apply le_trans he
  rw [div_le_iff₀ habpos]
  calc
    ((m : ℝ) + k) ^ 2 ≤ (m : ℝ) ^ 2 + 3 * m * k := by
      nlinarith only [mul_le_mul_of_nonneg_right hkm (Nat.cast_nonneg k)]
    _ = (3 * (k : ℝ) / m + 1) * (m : ℝ) ^ 2 := by
      field_simp
      ring
    _ ≤ (3 * (k : ℝ) / m + 1) * ((a : ℝ) * b) :=
      mul_le_mul_of_nonneg_left hab (by positivity)

theorem abs_ccmPrimeDeficitDivisorSource_square_near_le
    {m k a b : ℕ} (hm : 0 < m) (hk : 3 * k ≤ m) (ha : m < a) (hb : m < b) :
    |ccmPrimeDeficitDivisorSource
      (2 * Real.log (m + k : ℕ) - Real.log (a * b : ℕ))| ≤ 3 * (k : ℝ) / m :=
  abs_ccmPrimeDeficitDivisorSource_square_window_near_le hm hk ha hb le_rfl

end RHTower
