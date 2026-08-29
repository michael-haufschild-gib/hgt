import GaloisForLFunctions.RHTower.Sieve.KubalalikaFibreCondition

/-!
# The block envelope at the Kubalalika parameter choice

At `U ≍ T^{1/2}` and `V ≍ T^{1/8}` the five monomials of the block envelope become the five
powers `T^{13/16}r^{1/6}`, `T r^{-1/2}`, `T^{15/16}`, `T^{3/4}r^{1/4}` and `T^{3/4}`, whose
harmonic totals over `T^{1/4} ≤ r ≤ T^{3/4}` all stay at `T^{15/16}`.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction RHTower

noncomputable section

/-- The five monomials of the block envelope after the parameter substitution. -/
def kubalalikaScalePower (T r : ℝ) : ℝ :=
  T ^ (13 / 16 : ℝ) * r ^ (1 / 6 : ℝ) + T * r ^ (-(1 / 2) : ℝ) + T ^ (15 / 16 : ℝ)
    + T ^ (3 / 4 : ℝ) * r ^ (1 / 4 : ℝ) + T ^ (3 / 4 : ℝ)

theorem kubalalikaScalePower_nonneg {T r : ℝ} (hT : 0 ≤ T) (hr : 0 ≤ r) :
    0 ≤ kubalalikaScalePower T r := by
  rw [kubalalikaScalePower]
  positivity

theorem rpow_le_of_pow_le {x y e : ℝ} {n : ℕ} (hn : n ≠ 0) (hy : 0 ≤ y)
    (h : (x ^ e) ^ n ≤ y ^ n) : x ^ e ≤ y :=
  le_of_pow_le_pow_left₀ hn hy h

theorem four_rpow_third_le : (4 : ℝ) ^ (1 / 3 : ℝ) ≤ 2 := by
  refine rpow_le_of_pow_le (n := 3) (by norm_num) (by norm_num) ?_
  rw [← Real.rpow_natCast ((4 : ℝ) ^ (1 / 3 : ℝ)) 3, ← Real.rpow_mul (by norm_num)]
  norm_num

theorem four_rpow_three_half_le : (4 : ℝ) ^ (3 / 2 : ℝ) ≤ 8 := by
  refine rpow_le_of_pow_le (n := 2) (by norm_num) (by norm_num) ?_
  rw [← Real.rpow_natCast ((4 : ℝ) ^ (3 / 2 : ℝ)) 2, ← Real.rpow_mul (by norm_num)]
  norm_num

theorem four_rpow_three_quarter_le : (4 : ℝ) ^ (3 / 4 : ℝ) ≤ 3 := by
  refine rpow_le_of_pow_le (n := 4) (by norm_num) (by norm_num) ?_
  rw [← Real.rpow_natCast ((4 : ℝ) ^ (3 / 4 : ℝ)) 4, ← Real.rpow_mul (by norm_num)]
  norm_num

theorem mul3_le {a b c a' b' c' : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (ha' : a ≤ a') (hb' : b ≤ b') (hc' : c ≤ c') : a * b * c ≤ a' * b' * c' := by
  have ha'0 : 0 ≤ a' := le_trans ha ha'
  have hb'0 : 0 ≤ b' := le_trans hb hb'
  exact mul_le_mul (mul_le_mul ha' hb' hb ha'0) hc' hc (by positivity)

/-- The reciprocal of a positive power is antitone in the base. -/
theorem rpow_neg_le_rpow_neg {x y e : ℝ} (hx : 0 < x) (hxy : x ≤ y) (he : 0 ≤ e) :
    y ^ (-e) ≤ x ^ (-e) := by
  have hy : (0 : ℝ) < y := lt_of_lt_of_le hx hxy
  rw [Real.rpow_neg hx.le, Real.rpow_neg hy.le]
  refine inv_anti₀ (Real.rpow_pos_of_pos hx _) ?_
  exact Real.rpow_le_rpow hx.le hxy he

/-- **The block envelope at the Kubalalika parameters.** -/
theorem kubalalikaBlockPower_le_scale {D T r : ℝ} (hD : 0 ≤ D) (hT : 1 ≤ T) (hr : 0 < r)
    {A B U V : ℕ} (hA : 1 ≤ A) (hAB : A ≤ B) (hB4 : (B : ℝ) ≤ 4 * T)
    (hU1 : T ^ (1 / 2 : ℝ) ≤ (U : ℝ)) (hU2 : (U : ℝ) ≤ 2 * T ^ (1 / 2 : ℝ))
    (hV1 : T ^ (1 / 8 : ℝ) ≤ (V : ℝ)) (hV2 : (V : ℝ) ≤ 2 * T ^ (1 / 8 : ℝ)) :
    kubalalikaBlockPower D T r A B U V
      ≤ 8 * D * (1 + Real.log (4 * T)) ^ 4 * kubalalikaScalePower T r := by
  have hT0 : (0 : ℝ) < T := lt_of_lt_of_le zero_lt_one hT
  have hA0 : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
  have hB1 : (1 : ℝ) ≤ (B : ℝ) := by exact_mod_cast le_trans hA hAB
  have hB0 : (0 : ℝ) < (B : ℝ) := lt_of_lt_of_le zero_lt_one hB1
  have hA4 : (A : ℝ) ≤ 4 * T := le_trans (by exact_mod_cast hAB) hB4
  have hUp : (0 : ℝ) < T ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hT0 _
  have hVp : (0 : ℝ) < T ^ (1 / 8 : ℝ) := Real.rpow_pos_of_pos hT0 _
  have hU0 : (0 : ℝ) < (U : ℝ) := lt_of_lt_of_le hUp hU1
  have hV0 : (0 : ℝ) < (V : ℝ) := lt_of_lt_of_le hVp hV1
  have hX : (0 : ℝ) < T * r := by positivity
  -- the logarithmic factor
  have hlog : (1 + Real.log B) ^ 4 ≤ (1 + Real.log (4 * T)) ^ 4 := by
    have h : Real.log B ≤ Real.log (4 * T) := Real.log_le_log hB0 hB4
    have h0 : (0 : ℝ) ≤ 1 + Real.log B := by
      have := Real.log_nonneg hB1
      linarith
    exact pow_le_pow_left₀ h0 (by linarith) 4
  -- the five monomials
  have hP1 : (A : ℝ) ^ (1 / 3 : ℝ) * (T * r) ^ (1 / 6 : ℝ) * Real.sqrt ((U : ℝ) * (V : ℝ))
      ≤ 4 * (T ^ (13 / 16 : ℝ) * r ^ (1 / 6 : ℝ)) := by
    have h1 : (A : ℝ) ^ (1 / 3 : ℝ) ≤ 2 * T ^ (1 / 3 : ℝ) := by
      calc (A : ℝ) ^ (1 / 3 : ℝ) ≤ (4 * T) ^ (1 / 3 : ℝ) :=
            Real.rpow_le_rpow hA0.le hA4 (by norm_num)
        _ = (4 : ℝ) ^ (1 / 3 : ℝ) * T ^ (1 / 3 : ℝ) :=
            Real.mul_rpow (by norm_num) hT0.le
        _ ≤ 2 * T ^ (1 / 3 : ℝ) :=
            mul_le_mul_of_nonneg_right four_rpow_third_le (Real.rpow_nonneg hT0.le _)
    have h2 : (T * r) ^ (1 / 6 : ℝ) = T ^ (1 / 6 : ℝ) * r ^ (1 / 6 : ℝ) :=
      Real.mul_rpow hT0.le hr.le
    have h3 : Real.sqrt ((U : ℝ) * (V : ℝ)) ≤ 2 * T ^ (5 / 16 : ℝ) := by
      have hUV : (U : ℝ) * (V : ℝ) ≤ 4 * T ^ (5 / 8 : ℝ) := by
        have hmul : (U : ℝ) * (V : ℝ) ≤ (2 * T ^ (1 / 2 : ℝ)) * (2 * T ^ (1 / 8 : ℝ)) :=
          mul_le_mul hU2 hV2 hV0.le (by positivity)
        have hval : (2 * T ^ (1 / 2 : ℝ)) * (2 * T ^ (1 / 8 : ℝ)) = 4 * T ^ (5 / 8 : ℝ) := by
          rw [show (5 / 8 : ℝ) = 1 / 2 + 1 / 8 by norm_num, Real.rpow_add hT0]
          ring
        linarith [hval ▸ hmul]
      have hval2 : Real.sqrt (4 * T ^ (5 / 8 : ℝ)) = 2 * T ^ (5 / 16 : ℝ) := by
        have h4 : Real.sqrt 4 = 2 := by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
        have hTs : Real.sqrt (T ^ (5 / 8 : ℝ)) = T ^ (5 / 16 : ℝ) := by
          rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hT0.le]
          norm_num
        rw [Real.sqrt_mul (by norm_num), h4, hTs]
      calc Real.sqrt ((U : ℝ) * (V : ℝ)) ≤ Real.sqrt (4 * T ^ (5 / 8 : ℝ)) :=
            Real.sqrt_le_sqrt hUV
        _ = 2 * T ^ (5 / 16 : ℝ) := hval2
    have hcomb : 2 * T ^ (1 / 3 : ℝ) * (T ^ (1 / 6 : ℝ) * r ^ (1 / 6 : ℝ))
        * (2 * T ^ (5 / 16 : ℝ)) = 4 * (T ^ (13 / 16 : ℝ) * r ^ (1 / 6 : ℝ)) := by
      rw [show (13 / 16 : ℝ) = 1 / 3 + 1 / 6 + 5 / 16 by norm_num, Real.rpow_add hT0,
        Real.rpow_add hT0]
      ring
    calc (A : ℝ) ^ (1 / 3 : ℝ) * (T * r) ^ (1 / 6 : ℝ) * Real.sqrt ((U : ℝ) * (V : ℝ))
        ≤ 2 * T ^ (1 / 3 : ℝ) * (T ^ (1 / 6 : ℝ) * r ^ (1 / 6 : ℝ)) * (2 * T ^ (5 / 16 : ℝ)) := by
          refine mul3_le (by positivity) (by positivity) (Real.sqrt_nonneg _) h1
            (le_of_eq h2) h3
      _ = 4 * (T ^ (13 / 16 : ℝ) * r ^ (1 / 6 : ℝ)) := hcomb
  have hP2 : (B : ℝ) ^ (3 / 2 : ℝ) * (T * r) ^ (-(1 / 2) : ℝ)
      ≤ 8 * (T * r ^ (-(1 / 2) : ℝ)) := by
    have h1 : (B : ℝ) ^ (3 / 2 : ℝ) ≤ 8 * T ^ (3 / 2 : ℝ) := by
      calc (B : ℝ) ^ (3 / 2 : ℝ) ≤ (4 * T) ^ (3 / 2 : ℝ) :=
            Real.rpow_le_rpow hB0.le hB4 (by norm_num)
        _ = (4 : ℝ) ^ (3 / 2 : ℝ) * T ^ (3 / 2 : ℝ) := Real.mul_rpow (by norm_num) hT0.le
        _ ≤ 8 * T ^ (3 / 2 : ℝ) :=
            mul_le_mul_of_nonneg_right four_rpow_three_half_le (Real.rpow_nonneg hT0.le _)
    have h2 : (T * r) ^ (-(1 / 2) : ℝ) = T ^ (-(1 / 2) : ℝ) * r ^ (-(1 / 2) : ℝ) :=
      Real.mul_rpow hT0.le hr.le
    have hcomb : 8 * T ^ (3 / 2 : ℝ) * (T ^ (-(1 / 2) : ℝ) * r ^ (-(1 / 2) : ℝ))
        = 8 * (T * r ^ (-(1 / 2) : ℝ)) := by
      have h : T ^ (3 / 2 : ℝ) * T ^ (-(1 / 2) : ℝ) = T := by
        rw [← Real.rpow_add hT0, show (3 / 2 : ℝ) + -(1 / 2) = 1 by norm_num, Real.rpow_one]
      calc 8 * T ^ (3 / 2 : ℝ) * (T ^ (-(1 / 2) : ℝ) * r ^ (-(1 / 2) : ℝ))
          = 8 * (T ^ (3 / 2 : ℝ) * T ^ (-(1 / 2) : ℝ)) * r ^ (-(1 / 2) : ℝ) := by ring
        _ = 8 * T * r ^ (-(1 / 2) : ℝ) := by rw [h]
        _ = 8 * (T * r ^ (-(1 / 2) : ℝ)) := by ring
    calc (B : ℝ) ^ (3 / 2 : ℝ) * (T * r) ^ (-(1 / 2) : ℝ)
        ≤ 8 * T ^ (3 / 2 : ℝ) * (T ^ (-(1 / 2) : ℝ) * r ^ (-(1 / 2) : ℝ)) := by
          rw [h2]
          exact mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = 8 * (T * r ^ (-(1 / 2) : ℝ)) := hcomb
  have hP3 : (B : ℝ) * (V : ℝ) ^ (-(1 / 2) : ℝ) ≤ 4 * T ^ (15 / 16 : ℝ) := by
    have h1 : (V : ℝ) ^ (-(1 / 2) : ℝ) ≤ T ^ (-(1 / 16) : ℝ) := by
      have h := rpow_neg_le_rpow_neg (x := T ^ (1 / 8 : ℝ)) (y := (V : ℝ))
        hVp hV1 (by norm_num : (0 : ℝ) ≤ 1 / 2)
      have hval : (T ^ (1 / 8 : ℝ)) ^ (-(1 / 2) : ℝ) = T ^ (-(1 / 16) : ℝ) := by
        rw [← Real.rpow_mul hT0.le]
        norm_num
      rwa [hval] at h
    have hcomb : 4 * T * T ^ (-(1 / 16) : ℝ) = 4 * T ^ (15 / 16 : ℝ) := by
      rw [show (15 / 16 : ℝ) = 1 + -(1 / 16) by norm_num, Real.rpow_add hT0, Real.rpow_one]
      ring
    calc (B : ℝ) * (V : ℝ) ^ (-(1 / 2) : ℝ) ≤ (4 * T) * T ^ (-(1 / 16) : ℝ) :=
          mul_le_mul hB4 h1 (by positivity) (by positivity)
      _ = 4 * T ^ (15 / 16 : ℝ) := hcomb
  have hP4 : (T * r) ^ (1 / 4 : ℝ) * (B : ℝ) ^ (3 / 4 : ℝ) * (U : ℝ) ^ (-(1 / 2) : ℝ)
      ≤ 3 * (T ^ (3 / 4 : ℝ) * r ^ (1 / 4 : ℝ)) := by
    have h1 : (T * r) ^ (1 / 4 : ℝ) = T ^ (1 / 4 : ℝ) * r ^ (1 / 4 : ℝ) :=
      Real.mul_rpow hT0.le hr.le
    have h2 : (B : ℝ) ^ (3 / 4 : ℝ) ≤ 3 * T ^ (3 / 4 : ℝ) := by
      calc (B : ℝ) ^ (3 / 4 : ℝ) ≤ (4 * T) ^ (3 / 4 : ℝ) :=
            Real.rpow_le_rpow hB0.le hB4 (by norm_num)
        _ = (4 : ℝ) ^ (3 / 4 : ℝ) * T ^ (3 / 4 : ℝ) := Real.mul_rpow (by norm_num) hT0.le
        _ ≤ 3 * T ^ (3 / 4 : ℝ) :=
            mul_le_mul_of_nonneg_right four_rpow_three_quarter_le (Real.rpow_nonneg hT0.le _)
    have h3 : (U : ℝ) ^ (-(1 / 2) : ℝ) ≤ T ^ (-(1 / 4) : ℝ) := by
      have h := rpow_neg_le_rpow_neg (x := T ^ (1 / 2 : ℝ)) (y := (U : ℝ))
        hUp hU1 (by norm_num : (0 : ℝ) ≤ 1 / 2)
      have hval : (T ^ (1 / 2 : ℝ)) ^ (-(1 / 2) : ℝ) = T ^ (-(1 / 4) : ℝ) := by
        rw [← Real.rpow_mul hT0.le]
        norm_num
      rwa [hval] at h
    have hcomb : T ^ (1 / 4 : ℝ) * r ^ (1 / 4 : ℝ) * (3 * T ^ (3 / 4 : ℝ)) * T ^ (-(1 / 4) : ℝ)
        = 3 * (T ^ (3 / 4 : ℝ) * r ^ (1 / 4 : ℝ)) := by
      have h : T ^ (1 / 4 : ℝ) * T ^ (-(1 / 4) : ℝ) = 1 := by
        rw [← Real.rpow_add hT0, show (1 / 4 : ℝ) + -(1 / 4) = 0 by norm_num, Real.rpow_zero]
      calc T ^ (1 / 4 : ℝ) * r ^ (1 / 4 : ℝ) * (3 * T ^ (3 / 4 : ℝ)) * T ^ (-(1 / 4) : ℝ)
          = 3 * (T ^ (1 / 4 : ℝ) * T ^ (-(1 / 4) : ℝ)) * (T ^ (3 / 4 : ℝ) * r ^ (1 / 4 : ℝ)) := by
            ring
        _ = 3 * (T ^ (3 / 4 : ℝ) * r ^ (1 / 4 : ℝ)) := by rw [h]; ring
    calc (T * r) ^ (1 / 4 : ℝ) * (B : ℝ) ^ (3 / 4 : ℝ) * (U : ℝ) ^ (-(1 / 2) : ℝ)
        ≤ T ^ (1 / 4 : ℝ) * r ^ (1 / 4 : ℝ) * (3 * T ^ (3 / 4 : ℝ)) * T ^ (-(1 / 4) : ℝ) := by
          rw [h1]
          exact mul3_le (by positivity) (by positivity) (by positivity) le_rfl h2 h3
      _ = 3 * (T ^ (3 / 4 : ℝ) * r ^ (1 / 4 : ℝ)) := hcomb
  have hP5 : (B : ℝ) * (U : ℝ) ^ (-(1 / 2) : ℝ) ≤ 4 * T ^ (3 / 4 : ℝ) := by
    have h3 : (U : ℝ) ^ (-(1 / 2) : ℝ) ≤ T ^ (-(1 / 4) : ℝ) := by
      have h := rpow_neg_le_rpow_neg (x := T ^ (1 / 2 : ℝ)) (y := (U : ℝ))
        hUp hU1 (by norm_num : (0 : ℝ) ≤ 1 / 2)
      have hval : (T ^ (1 / 2 : ℝ)) ^ (-(1 / 2) : ℝ) = T ^ (-(1 / 4) : ℝ) := by
        rw [← Real.rpow_mul hT0.le]
        norm_num
      rwa [hval] at h
    have hcomb : 4 * T * T ^ (-(1 / 4) : ℝ) = 4 * T ^ (3 / 4 : ℝ) := by
      rw [show (3 / 4 : ℝ) = 1 + -(1 / 4) by norm_num, Real.rpow_add hT0, Real.rpow_one]
      ring
    calc (B : ℝ) * (U : ℝ) ^ (-(1 / 2) : ℝ) ≤ (4 * T) * T ^ (-(1 / 4) : ℝ) :=
          mul_le_mul hB4 h3 (by positivity) (by positivity)
      _ = 4 * T ^ (3 / 4 : ℝ) := hcomb
  -- assemble
  rw [kubalalikaBlockPower, kubalalikaScalePower]
  have hL0 : (0 : ℝ) ≤ (1 + Real.log (4 * T)) ^ 4 := by positivity
  have hLB0 : (0 : ℝ) ≤ (1 + Real.log B) ^ 4 := by positivity
  set S : ℝ := T ^ (13 / 16 : ℝ) * r ^ (1 / 6 : ℝ) + T * r ^ (-(1 / 2) : ℝ) + T ^ (15 / 16 : ℝ)
    + T ^ (3 / 4 : ℝ) * r ^ (1 / 4 : ℝ) + T ^ (3 / 4 : ℝ) with hSdef
  have hS0 : (0 : ℝ) ≤ S := by rw [hSdef]; positivity
  have hinner : (A : ℝ) ^ (1 / 3 : ℝ) * (T * r) ^ (1 / 6 : ℝ) * Real.sqrt ((U : ℝ) * (V : ℝ))
      + (B : ℝ) ^ (3 / 2 : ℝ) * (T * r) ^ (-(1 / 2) : ℝ)
      + (B : ℝ) * (V : ℝ) ^ (-(1 / 2) : ℝ)
      + (T * r) ^ (1 / 4 : ℝ) * (B : ℝ) ^ (3 / 4 : ℝ) * (U : ℝ) ^ (-(1 / 2) : ℝ)
      + (B : ℝ) * (U : ℝ) ^ (-(1 / 2) : ℝ) ≤ 8 * S := by
    rw [hSdef]
    have h1 : (0 : ℝ) ≤ T ^ (13 / 16 : ℝ) * r ^ (1 / 6 : ℝ) := by positivity
    have h2 : (0 : ℝ) ≤ T * r ^ (-(1 / 2) : ℝ) := by positivity
    have h3 : (0 : ℝ) ≤ T ^ (15 / 16 : ℝ) := by positivity
    have h4 : (0 : ℝ) ≤ T ^ (3 / 4 : ℝ) * r ^ (1 / 4 : ℝ) := by positivity
    have h5 : (0 : ℝ) ≤ T ^ (3 / 4 : ℝ) := by positivity
    linarith [hP1, hP2, hP3, hP4, hP5]
  have hstep : (1 + Real.log B) ^ 4
      * ((A : ℝ) ^ (1 / 3 : ℝ) * (T * r) ^ (1 / 6 : ℝ) * Real.sqrt ((U : ℝ) * (V : ℝ))
        + (B : ℝ) ^ (3 / 2 : ℝ) * (T * r) ^ (-(1 / 2) : ℝ)
        + (B : ℝ) * (V : ℝ) ^ (-(1 / 2) : ℝ)
        + (T * r) ^ (1 / 4 : ℝ) * (B : ℝ) ^ (3 / 4 : ℝ) * (U : ℝ) ^ (-(1 / 2) : ℝ)
        + (B : ℝ) * (U : ℝ) ^ (-(1 / 2) : ℝ))
      ≤ (1 + Real.log (4 * T)) ^ 4 * (8 * S) := by
    refine mul_le_mul hlog hinner ?_ hL0
    have h1 : (0 : ℝ) ≤ (A : ℝ) ^ (1 / 3 : ℝ) * (T * r) ^ (1 / 6 : ℝ)
        * Real.sqrt ((U : ℝ) * (V : ℝ)) := by positivity
    have h2 : (0 : ℝ) ≤ (B : ℝ) ^ (3 / 2 : ℝ) * (T * r) ^ (-(1 / 2) : ℝ) := by positivity
    have h3 : (0 : ℝ) ≤ (B : ℝ) * (V : ℝ) ^ (-(1 / 2) : ℝ) := by positivity
    have h4 : (0 : ℝ) ≤ (T * r) ^ (1 / 4 : ℝ) * (B : ℝ) ^ (3 / 4 : ℝ)
        * (U : ℝ) ^ (-(1 / 2) : ℝ) := by positivity
    have h5 : (0 : ℝ) ≤ (B : ℝ) * (U : ℝ) ^ (-(1 / 2) : ℝ) := by positivity
    linarith
  have hDmul := mul_le_mul_of_nonneg_left hstep hD
  calc D * (1 + Real.log B) ^ 4
      * ((A : ℝ) ^ (1 / 3 : ℝ) * (T * r) ^ (1 / 6 : ℝ) * Real.sqrt ((U : ℝ) * (V : ℝ))
        + (B : ℝ) ^ (3 / 2 : ℝ) * (T * r) ^ (-(1 / 2) : ℝ)
        + (B : ℝ) * (V : ℝ) ^ (-(1 / 2) : ℝ)
        + (T * r) ^ (1 / 4 : ℝ) * (B : ℝ) ^ (3 / 4 : ℝ) * (U : ℝ) ^ (-(1 / 2) : ℝ)
        + (B : ℝ) * (U : ℝ) ^ (-(1 / 2) : ℝ))
      = D * ((1 + Real.log B) ^ 4
      * ((A : ℝ) ^ (1 / 3 : ℝ) * (T * r) ^ (1 / 6 : ℝ) * Real.sqrt ((U : ℝ) * (V : ℝ))
        + (B : ℝ) ^ (3 / 2 : ℝ) * (T * r) ^ (-(1 / 2) : ℝ)
        + (B : ℝ) * (V : ℝ) ^ (-(1 / 2) : ℝ)
        + (T * r) ^ (1 / 4 : ℝ) * (B : ℝ) ^ (3 / 4 : ℝ) * (U : ℝ) ^ (-(1 / 2) : ℝ)
        + (B : ℝ) * (U : ℝ) ^ (-(1 / 2) : ℝ))) := by ring
    _ ≤ D * ((1 + Real.log (4 * T)) ^ 4 * (8 * S)) := hDmul
    _ = 8 * D * (1 + Real.log (4 * T)) ^ 4 * S := by ring

end

end RHTower.Sieve
