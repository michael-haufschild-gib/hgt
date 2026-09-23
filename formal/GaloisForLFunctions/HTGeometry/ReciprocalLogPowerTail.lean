import GaloisForLFunctions.HTGeometry.LogLinearTailIntegral

/-!
# A fourth-power reciprocal-log tail

The unconditional zero-free-region estimate for the Mertens function is stronger than every
inverse power of the logarithm.  Its Abel tail is therefore reduced to the integral-test series

`sum 1 / (n * (log n)^(4 : ℕ))`.

This file records the exact antiderivative and the shifted infinite-tail bound needed by that
reduction.
-/

open Real
open Filter Topology MeasureTheory Set

namespace GaloisForLFunctions.HTGeometry

/-- The exact antiderivative used for the fourth-power reciprocal-log tail. -/
theorem hasDerivAt_neg_inv_log_cube {x : ℝ} (hx : 1 < x) :
    HasDerivAt (fun x => -(1 / (3 * (Real.log x) ^ (3 : ℕ))))
      (1 / (x * (Real.log x) ^ (4 : ℕ))) x := by
  have hx0 : x ≠ 0 := by linarith
  have hlog0 : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx)
  have hden := ((Real.hasDerivAt_log hx0).pow 3).const_mul (3 : ℝ)
  have hinv := hden.inv (mul_ne_zero (by norm_num) (pow_ne_zero 3 hlog0))
  simp only [Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSub] at hinv
  have hnegfun : (-(fun y : ℝ => 3 * (Real.log y) ^ (3 : ℕ))⁻¹) =
      (fun y : ℝ => -(3 * (Real.log y) ^ (3 : ℕ))⁻¹) := by
    funext y
    rfl
  have hneg := hinv.neg
  rw [hnegfun] at hneg
  have hraw : HasDerivAt (fun y : ℝ => -(3 * (Real.log y) ^ (3 : ℕ))⁻¹)
      (-(-(3 * (3 * Real.log x ^ (2 : ℕ) * x⁻¹)) / (3 * Real.log x ^ (3 : ℕ)) ^ (2 : ℕ))) x := by
    exact hneg
  have hfun : (fun y : ℝ => -(1 / (3 * (Real.log y) ^ (3 : ℕ)))) =
      (fun y : ℝ => -(3 * (Real.log y) ^ (3 : ℕ))⁻¹) := by
    funext y
    rw [one_div]
  rw [hfun]
  refine hraw.congr_deriv ?_
  field_simp

/-- The exact antiderivative used for the third-power reciprocal-log tail. -/
theorem hasDerivAt_neg_inv_two_log_sq {x : ℝ} (hx : 1 < x) :
    HasDerivAt (fun x => -(1 / (2 * (Real.log x) ^ (2 : ℕ))))
      (1 / (x * (Real.log x) ^ (3 : ℕ))) x := by
  have hx0 : x ≠ 0 := by linarith
  have hlog0 : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx)
  have hden := ((Real.hasDerivAt_log hx0).pow 2).const_mul (2 : ℝ)
  have hinv := hden.inv (mul_ne_zero (by norm_num) (pow_ne_zero 2 hlog0))
  simp only [Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSub] at hinv
  have hnegfun : (-(fun y : ℝ => 2 * (Real.log y) ^ (2 : ℕ))⁻¹) =
      (fun y : ℝ => -(2 * (Real.log y) ^ (2 : ℕ))⁻¹) := by
    funext y
    rfl
  have hneg := hinv.neg
  rw [hnegfun] at hneg
  have hraw : HasDerivAt (fun y : ℝ => -(2 * (Real.log y) ^ (2 : ℕ))⁻¹)
      (-(-(2 * (2 * Real.log x * x⁻¹)) / (2 * Real.log x ^ (2 : ℕ)) ^ (2 : ℕ))) x := by
    simpa only [pow_one] using hneg
  have hfun : (fun y : ℝ => -(1 / (2 * (Real.log y) ^ (2 : ℕ)))) =
      (fun y : ℝ => -(2 * (Real.log y) ^ (2 : ℕ))⁻¹) := by
    funext y
    rw [one_div]
  rw [hfun]
  refine hraw.congr_deriv ?_
  field_simp

/-- The reciprocal-log antiderivative vanishes at infinity. -/
theorem tendsto_neg_inv_log_cube_atTop :
    Tendsto (fun x : ℝ => -(1 / (3 * (Real.log x) ^ (3 : ℕ)))) atTop (𝓝 0) := by
  have hlog : Tendsto (fun x : ℝ => (Real.log x) ^ (3 : ℕ)) atTop atTop := by
    refine Filter.tendsto_atTop_mono' _ ?_ Real.tendsto_log_atTop
    filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ)] with x hx
    nlinarith [sq_nonneg (Real.log x)]
  have hinv : Tendsto (fun x : ℝ => 1 / ((Real.log x) ^ (3 : ℕ))) atTop (𝓝 0) := by
    simpa using
      ((tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1)).div_atTop hlog)
  convert (hinv.const_mul (-((3 : ℝ)⁻¹))) using 1 <;> simp <;> ring

/-- The fourth-power reciprocal-log integrand decreases beyond `e`. -/
theorem antitoneOn_one_div_mul_log_four :
    AntitoneOn (fun x : ℝ => 1 / (x * (Real.log x) ^ (4 : ℕ))) (Set.Ici (Real.exp 1)) := by
  intro a ha b hb hab
  have he1 : (1 : ℝ) < Real.exp 1 := Real.one_lt_exp_iff.mpr zero_lt_one
  have ha1 : 1 < a := lt_of_lt_of_le he1 ha
  have hb1 : 1 < b := lt_of_lt_of_le ha1 hab
  have hloga : 0 < Real.log a := Real.log_pos ha1
  have hlogb : 0 < Real.log b := Real.log_pos hb1
  have hlogle : Real.log a ≤ Real.log b := Real.log_le_log (by linarith) hab
  have hpowle : (Real.log a) ^ (4 : ℕ) ≤ (Real.log b) ^ (4 : ℕ) :=
    pow_le_pow_left₀ hloga.le hlogle 4
  have hden : a * (Real.log a) ^ (4 : ℕ) ≤ b * (Real.log b) ^ (4 : ℕ) :=
    mul_le_mul hab hpowle (pow_nonneg hloga.le 4) (by linarith)
  exact one_div_le_one_div_of_le (mul_pos (by linarith) (pow_pos hloga 4)) hden

/-- The third-power reciprocal-log integrand decreases beyond `e`. -/
theorem antitoneOn_one_div_mul_log_three :
    AntitoneOn (fun x : ℝ => 1 / (x * (Real.log x) ^ (3 : ℕ))) (Set.Ici (Real.exp 1)) := by
  intro a ha b hb hab
  have he1 : (1 : ℝ) < Real.exp 1 := Real.one_lt_exp_iff.mpr zero_lt_one
  have ha1 : 1 < a := lt_of_lt_of_le he1 ha
  have hb1 : 1 < b := lt_of_lt_of_le ha1 hab
  have hloga : 0 < Real.log a := Real.log_pos ha1
  have hlogb : 0 < Real.log b := Real.log_pos hb1
  have hlogle : Real.log a ≤ Real.log b := Real.log_le_log (by linarith) hab
  have hpowle : (Real.log a) ^ (3 : ℕ) ≤ (Real.log b) ^ (3 : ℕ) :=
    pow_le_pow_left₀ hloga.le hlogle 3
  have hden : a * (Real.log a) ^ (3 : ℕ) ≤ b * (Real.log b) ^ (3 : ℕ) :=
    mul_le_mul hab hpowle (pow_nonneg hloga.le 3) (by linarith)
  exact one_div_le_one_div_of_le (mul_pos (by linarith) (pow_pos hloga 3)) hden

/-- Every finite shifted third-power tail is bounded by its exact integral-test main term. -/
theorem sum_one_div_mul_log_three_le {N : ℝ} (hN : Real.exp 1 ≤ N) (a : ℕ) :
    ∑ i ∈ Finset.range a,
        1 / ((N + (i + 1)) * (Real.log (N + (i + 1))) ^ (3 : ℕ))
      ≤ 1 / (2 * (Real.log N) ^ (2 : ℕ)) := by
  have he1 : (1 : ℝ) < Real.exp 1 := Real.one_lt_exp_iff.mpr zero_lt_one
  have hN1 : 1 < N := lt_of_lt_of_le he1 hN
  have hM : N ≤ N + (a : ℝ) := le_add_of_nonneg_right (Nat.cast_nonneg a)
  have hanti : AntitoneOn (fun x : ℝ => 1 / (x * (Real.log x) ^ (3 : ℕ)))
      (Set.Icc N (N + a)) :=
    antitoneOn_one_div_mul_log_three.mono (fun y hy => le_trans hN hy.1)
  have hsum := hanti.sum_le_integral
  have hcont : ContinuousOn (fun x : ℝ => 1 / (x * (Real.log x) ^ (3 : ℕ)))
      (Set.uIcc N (N + a)) := by
    intro x hx
    rw [Set.uIcc_of_le hM] at hx
    have hx1 : 1 < x := lt_of_lt_of_le hN1 hx.1
    have hx0 : x ≠ 0 := by linarith
    have hlog0 : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx1)
    exact (continuousAt_const.div
      (continuousAt_id.mul ((Real.continuousAt_log hx0).pow 3))
      (mul_ne_zero hx0 (pow_ne_zero 3 hlog0))).continuousWithinAt
  have hderiv : ∀ x ∈ Set.uIcc N (N + (a : ℝ)),
      HasDerivAt (fun x => -(1 / (2 * (Real.log x) ^ (2 : ℕ))))
        (1 / (x * (Real.log x) ^ (3 : ℕ))) x := by
    intro x hx
    rw [Set.uIcc_of_le hM] at hx
    exact hasDerivAt_neg_inv_two_log_sq (lt_of_lt_of_le hN1 hx.1)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable
  rw [hftc] at hsum
  have hlogNa : 0 < Real.log (N + (a : ℝ)) :=
    Real.log_pos (lt_of_lt_of_le hN1 hM)
  have hfNa : -(1 / (2 * (Real.log (N + (a : ℝ))) ^ (2 : ℕ))) ≤ 0 := by
    exact neg_nonpos.mpr (one_div_nonneg.mpr (mul_nonneg (by norm_num) (pow_nonneg hlogNa.le 2)))
  calc
    ∑ i ∈ Finset.range a,
        1 / ((N + (i + 1)) * (Real.log (N + (i + 1))) ^ (3 : ℕ))
        ≤ -(1 / (2 * (Real.log (N + (a : ℝ))) ^ (2 : ℕ)))
            - (-(1 / (2 * (Real.log N) ^ (2 : ℕ)))) := by
              convert hsum using 2 with i
              push_cast
              ring
    _ ≤ 0 - (-(1 / (2 * (Real.log N) ^ (2 : ℕ)))) := by linarith
    _ = 1 / (2 * (Real.log N) ^ (2 : ℕ)) := by ring

/-- The shifted third-power reciprocal-log tail is summable. -/
theorem summable_one_div_mul_log_three {N : ℝ} (hN : Real.exp 1 ≤ N) :
    Summable fun i : ℕ =>
      1 / ((N + (i + 1)) * (Real.log (N + (i + 1))) ^ (3 : ℕ)) := by
  apply summable_of_sum_range_le
  · intro n
    have he1 : (1 : ℝ) < Real.exp 1 := Real.one_lt_exp_iff.mpr zero_lt_one
    have hpos : 0 < Real.log (N + ((n : ℝ) + 1)) :=
      Real.log_pos (lt_of_lt_of_le he1 (le_trans hN (by
        have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        linarith)))
    exact one_div_nonneg.mpr (mul_nonneg (by
      have : (0 : ℝ) ≤ N := le_trans (Real.exp_pos 1).le hN
      have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith) (pow_nonneg hpos.le 3))
  · exact sum_one_div_mul_log_three_le hN

/-- Every finite shifted tail is bounded by the exact integral-test main term. -/
theorem sum_one_div_mul_log_four_le {N : ℝ} (hN : Real.exp 1 ≤ N) (a : ℕ) :
    ∑ i ∈ Finset.range a,
        1 / ((N + (i + 1)) * (Real.log (N + (i + 1))) ^ (4 : ℕ))
      ≤ 1 / (3 * (Real.log N) ^ (3 : ℕ)) := by
  have he1 : (1 : ℝ) < Real.exp 1 := Real.one_lt_exp_iff.mpr zero_lt_one
  have hN1 : 1 < N := lt_of_lt_of_le he1 hN
  have hM : N ≤ N + (a : ℝ) := le_add_of_nonneg_right (Nat.cast_nonneg a)
  have hanti : AntitoneOn (fun x : ℝ => 1 / (x * (Real.log x) ^ (4 : ℕ)))
      (Set.Icc N (N + a)) :=
    antitoneOn_one_div_mul_log_four.mono (fun y hy => le_trans hN hy.1)
  have hsum := hanti.sum_le_integral
  have hcont : ContinuousOn (fun x : ℝ => 1 / (x * (Real.log x) ^ (4 : ℕ)))
      (Set.uIcc N (N + a)) := by
    intro x hx
    rw [Set.uIcc_of_le hM] at hx
    have hx1 : 1 < x := lt_of_lt_of_le hN1 hx.1
    have hx0 : x ≠ 0 := by linarith
    have hlog0 : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx1)
    exact (continuousAt_const.div
      (continuousAt_id.mul ((Real.continuousAt_log hx0).pow 4))
      (mul_ne_zero hx0 (pow_ne_zero 4 hlog0))).continuousWithinAt
  have hderiv : ∀ x ∈ Set.uIcc N (N + (a : ℝ)),
      HasDerivAt (fun x => -(1 / (3 * (Real.log x) ^ (3 : ℕ))))
        (1 / (x * (Real.log x) ^ (4 : ℕ))) x := by
    intro x hx
    rw [Set.uIcc_of_le hM] at hx
    exact hasDerivAt_neg_inv_log_cube (lt_of_lt_of_le hN1 hx.1)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable
  rw [hftc] at hsum
  have hlogNa : 0 < Real.log (N + (a : ℝ)) :=
    Real.log_pos (lt_of_lt_of_le hN1 hM)
  have hfNa : -(1 / (3 * (Real.log (N + (a : ℝ))) ^ (3 : ℕ))) ≤ 0 := by
    exact neg_nonpos.mpr (one_div_nonneg.mpr (mul_nonneg (by norm_num) (pow_nonneg hlogNa.le 3)))
  calc
    ∑ i ∈ Finset.range a,
        1 / ((N + (i + 1)) * (Real.log (N + (i + 1))) ^ (4 : ℕ))
        ≤ -(1 / (3 * (Real.log (N + (a : ℝ))) ^ (3 : ℕ)))
            - (-(1 / (3 * (Real.log N) ^ (3 : ℕ)))) := by
              convert hsum using 2 with i
              push_cast
              ring
    _ ≤ 0 - (-(1 / (3 * (Real.log N) ^ (3 : ℕ)))) := by linarith
    _ = 1 / (3 * (Real.log N) ^ (3 : ℕ)) := by ring

/-- Infinite shifted-tail form of the fourth-power reciprocal-log integral test. -/
theorem tsum_one_div_mul_log_four_le {N : ℝ} (hN : Real.exp 1 ≤ N) :
    ∑' i : ℕ, 1 / ((N + (i + 1)) * (Real.log (N + (i + 1))) ^ (4 : ℕ))
      ≤ 1 / (3 * (Real.log N) ^ (3 : ℕ)) := by
  apply tsum_le_of_sum_range_le
  · intro n
    have he1 : (1 : ℝ) < Real.exp 1 := Real.one_lt_exp_iff.mpr zero_lt_one
    have hpos : 0 < Real.log (N + ((n : ℝ) + 1)) :=
      Real.log_pos (lt_of_lt_of_le he1 (le_trans hN (by
        have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        linarith)))
    exact one_div_nonneg.mpr (mul_nonneg (by
      have : (0 : ℝ) ≤ N := le_trans (Real.exp_pos 1).le hN
      have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith) (pow_nonneg hpos.le 4))
  · exact sum_one_div_mul_log_four_le hN

end GaloisForLFunctions.HTGeometry
