import GaloisForLFunctions.HTGeometry.ReciprocalLogPowerTail

/-!
# Reciprocal-log tails at arbitrary fixed power

For every positive natural `p`, the function

`x ↦ 1 / (x * (log x)^(p+1))`

has antiderivative `-1 / (p * (log x)^p)`.  Monotonicity and the integral test give the exact
finite and infinite tail bounds needed by higher logarithmic Möbius kernels.
-/

open Real Filter Topology MeasureTheory Set

namespace GaloisForLFunctions.HTGeometry

/-- Exact reciprocal-log antiderivative at every positive natural power. -/
theorem hasDerivAt_neg_inv_log_pow
    {p : ℕ} (hp : 0 < p) {x : ℝ} (hx : 1 < x) :
    HasDerivAt (fun y : ℝ => -(1 / ((p : ℝ) * Real.log y ^ p)))
      (1 / (x * Real.log x ^ (p + 1))) x := by
  have hx0 : x ≠ 0 := by linarith
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  have hlog0 : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx)
  have hden := ((Real.hasDerivAt_log hx0).pow p).const_mul (p : ℝ)
  have hinv := hden.inv (mul_ne_zero hpR (pow_ne_zero p hlog0))
  have hneg := hinv.neg
  have hnegfun : (-(fun y : ℝ => (p : ℝ) * (Real.log ^ p) y)⁻¹) =
      (fun y : ℝ => -((p : ℝ) * Real.log y ^ p)⁻¹) := by
    funext y
    rfl
  rw [hnegfun] at hneg
  have hfun : (fun y : ℝ => -(1 / ((p : ℝ) * Real.log y ^ p))) =
      (fun y : ℝ => -((p : ℝ) * Real.log y ^ p)⁻¹) := by
    funext y
    rw [one_div]
  rw [hfun]
  refine hneg.congr_deriv ?_
  simp only [Pi.pow_apply]
  field_simp
  rw [← pow_add, ← pow_mul]
  congr 1
  omega

/-- The reciprocal-log integrand decreases beyond `e` at every successor power. -/
theorem antitoneOn_one_div_mul_log_pow_succ (p : ℕ) :
    AntitoneOn (fun x : ℝ => 1 / (x * Real.log x ^ (p + 1)))
      (Set.Ici (Real.exp 1)) := by
  intro a ha b hb hab
  have he1 : (1 : ℝ) < Real.exp 1 := Real.one_lt_exp_iff.mpr zero_lt_one
  have ha1 : 1 < a := lt_of_lt_of_le he1 ha
  have hb1 : 1 < b := lt_of_lt_of_le ha1 hab
  have hloga : 0 < Real.log a := Real.log_pos ha1
  have hlogb : 0 < Real.log b := Real.log_pos hb1
  have hlogle : Real.log a ≤ Real.log b := Real.log_le_log (by linarith) hab
  have hpowle : Real.log a ^ (p + 1) ≤ Real.log b ^ (p + 1) :=
    pow_le_pow_left₀ hloga.le hlogle (p + 1)
  have hden : a * Real.log a ^ (p + 1) ≤ b * Real.log b ^ (p + 1) :=
    mul_le_mul hab hpowle (pow_nonneg hloga.le _) (by linarith)
  exact one_div_le_one_div_of_le
    (mul_pos (by linarith) (pow_pos hloga (p + 1))) hden

/-- Finite shifted reciprocal-log tail bounded by its exact integral-test main term. -/
theorem sum_one_div_mul_log_pow_succ_le
    {p : ℕ} (hp : 0 < p) {N : ℝ} (hN : Real.exp 1 ≤ N) (a : ℕ) :
    ∑ i ∈ Finset.range a,
        1 / ((N + (i + 1)) * Real.log (N + (i + 1)) ^ (p + 1))
      ≤ 1 / ((p : ℝ) * Real.log N ^ p) := by
  have he1 : (1 : ℝ) < Real.exp 1 := Real.one_lt_exp_iff.mpr zero_lt_one
  have hN1 : 1 < N := lt_of_lt_of_le he1 hN
  have hM : N ≤ N + (a : ℝ) := le_add_of_nonneg_right (Nat.cast_nonneg a)
  have hanti : AntitoneOn
      (fun x : ℝ => 1 / (x * Real.log x ^ (p + 1)))
      (Set.Icc N (N + a)) :=
    (antitoneOn_one_div_mul_log_pow_succ p).mono
      (fun y hy => le_trans hN hy.1)
  have hsum := hanti.sum_le_integral
  have hcont : ContinuousOn
      (fun x : ℝ => 1 / (x * Real.log x ^ (p + 1)))
      (Set.uIcc N (N + a)) := by
    intro x hx
    rw [Set.uIcc_of_le hM] at hx
    have hx1 : 1 < x := lt_of_lt_of_le hN1 hx.1
    have hx0 : x ≠ 0 := by linarith
    have hlog0 : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx1)
    exact (continuousAt_const.div
      (continuousAt_id.mul ((Real.continuousAt_log hx0).pow (p + 1)))
      (mul_ne_zero hx0 (pow_ne_zero (p + 1) hlog0))).continuousWithinAt
  have hderiv : ∀ x ∈ Set.uIcc N (N + (a : ℝ)),
      HasDerivAt (fun y : ℝ => -(1 / ((p : ℝ) * Real.log y ^ p)))
        (1 / (x * Real.log x ^ (p + 1))) x := by
    intro x hx
    rw [Set.uIcc_of_le hM] at hx
    exact hasDerivAt_neg_inv_log_pow hp (lt_of_lt_of_le hN1 hx.1)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    hderiv hcont.intervalIntegrable
  rw [hftc] at hsum
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hlogNa : 0 < Real.log (N + (a : ℝ)) :=
    Real.log_pos (lt_of_lt_of_le hN1 hM)
  have hfNa : -(1 / ((p : ℝ) * Real.log (N + (a : ℝ)) ^ p)) ≤ 0 := by
    exact neg_nonpos.mpr (one_div_nonneg.mpr
      (mul_nonneg hpR.le (pow_nonneg hlogNa.le p)))
  calc
    ∑ i ∈ Finset.range a,
        1 / ((N + (i + 1)) * Real.log (N + (i + 1)) ^ (p + 1))
        ≤ -(1 / ((p : ℝ) * Real.log (N + (a : ℝ)) ^ p)) -
            (-(1 / ((p : ℝ) * Real.log N ^ p))) := by
          convert hsum using 2 with i
          push_cast
          ring
    _ ≤ 0 - (-(1 / ((p : ℝ) * Real.log N ^ p))) := by linarith
    _ = 1 / ((p : ℝ) * Real.log N ^ p) := by ring

/-- Shifted reciprocal-log tail is summable at every exponent greater than one. -/
theorem summable_one_div_mul_log_pow_succ
    {p : ℕ} (hp : 0 < p) {N : ℝ} (hN : Real.exp 1 ≤ N) :
    Summable fun i : ℕ =>
      1 / ((N + (i + 1)) * Real.log (N + (i + 1)) ^ (p + 1)) := by
  apply summable_of_sum_range_le
  · intro n
    have he1 : (1 : ℝ) < Real.exp 1 := Real.one_lt_exp_iff.mpr zero_lt_one
    have hn0 : 0 ≤ (n : ℝ) + 1 := by positivity
    have hshift : N ≤ N + ((n : ℝ) + 1) := le_add_of_nonneg_right hn0
    have hpos : 0 < Real.log (N + ((n : ℝ) + 1)) :=
      Real.log_pos (lt_of_lt_of_le he1 (hN.trans hshift))
    exact one_div_nonneg.mpr (mul_nonneg
      ((Real.exp_pos 1).le.trans (hN.trans hshift))
      (pow_nonneg hpos.le (p + 1)))
  · exact sum_one_div_mul_log_pow_succ_le hp hN

/-- Infinite shifted reciprocal-log tail bound. -/
theorem tsum_one_div_mul_log_pow_succ_le
    {p : ℕ} (hp : 0 < p) {N : ℝ} (hN : Real.exp 1 ≤ N) :
    ∑' i : ℕ,
        1 / ((N + (i + 1)) * Real.log (N + (i + 1)) ^ (p + 1))
      ≤ 1 / ((p : ℝ) * Real.log N ^ p) := by
  apply tsum_le_of_sum_range_le
  · intro n
    have he1 : (1 : ℝ) < Real.exp 1 := Real.one_lt_exp_iff.mpr zero_lt_one
    have hn0 : 0 ≤ (n : ℝ) + 1 := by positivity
    have hshift : N ≤ N + ((n : ℝ) + 1) := le_add_of_nonneg_right hn0
    have hpos : 0 < Real.log (N + ((n : ℝ) + 1)) :=
      Real.log_pos (lt_of_lt_of_le he1 (hN.trans hshift))
    exact one_div_nonneg.mpr (mul_nonneg
      ((Real.exp_pos 1).le.trans (hN.trans hshift))
      (pow_nonneg hpos.le (p + 1)))
  · exact sum_one_div_mul_log_pow_succ_le hp hN

end GaloisForLFunctions.HTGeometry
