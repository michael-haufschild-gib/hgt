import Mathlib

/-!
# Decreasing-tail estimate for `log x / x^2`

The prime-power completion bound `(PFK14)` of
`xi-physical-prime-log-aperture-fusion-cross-kernel` reduces (in the dominant `r = 2` band) to the
integral-test tail of `∑ log(n)/n^2`.  This file formalizes that tail through the exact antiderivative
`d/dx[-(log x + 1)/x] = log x / x^2`, giving the improper integral
`∫_{x>N} log x/x^2 = (log N + 1)/N` and the decreasing-tail sum bound
`∑_{n>N} log n/n^2 ≤ (log N + 1)/N` for `N ≥ e`.
-/

open Real

namespace GaloisForLFunctions.HTGeometry

/-- **Antiderivative of `log x / x^2`.**  For `x > 0`, `d/dx[-(log x + 1)/x] = log x / x^2`. -/
theorem hasDerivAt_neg_logLin_tail {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun x => -(Real.log x + 1) / x) (Real.log x / x ^ 2) x := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hlog : HasDerivAt Real.log x⁻¹ x := Real.hasDerivAt_log hx0
  have hg : HasDerivAt (fun x => Real.log x + 1) (x⁻¹) x := by simpa using hlog.add_const 1
  have hF := (hg.neg).div (hasDerivAt_id x) hx0
  convert hF using 1
  simp only [id_eq, Pi.neg_apply]
  field_simp
  ring

open Filter Topology MeasureTheory Set

/-- `-(log x + 1)/x → 0` as `x → ∞`, from `log x/x → 0` and `1/x → 0`. -/
theorem tendsto_neg_logLin_tail_atTop :
    Tendsto (fun x => -(Real.log x + 1) / x) atTop (𝓝 0) := by
  have h1 : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 (by norm_num)
  have h0 : Tendsto (fun x : ℝ => (1 : ℝ) / x) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds (x := (1 : ℝ)) |>.div_atTop tendsto_id
  have hsum : Tendsto (fun x : ℝ => Real.log x / x + 1 / x) atTop (𝓝 0) := by
    simpa using h1.add h0
  have hnegsum : Tendsto (fun x : ℝ => -(Real.log x / x + 1 / x)) atTop (𝓝 0) := by
    simpa using hsum.neg
  refine Tendsto.congr' ?_ hnegsum
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  field_simp

/-- **Improper tail integral.**  `∫_{x>N} log x/x^2 = (log N + 1)/N` for `N ≥ 1`, by the
fundamental theorem of calculus on `[N,∞)` with the antiderivative `hasDerivAt_neg_logLin_tail`. -/
theorem integral_logLin_div_sq_Ioi {N : ℝ} (hN : 1 ≤ N) :
    ∫ x in Set.Ioi N, Real.log x / x ^ 2 = (Real.log N + 1) / N := by
  have hNpos : 0 < N := lt_of_lt_of_le one_pos hN
  have hcont : ContinuousWithinAt (fun x => -(Real.log x + 1) / x) (Set.Ici N) N :=
    (hasDerivAt_neg_logLin_tail hNpos).continuousAt.continuousWithinAt
  have hderiv : ∀ x ∈ Set.Ioi N,
      HasDerivAt (fun x => -(Real.log x + 1) / x) (Real.log x / x ^ 2) x :=
    fun x hx => hasDerivAt_neg_logLin_tail (lt_trans hNpos hx)
  have hpos : ∀ x ∈ Set.Ioi N, 0 ≤ Real.log x / x ^ 2 := by
    intro x hx
    have hx1 : 1 ≤ x := le_of_lt (lt_of_le_of_lt hN hx)
    exact div_nonneg (Real.log_nonneg hx1) (by positivity)
  rw [integral_Ioi_of_hasDerivAt_of_nonneg hcont hderiv hpos tendsto_neg_logLin_tail_atTop]
  ring

/-- `log x / x^2` is antitone on `[e, ∞)`: it is the product of the nonnegative antitone functions
`log x / x` (`log_div_self_antitoneOn`) and `1/x`. -/
theorem antitoneOn_logLin_div_sq :
    AntitoneOn (fun x : ℝ => Real.log x / x ^ 2) (Set.Ici (Real.exp 1)) := by
  intro a ha b hb hab
  simp only
  have hone : (1 : ℝ) ≤ Real.exp 1 := by nlinarith [Real.add_one_le_exp (1 : ℝ)]
  have hapos : 0 < a := lt_of_lt_of_le (Real.exp_pos 1) ha
  have hbpos : 0 < b := lt_of_lt_of_le (Real.exp_pos 1) hb
  have hloga : 0 ≤ Real.log a := Real.log_nonneg (le_trans hone ha)
  have hdiv : Real.log b / b ≤ Real.log a / a := log_div_self_antitoneOn ha hb hab
  have hinv : 1 / b ≤ 1 / a := one_div_le_one_div_of_le hapos hab
  have key : (Real.log b / b) * (1 / b) ≤ (Real.log a / a) * (1 / a) :=
    mul_le_mul hdiv hinv (one_div_nonneg.mpr hbpos.le) (div_nonneg hloga hapos.le)
  have ea : Real.log a / a ^ 2 = (Real.log a / a) * (1 / a) := by rw [sq]; ring
  have eb : Real.log b / b ^ 2 = (Real.log b / b) * (1 / b) := by rw [sq]; ring
  rw [ea, eb]; exact key

/-- Uniform tail-sum bound: for `N ≥ e`, every partial sum `∑_{i<a} log(N+i+1)/(N+i+1)^2` is at
most `(log N + 1)/N`, via `AntitoneOn.sum_le_integral` and the fundamental theorem of calculus
(antiderivative `≤ 0` at the upper endpoint). -/
theorem sum_logLin_div_sq_le {N : ℝ} (hN : Real.exp 1 ≤ N) (a : ℕ) :
    ∑ i ∈ Finset.range a, Real.log (N + (i + 1)) / (N + (i + 1)) ^ 2
      ≤ (Real.log N + 1) / N := by
  have hNpos : 0 < N := lt_of_lt_of_le (Real.exp_pos 1) hN
  have hone : (1 : ℝ) ≤ Real.exp 1 := by nlinarith [Real.add_one_le_exp (1 : ℝ)]
  have hM : N ≤ N + (a : ℝ) := le_add_of_nonneg_right (Nat.cast_nonneg a)
  have hanti : AntitoneOn (fun x => Real.log x / x ^ 2) (Set.Icc N (N + a)) :=
    antitoneOn_logLin_div_sq.mono (fun y hy => le_trans hN hy.1)
  have hsum := hanti.sum_le_integral
  have hcont : ContinuousOn (fun x => Real.log x / x ^ 2) (Set.uIcc N (N + a)) := by
    intro x hx
    rw [Set.uIcc_of_le hM] at hx
    have hxpos : 0 < x := lt_of_lt_of_le hNpos hx.1
    exact ((Real.continuousAt_log hxpos.ne').div (continuousAt_id.pow 2)
      (pow_ne_zero 2 hxpos.ne')).continuousWithinAt
  have hderiv : ∀ x ∈ Set.uIcc N (N + (a : ℝ)),
      HasDerivAt (fun x => -(Real.log x + 1) / x) (Real.log x / x ^ 2) x := by
    intro x hx
    rw [Set.uIcc_of_le hM] at hx
    exact hasDerivAt_neg_logLin_tail (lt_of_lt_of_le hNpos hx.1)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable
  rw [hftc] at hsum
  have hlogNa : 0 ≤ Real.log (N + (a : ℝ)) :=
    Real.log_nonneg (le_trans hone (le_trans hN hM))
  have hfNa : -(Real.log (N + (a : ℝ)) + 1) / (N + (a : ℝ)) ≤ 0 := by
    apply div_nonpos_of_nonpos_of_nonneg
    · linarith
    · positivity
  calc ∑ i ∈ Finset.range a, Real.log (N + (i + 1)) / (N + (i + 1)) ^ 2
      ≤ (-(Real.log (N + (a:ℝ)) + 1) / (N + (a:ℝ))) - (-(Real.log N + 1) / N) := by
        convert hsum using 2 with i
        push_cast; ring
    _ ≤ 0 - (-(Real.log N + 1) / N) := by linarith [hfNa]
    _ = (Real.log N + 1) / N := by ring

/-- Tail-series bound: `∑_{n>N} log n/n^2 ≤ (log N + 1)/N` for `N ≥ e`, from the uniform
partial-sum bound via `tsum_le_of_sum_range_le`. -/
theorem tsum_logLin_div_sq_le {N : ℝ} (hN : Real.exp 1 ≤ N) :
    ∑' i : ℕ, Real.log (N + (i + 1)) / (N + (i + 1)) ^ 2 ≤ (Real.log N + 1) / N := by
  apply tsum_le_of_sum_range_le
  · intro n
    have hNpos : 0 < N := lt_of_lt_of_le (Real.exp_pos 1) hN
    have hone : (1 : ℝ) ≤ Real.exp 1 := by nlinarith [Real.add_one_le_exp (1 : ℝ)]
    have : (1:ℝ) ≤ N + ((n:ℝ) + 1) := by
      have : (1:ℝ) ≤ N := le_trans hone hN
      have : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
      linarith
    exact div_nonneg (Real.log_nonneg this) (by positivity)
  · intro n
    exact sum_logLin_div_sq_le hN n

open Asymptotics in
/-- `log n / n^2` is summable over `ℕ`: it is `O(n^{-3/2})` since `log x = o(x^{1/2})`. -/
theorem summable_logLin_div_sq : Summable (fun n : ℕ => Real.log n / n ^ 2) := by
  apply summable_of_isBigO_nat (g := fun n : ℕ => 1 / (n : ℝ) ^ ((3 : ℝ) / 2))
  · rw [Real.summable_one_div_nat_rpow]; norm_num
  · have hreal : (fun x : ℝ => Real.log x / x ^ 2) =O[atTop] (fun x : ℝ => 1 / x ^ ((3 : ℝ) / 2)) := by
      have hlO : (fun x : ℝ => Real.log x) =O[atTop] (fun x : ℝ => x ^ ((1:ℝ)/2)) :=
        (isLittleO_log_rpow_atTop (r := (1:ℝ)/2) (by norm_num)).isBigO
      have hmul := hlO.mul (isBigO_refl (fun x : ℝ => (x ^ (2:ℝ))⁻¹) atTop)
      refine hmul.congr' ?_ ?_
      · filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
        have : Real.log x / x ^ 2 = Real.log x * (x ^ (2:ℝ))⁻¹ := by
          rw [← Real.rpow_natCast x 2, div_eq_mul_inv]; norm_num
        exact this.symm
      · filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
        show x ^ ((1:ℝ)/2) * (x ^ (2:ℝ))⁻¹ = 1 / x ^ ((3:ℝ)/2)
        have e1 : (x ^ (2:ℝ))⁻¹ = x ^ (-(2:ℝ)) := (Real.rpow_neg hx.le 2).symm
        have e2 : x ^ (-((3:ℝ)/2)) = 1 / x ^ ((3:ℝ)/2) := by rw [Real.rpow_neg hx.le, one_div]
        rw [e1, ← Real.rpow_add hx, ← e2]; congr 1; norm_num
    exact hreal.comp_tendsto tendsto_natCast_atTop_atTop

end GaloisForLFunctions.HTGeometry
