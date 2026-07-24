import Mathlib

/-!
# Antiderivative of `(log x / x)^2`

The decreasing-tail estimate behind the prime-diagonal bound `(PFK11)`
(`∑_{n≥N} (log n / n)^2 ≪ (log(N)^2 + 2 log N + 2)/N`, of
`xi-physical-prime-log-aperture-fusion-cross-kernel`) rests on the exact antiderivative
`d/dx[-(log²x + 2 log x + 2)/x] = (log x / x)^2`.  This file formalizes that antiderivative, the
analytic core from which the improper tail integral `∫_{x>N} (log x/x)^2 = (log²N+2logN+2)/N`
follows by the fundamental theorem of calculus.
-/

open Real

namespace GaloisForLFunctions.HTGeometry

/-- **Antiderivative of `(log x / x)^2`.**  For `x > 0`,
`d/dx[-(log²x + 2 log x + 2)/x] = (log x / x)^2`. -/
theorem hasDerivAt_neg_logSq_tail {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun x => -(Real.log x ^ 2 + 2 * Real.log x + 2) / x)
      ((Real.log x / x) ^ 2) x := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hlog : HasDerivAt Real.log x⁻¹ x := Real.hasDerivAt_log hx0
  have hlogsq : HasDerivAt (fun x => Real.log x ^ 2) (2 * Real.log x * x⁻¹) x := by
    simpa using hlog.pow 2
  have h2log : HasDerivAt (fun x => 2 * Real.log x) (2 * x⁻¹) x := by
    simpa using hlog.const_mul 2
  have hg : HasDerivAt (fun x => Real.log x ^ 2 + 2 * Real.log x + 2)
      (2 * Real.log x * x⁻¹ + 2 * x⁻¹) x := by
    simpa using (hlogsq.add h2log).add_const 2
  have hF := (hg.neg).div (hasDerivAt_id x) hx0
  convert hF using 1
  simp only [id_eq, Pi.neg_apply]
  field_simp
  ring

open Filter Topology MeasureTheory Set

theorem tendsto_neg_logSq_tail_atTop :
    Tendsto (fun x => -(Real.log x ^ 2 + 2 * Real.log x + 2) / x) atTop (𝓝 0) := by
  have h2 : Tendsto (fun x : ℝ => Real.log x ^ 2 / x) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 (by norm_num)
  have h1 : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 (by norm_num)
  have h0 : Tendsto (fun x : ℝ => (2 : ℝ) / x) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds (x := (2 : ℝ)) |>.div_atTop tendsto_id
  have hsum : Tendsto (fun x : ℝ => Real.log x ^ 2 / x + 2 * (Real.log x / x) + 2 / x)
      atTop (𝓝 0) := by simpa using (h2.add (h1.const_mul 2)).add h0
  have hnegsum : Tendsto (fun x : ℝ => -(Real.log x ^ 2 / x + 2 * (Real.log x / x) + 2 / x))
      atTop (𝓝 0) := by simpa using hsum.neg
  refine Tendsto.congr' ?_ hnegsum
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  field_simp

/-- **Improper tail integral (core of PFK11).**  `∫_{x>N} (log x/x)^2 = (log²N + 2 log N + 2)/N`. -/
theorem integral_logSq_div_sq_Ioi {N : ℝ} (hN : 0 < N) :
    ∫ x in Set.Ioi N, (Real.log x / x) ^ 2 = (Real.log N ^ 2 + 2 * Real.log N + 2) / N := by
  have hcont : ContinuousWithinAt (fun x => -(Real.log x ^ 2 + 2 * Real.log x + 2) / x)
      (Set.Ici N) N := (hasDerivAt_neg_logSq_tail hN).continuousAt.continuousWithinAt
  have hderiv : ∀ x ∈ Set.Ioi N,
      HasDerivAt (fun x => -(Real.log x ^ 2 + 2 * Real.log x + 2) / x) ((Real.log x / x) ^ 2) x :=
    fun x hx => hasDerivAt_neg_logSq_tail (lt_trans hN hx)
  have hpos : ∀ x ∈ Set.Ioi N, 0 ≤ (Real.log x / x) ^ 2 := fun x _ => sq_nonneg _
  rw [integral_Ioi_of_hasDerivAt_of_nonneg hcont hderiv hpos tendsto_neg_logSq_tail_atTop]
  ring

/-- `(log x / x)^2` is antitone on `[e, ∞)`: it is the square of the nonnegative antitone
function `log x / x` (mathlib `log_div_self_antitoneOn`). -/
theorem antitoneOn_logSq_div_sq :
    AntitoneOn (fun x : ℝ => (Real.log x / x) ^ 2) (Set.Ici (Real.exp 1)) := by
  intro a ha b hb hab
  simp only
  have hone : (1 : ℝ) ≤ Real.exp 1 := by nlinarith [Real.add_one_le_exp (1 : ℝ)]
  have hbpos : 0 < b := lt_of_lt_of_le (Real.exp_pos 1) hb
  have hlogb : 0 ≤ Real.log b := Real.log_nonneg (le_trans hone hb)
  have h0 : 0 ≤ Real.log b / b := div_nonneg hlogb (le_of_lt hbpos)
  have hle : Real.log b / b ≤ Real.log a / a := log_div_self_antitoneOn ha hb hab
  exact pow_le_pow_left₀ h0 hle 2

/-- Uniform tail-sum bound: for `N ≥ e`, every partial sum
`∑_{i<a} (log(N+i+1)/(N+i+1))^2` is bounded by the closed form `(log²N + 2 log N + 2)/N`.
Proof: `AntitoneOn.sum_le_integral` bounds the partial sum by `∫_N^{N+a} (log x/x)^2`, which the
fundamental theorem of calculus (antiderivative `hasDerivAt_neg_logSq_tail`) evaluates to
`F(N+a) - F(N)` with `F ≤ 0`, so `≤ -F(N)`. -/
theorem sum_logSq_div_sq_le {N : ℝ} (hN : Real.exp 1 ≤ N) (a : ℕ) :
    ∑ i ∈ Finset.range a, (Real.log (N + (i + 1)) / (N + (i + 1))) ^ 2
      ≤ (Real.log N ^ 2 + 2 * Real.log N + 2) / N := by
  have hNpos : 0 < N := lt_of_lt_of_le (Real.exp_pos 1) hN
  have hM : N ≤ N + (a : ℝ) := le_add_of_nonneg_right (Nat.cast_nonneg a)
  have hanti : AntitoneOn (fun x => (Real.log x / x) ^ 2) (Set.Icc N (N + a)) :=
    antitoneOn_logSq_div_sq.mono (fun y hy => le_trans hN hy.1)
  have hsum := hanti.sum_le_integral
  have hcont : ContinuousOn (fun x => (Real.log x / x) ^ 2) (Set.uIcc N (N + a)) := by
    intro x hx
    rw [Set.uIcc_of_le hM] at hx
    have hxpos : 0 < x := lt_of_lt_of_le hNpos hx.1
    exact (((Real.continuousAt_log hxpos.ne').div continuousAt_id hxpos.ne').pow 2).continuousWithinAt
  have hderiv : ∀ x ∈ Set.uIcc N (N + (a : ℝ)),
      HasDerivAt (fun x => -(Real.log x ^ 2 + 2 * Real.log x + 2) / x) ((Real.log x / x) ^ 2) x := by
    intro x hx
    rw [Set.uIcc_of_le hM] at hx
    exact hasDerivAt_neg_logSq_tail (lt_of_lt_of_le hNpos hx.1)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable
  rw [hftc] at hsum
  have hfNa : -(Real.log (N + (a : ℝ)) ^ 2 + 2 * Real.log (N + (a : ℝ)) + 2) / (N + (a : ℝ)) ≤ 0 := by
    apply div_nonpos_of_nonpos_of_nonneg
    · nlinarith [sq_nonneg (Real.log (N + (a : ℝ)) + 1)]
    · positivity
  have hfN : -(Real.log N ^ 2 + 2 * Real.log N + 2) / N = -((Real.log N ^ 2 + 2 * Real.log N + 2) / N) := by
    ring
  calc ∑ i ∈ Finset.range a, (Real.log (N + (i + 1)) / (N + (i + 1))) ^ 2
      ≤ (-(Real.log (N + (a:ℝ)) ^ 2 + 2 * Real.log (N + (a:ℝ)) + 2) / (N + (a:ℝ)))
        - (-(Real.log N ^ 2 + 2 * Real.log N + 2) / N) := by
        convert hsum using 2 with i
        push_cast; ring
    _ ≤ 0 - (-(Real.log N ^ 2 + 2 * Real.log N + 2) / N) := by linarith [hfNa]
    _ = (Real.log N ^ 2 + 2 * Real.log N + 2) / N := by ring

/-- Tail-series bound: `∑_{i} (log(N+i+1)/(N+i+1))^2 ≤ (log²N + 2 log N + 2)/N` for `N ≥ e`.
The uniform partial-sum bound `sum_logSq_div_sq_le` bounds the series via `tsum_le_of_sum_range_le`. -/
theorem tsum_logSq_div_sq_le {N : ℝ} (hN : Real.exp 1 ≤ N) :
    ∑' i : ℕ, (Real.log (N + (i + 1)) / (N + (i + 1))) ^ 2
      ≤ (Real.log N ^ 2 + 2 * Real.log N + 2) / N := by
  apply tsum_le_of_sum_range_le (fun n => sq_nonneg _)
  intro n
  exact sum_logSq_div_sq_le hN n

open Asymptotics in
/-- `(log n / n)^2` is summable over `ℕ`: it is `O(n^{-3/2})` since `(log x)^2 = o(x^{1/2})`
(`isLittleO_log_rpow_rpow_atTop`), and `∑ n^{-3/2}` converges. -/
theorem summable_logSq_div_sq : Summable (fun n : ℕ => (Real.log n / n) ^ 2) := by
  apply summable_of_isBigO_nat (g := fun n : ℕ => 1 / (n : ℝ) ^ ((3 : ℝ) / 2))
  · rw [Real.summable_one_div_nat_rpow]; norm_num
  · have hreal : (fun x : ℝ => (Real.log x / x) ^ 2) =O[atTop]
        (fun x : ℝ => 1 / x ^ ((3 : ℝ) / 2)) := by
      have hrpow := (isLittleO_log_rpow_rpow_atTop (s := (1:ℝ)/2) 2 (by norm_num)).isBigO
      have hlO : (fun x : ℝ => Real.log x ^ (2:ℕ)) =O[atTop] (fun x : ℝ => x ^ ((1:ℝ)/2)) := by
        refine hrpow.congr' ?_ EventuallyEq.rfl
        filter_upwards with x
        rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
      have hmul := hlO.mul (isBigO_refl (fun x : ℝ => (x ^ (2:ℝ))⁻¹) atTop)
      refine hmul.congr' ?_ ?_
      · filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
        have hA : (Real.log x / x) ^ 2 = Real.log x ^ (2:ℕ) * (x ^ (2:ℝ))⁻¹ := by
          rw [div_pow, ← Real.rpow_natCast x 2, div_eq_mul_inv]; norm_num
        exact hA.symm
      · filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
        show x ^ ((1:ℝ)/2) * (x ^ (2:ℝ))⁻¹ = 1 / x ^ ((3:ℝ)/2)
        have e1 : (x ^ (2:ℝ))⁻¹ = x ^ (-(2:ℝ)) := (Real.rpow_neg hx.le 2).symm
        have e2 : x ^ (-((3:ℝ)/2)) = 1 / x ^ ((3:ℝ)/2) := by
          rw [Real.rpow_neg hx.le, one_div]
        rw [e1, ← Real.rpow_add hx, ← e2]
        congr 1
        norm_num
    exact hreal.comp_tendsto tendsto_natCast_atTop_atTop

end GaloisForLFunctions.HTGeometry
