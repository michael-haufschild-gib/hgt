import GaloisForLFunctions.TransHorizonIncidenceMechanics.TheOscillatingSmoothPowerIsPaidExactlyAtTheZerosOfZeta

/-!
# The log-twisted oscillating smooth power is paid exactly at the double zeros of ζ

For `0 < ε ≤ 1/2`, `t ∈ ℝ` and `ρ = 1 − ε + it`, the receiver of
`d^{-ε} cos(t log d) log d` is bounded **if and only if** `ζ(ρ) = ζ'(ρ) = 0`
(`receiverBounded_logOscillatingSmoothPower_iff`). Hence all zeros of `ζ` in `1/2 ≤ Re s < 1` are
simple iff no such weight is paid (`forall_simple_zero_iff_forall_not_receiverBounded`): the
receiver reads the order of vanishing, not only the zero set.

* **Differentiating the floor-sum asymptotic in `ρ`.** For fixed `n` the remainder
  `R_n(ρ) = D_ρ(n) − ζ(2 − ρ) n − ζ(ρ) n^ρ/ρ` is holomorphic on the strip
  (`differentiableAt_floorRemainder`) and `|R_n(ρ)| ≤ K (√n)^{1 − ε/2}` uniformly on the disc
  `|ρ − ρ₀| ≤ ε/2` (`norm_floorRemainder_le_of_mem_closedBall`). Cauchy's estimate gives
  `|∂_ρ R_n(ρ₀)| ≤ (2K/ε)(√n)^{1−ε/2}`, an exponent below `1/2`.
* **The log-twisted prefix.** `Σ_{d ≤ n} d^{ρ−1} log d ⌊n/d⌋ = ∂_ρ D_ρ(n)` and the mean is
  `−Re ζ'(2 − ρ)`, so the prefix is `Re(n^ρ (b + a log n)) + O(n^{1/2 − ε/4})`,
  `a = ζ(ρ)/ρ`, `b = ζ'(ρ)/ρ − ζ(ρ)/ρ²` (`abs_weightCenteredPrefix_logOscillatingSmoothPower_sub_le`).
* **Both directions.** At a double zero `a = b = 0` and the receiver is paid. Otherwise the main
  term carries the energy `Σ Re(n^{it}(b + a log n))²/(2n)`, which grows like `(|a|²/4)(log T)³`
  when `a ≠ 0` (the oscillating part is `O((log T)²)` by Abel summation against the bounded sums of
  `n^{-(1−2it)}`) and like `(|b|²/4) log T` when `a = 0 ≠ b`.
-/

open Finset Filter Topology Complex Metric
open scoped BigOperators

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-! ### The remainder as a holomorphic function of the exponent -/

/-- The floor-sum remainder `R_n(ρ) = D_ρ(n) − ζ(2 − ρ) n − ζ(ρ) n^ρ/ρ`. -/
def floorRemainder (n : ℕ) (ρ : ℂ) : ℂ :=
  cpowFloorSum ρ n - riemannZeta (2 - ρ) * n - riemannZeta ρ * ((n : ℝ) : ℂ) ^ ρ / ρ

theorem hasDerivAt_cpowFloorSum (n : ℕ) (ρ : ℂ) :
    HasDerivAt (fun ρ : ℂ => cpowFloorSum ρ n)
      (∑ d ∈ Icc 1 n, ((d : ℝ) : ℂ) ^ (ρ - 1) * (Real.log d : ℂ) * ((n / d : ℕ) : ℂ)) ρ := by
  unfold cpowFloorSum
  refine HasDerivAt.fun_sum fun d hd => ?_
  have hd0 : ((d : ℝ) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < d := by exact_mod_cast (mem_Icc.mp hd).1
    exact_mod_cast this.ne'
  have h := (((hasDerivAt_id ρ).sub_const 1).const_cpow (c := ((d : ℝ) : ℂ)) (Or.inl hd0)).mul_const
    ((n / d : ℕ) : ℂ)
  rw [← Complex.ofReal_log (Nat.cast_nonneg d)] at h
  simpa only [id, mul_one] using h

theorem hasDerivAt_zeta_two_sub {ρ : ℂ} (hρ1 : ρ ≠ 1) :
    HasDerivAt (fun ρ : ℂ => riemannZeta (2 - ρ)) (-deriv riemannZeta (2 - ρ)) ρ := by
  have h2 : (2 : ℂ) - ρ ≠ 1 := fun h => hρ1 (by linear_combination -h)
  have h := (differentiableAt_riemannZeta h2).hasDerivAt.comp ρ
    ((hasDerivAt_const ρ (2 : ℂ)).sub (hasDerivAt_id' ρ))
  rw [show deriv riemannZeta (2 - ρ) * (0 - 1) = -deriv riemannZeta (2 - ρ) by ring] at h
  exact h

theorem hasDerivAt_zeta_mul_cpow_div {ρ : ℂ} (hρ0 : ρ ≠ 0) (hρ1 : ρ ≠ 1) {n : ℕ} (hn : 1 ≤ n) :
    HasDerivAt (fun ρ : ℂ => riemannZeta ρ * ((n : ℝ) : ℂ) ^ ρ / ρ)
      (((n : ℝ) : ℂ) ^ ρ * ((deriv riemannZeta ρ / ρ - riemannZeta ρ / ρ ^ 2) +
        riemannZeta ρ / ρ * (Real.log n : ℂ))) ρ := by
  have hn0 : ((n : ℝ) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < n := by exact_mod_cast hn
    exact_mod_cast this.ne'
  have hz := (differentiableAt_riemannZeta hρ1).hasDerivAt
  have hc := (hasDerivAt_id ρ).const_cpow (c := ((n : ℝ) : ℂ)) (Or.inl hn0)
  have h := (hz.mul hc).div (hasDerivAt_id ρ) hρ0
  rw [← Complex.ofReal_log (Nat.cast_nonneg n)] at h
  refine h.congr_deriv ?_
  simp only [id, Pi.mul_apply]
  field_simp
  ring

/-- `R_n` is holomorphic away from `ρ ∈ {0, 1}`. -/
theorem differentiableAt_floorRemainder (n : ℕ) {ρ : ℂ} (hρ0 : ρ ≠ 0) (hρ1 : ρ ≠ 1) :
    DifferentiableAt ℂ (floorRemainder n) ρ := by
  unfold floorRemainder
  have h1 := (hasDerivAt_cpowFloorSum n ρ).differentiableAt
  have h2 := ((hasDerivAt_zeta_two_sub hρ1).differentiableAt).mul_const (n : ℂ)
  have hz := differentiableAt_riemannZeta hρ1
  have hc : DifferentiableAt ℂ (fun ρ : ℂ => ((n : ℝ) : ℂ) ^ ρ) ρ :=
    differentiableAt_id.const_cpow (Or.inr hρ0)
  exact (h1.sub h2).sub ((hz.mul hc).div differentiableAt_id hρ0)

/-- The derivative of `R_n` at `ρ`. -/
theorem deriv_floorRemainder {ρ : ℂ} (hρ0 : ρ ≠ 0) (hρ1 : ρ ≠ 1) {n : ℕ} (hn : 1 ≤ n) :
    deriv (floorRemainder n) ρ =
      ∑ d ∈ Icc 1 n, ((d : ℝ) : ℂ) ^ (ρ - 1) * (Real.log d : ℂ) * ((n / d : ℕ) : ℂ) +
        deriv riemannZeta (2 - ρ) * n -
        ((n : ℝ) : ℂ) ^ ρ * ((deriv riemannZeta ρ / ρ - riemannZeta ρ / ρ ^ 2) +
          riemannZeta ρ / ρ * (Real.log n : ℂ)) := by
  have h := ((hasDerivAt_cpowFloorSum n ρ).sub ((hasDerivAt_zeta_two_sub hρ1).mul_const (n : ℂ))).sub
    (hasDerivAt_zeta_mul_cpow_div hρ0 hρ1 hn)
  exact h.deriv.trans (by ring)

/-! ### A uniform bound on a disc -/

/-- A uniform bound for the partial-sum rate on a box of exponents. -/
theorem partialSumRate_le {w : ℂ} {a b M : ℝ} (ha : 0 < a) (haw : a ≤ w.re) (hwb : w.re ≤ b)
    (hwM : ‖w‖ ≤ M) : partialSumRate w ≤ (M * (1 + 1 / a) + 1) * (2 : ℝ) ^ b := by
  have hw0 : 0 < w.re := lt_of_lt_of_le ha haw
  unfold partialSumRate
  have h1 : 1 / w.re ≤ 1 / a := one_div_le_one_div_of_le ha haw
  have h2 : (2 : ℝ) ^ w.re ≤ (2 : ℝ) ^ b := Real.rpow_le_rpow_of_exponent_le (by norm_num) hwb
  have h3 : ‖w‖ * (1 + 1 / w.re) ≤ M * (1 + 1 / a) :=
    mul_le_mul hwM (by linarith) (by positivity) ((norm_nonneg _).trans hwM)
  have h4 : 0 ≤ ‖w‖ * (1 + 1 / w.re) + 1 := by positivity
  calc (‖w‖ * (1 + 1 / w.re) + 1) * (2 : ℝ) ^ w.re ≤ (‖w‖ * (1 + 1 / w.re) + 1) * (2 : ℝ) ^ b :=
        mul_le_mul_of_nonneg_left h2 h4
    _ ≤ (M * (1 + 1 / a) + 1) * (2 : ℝ) ^ b :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)

theorem floorSumRate_nonneg {ρ : ℂ} (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1) : 0 ≤ floorSumRate ρ := by
  unfold floorSumRate
  have h1 := partialSumRate_nonneg (w := 2 - ρ) (by rw [sub_re]; norm_num; linarith)
  have h2 := partialSumRate_nonneg (w := ρ) hρ0
  have h3 := partialSumRate_nonneg (w := 1 - ρ) (by rw [sub_re, one_re]; linarith)
  positivity

/-- The disc rate: a bound for `floorSumRate` on `|ρ − (1 − ε + it)| ≤ ε/2`. -/
def discRate (ε t : ℝ) : ℝ :=
  4 + ((2 + (2 + |t|)) * (1 + 1 / 1) + 1) * (2 : ℝ) ^ (2 : ℝ) +
    ((2 + |t|) * (1 + 1 / (1 / 4)) + 1) * (2 : ℝ) ^ (1 : ℝ) * 4 +
    2 * (((1 + (2 + |t|)) * (1 + 1 / (ε / 2)) + 1) * (2 : ℝ) ^ (1 : ℝ)) + (1 + 4)

theorem floorSumRate_le_discRate {ε t : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) {ρ : ℂ}
    (hρ : ρ ∈ closedBall (oscillationExponent ε t) (ε / 2)) : floorSumRate ρ ≤ discRate ε t := by
  rw [mem_closedBall, dist_eq_norm] at hρ
  have hre := (Complex.abs_re_le_norm (ρ - oscillationExponent ε t)).trans hρ
  rw [sub_re, oscillationExponent_re, abs_le] at hre
  have hρ0 : ‖oscillationExponent ε t‖ ≤ 1 + |t| := by
    unfold oscillationExponent
    refine (norm_add_le _ _).trans ?_
    rw [Complex.norm_real, norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    linarith [abs_nonneg t]
  have hnorm : ‖ρ‖ ≤ 2 + |t| := by
    have := norm_add_le (ρ - oscillationExponent ε t) (oscillationExponent ε t)
    rw [sub_add_cancel] at this
    linarith
  have hreρ : 1 / 4 ≤ ρ.re := by linarith
  have hreρ1 : ρ.re ≤ 1 := by linarith
  have hpos : 0 < ‖ρ‖ := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 4)
    (hreρ.trans (Complex.re_le_norm ρ))
  have hinv : 1 / ‖ρ‖ ≤ 4 := by
    rw [div_le_iff₀ hpos]
    have := hreρ.trans (Complex.re_le_norm ρ); linarith
  -- the three rates
  have hC2 := partialSumRate_le (w := 2 - ρ) (a := 1) (b := 2) (M := 2 + (2 + |t|)) one_pos
    (by rw [sub_re]; norm_num; linarith) (by rw [sub_re]; norm_num; linarith)
    ((norm_sub_le _ _).trans (by rw [Complex.norm_two]; linarith))
  have hC3 := partialSumRate_le (w := ρ) (a := 1 / 4) (b := 1) (M := 2 + |t|) (by norm_num)
    hreρ hreρ1 hnorm
  have hC1 := partialSumRate_le (w := 1 - ρ) (a := ε / 2) (b := 1) (M := 1 + (2 + |t|))
    (by linarith) (by rw [sub_re, one_re]; linarith) (by rw [sub_re, one_re]; linarith)
    ((norm_sub_le _ _).trans (by rw [norm_one]; linarith))
  have hC30 := partialSumRate_nonneg (w := ρ) (by linarith)
  have hC3d : partialSumRate ρ / ‖ρ‖ ≤ ((2 + |t|) * (1 + 1 / (1 / 4)) + 1) * (2 : ℝ) ^ (1 : ℝ) * 4 := by
    rw [div_eq_mul_one_div]
    exact mul_le_mul hC3 hinv (by positivity) ((partialSumRate_nonneg (by linarith)).trans hC3)
  have hre4 : 1 + 1 / ρ.re ≤ 1 + 4 := by
    have : 1 / ρ.re ≤ 1 / (1 / 4) := one_div_le_one_div_of_le (by norm_num) hreρ
    norm_num at this ⊢; linarith
  unfold floorSumRate discRate
  linarith

/-- **The uniform remainder bound on the disc** `|ρ − ρ₀| ≤ ε/2`. -/
theorem norm_floorRemainder_le_of_mem_closedBall {ε t : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    {n : ℕ} (hn : 1 ≤ n) {ρ : ℂ} (hρ : ρ ∈ closedBall (oscillationExponent ε t) (ε / 2)) :
    ‖floorRemainder n ρ‖ ≤ discRate ε t * Real.sqrt n ^ (1 - ε / 2) := by
  have hρ' := hρ
  rw [mem_closedBall, dist_eq_norm] at hρ'
  have hre := (Complex.abs_re_le_norm (ρ - oscillationExponent ε t)).trans hρ'
  rw [sub_re, oscillationExponent_re, abs_le] at hre
  have h := norm_cpowFloorSum_sub_le (ρ := ρ) (by linarith) (by linarith) hn
  have hsq1 : 1 ≤ Real.sqrt n := Real.one_le_sqrt.mpr (by exact_mod_cast hn)
  have hpow : Real.sqrt n ^ ρ.re ≤ Real.sqrt n ^ (1 - ε / 2) :=
    Real.rpow_le_rpow_of_exponent_le hsq1 (by linarith)
  have hK := floorSumRate_le_discRate hε hε2 hρ
  have hK0 : 0 ≤ floorSumRate ρ := floorSumRate_nonneg (by linarith) (by linarith)
  calc ‖floorRemainder n ρ‖ ≤ floorSumRate ρ * Real.sqrt n ^ ρ.re := h
    _ ≤ discRate ε t * Real.sqrt n ^ (1 - ε / 2) :=
        mul_le_mul hK hpow (Real.rpow_nonneg (Real.sqrt_nonneg _) _) (hK0.trans hK)

/-- `R_n` is holomorphic on the disc `|ρ − ρ₀| < ε/2`, `ρ₀ = 1 − ε + it`, and continuous up to its
boundary. -/
theorem diffContOnCl_floorRemainder {ε t : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) (n : ℕ) :
    DiffContOnCl ℂ (floorRemainder n) (ball (oscillationExponent ε t) (ε / 2)) := by
  have hδ : 0 < ε / 2 := by linarith
  refine DifferentiableOn.diffContOnCl ?_
  rw [closure_ball _ hδ.ne']
  intro ρ hρ
  rw [mem_closedBall, dist_eq_norm] at hρ
  have hre := (Complex.abs_re_le_norm (ρ - oscillationExponent ε t)).trans hρ
  rw [sub_re, oscillationExponent_re, abs_le] at hre
  have h0 : ρ ≠ 0 := fun h => by rw [h, zero_re] at hre; linarith
  have h1 : ρ ≠ 1 := fun h => by rw [h, one_re] at hre; linarith
  exact (differentiableAt_floorRemainder n h0 h1).differentiableWithinAt

/-- **Cauchy's estimate for the remainder derivative**:
`‖∂_ρ R_n(ρ₀)‖ ≤ (2/ε) K (√n)^{1−ε/2}` at `ρ₀ = 1 − ε + it`. -/
theorem norm_deriv_floorRemainder_le {ε t : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) {n : ℕ}
    (hn : 1 ≤ n) :
    ‖deriv (floorRemainder n) (oscillationExponent ε t)‖ ≤
      discRate ε t * Real.sqrt n ^ (1 - ε / 2) / (ε / 2) :=
  Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by linarith)
    (diffContOnCl_floorRemainder hε hε2 n) fun z hz =>
      norm_floorRemainder_le_of_mem_closedBall hε hε2 hn (sphere_subset_closedBall hz)

/-- **Cauchy's estimate for the iterated remainder derivatives**:
`‖∂^k_ρ R_n(ρ₀)‖ ≤ k! K (√n)^{1−ε/2} / (ε/2)^k`. -/
theorem norm_iteratedDeriv_floorRemainder_le {ε t : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) {n : ℕ}
    (hn : 1 ≤ n) (k : ℕ) :
    ‖iteratedDeriv k (floorRemainder n) (oscillationExponent ε t)‖ ≤
      k.factorial * (discRate ε t * Real.sqrt n ^ (1 - ε / 2)) / (ε / 2) ^ k :=
  Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k (by linarith)
    (diffContOnCl_floorRemainder hε hε2 n) fun z hz =>
      norm_floorRemainder_le_of_mem_closedBall hε hε2 hn (sphere_subset_closedBall hz)

/-! ### The log-twisted weight and its prefix -/

/-- The log-twisted oscillating smooth power `d^{-ε} cos(t log d) log d`. -/
def logOscillatingSmoothPower (ε t : ℝ) (d : ℕ) : ℝ := oscillatingSmoothPower ε t d * Real.log d

/-- `d^{-ε} cos(t log d) log d = Re(d^{ρ−1} log d)`. -/
theorem logOscillatingSmoothPower_eq_re {ε : ℝ} (hε : 0 < ε) (t : ℝ) (d : ℕ) :
    logOscillatingSmoothPower ε t d =
      (((d : ℝ) : ℂ) ^ (oscillationExponent ε t - 1) * (Real.log d : ℂ)).re := by
  rw [logOscillatingSmoothPower, oscillatingSmoothPower_eq_re hε, Complex.re_mul_ofReal]

/-- The mean of the log-twisted weight is `−Re ζ'(2 − ρ)`. -/
theorem hasSum_logOscillatingSmoothPower_div {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    HasSum (fun d : ℕ => logOscillatingSmoothPower ε t d / d)
      (-deriv riemannZeta (2 - oscillationExponent ε t)).re := by
  set ρ := oscillationExponent ε t with hρ
  set s : ℂ := 2 - ρ with hs
  have hre : 1 < s.re := by rw [hs, sub_re, oscillationExponent_re]; norm_num; linarith
  have habs : LSeries.abscissaOfAbsConv 1 < s.re := by
    rw [LSeries.abscissaOfAbsConv_one]; exact_mod_cast hre
  -- `ζ' = −L(log)` on `Re s > 1`
  have hderiv : deriv riemannZeta s = -LSeries (LSeries.logMul 1) s := by
    rw [← LSeries_deriv habs]
    refine Filter.EventuallyEq.deriv_eq ?_
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hre] with z hz
    exact (LSeries_one_eq_riemannZeta hz).symm
  rw [hderiv, neg_neg]
  refine (Complex.hasSum_re (LSeriesSummable_logMul_of_lt_re habs).LSeriesHasSum).congr_fun
    fun d => ?_
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hdC : ((d : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hd0.ne'
  rw [LSeries.term_of_ne_zero hd.ne']
  simp only [LSeries.logMul, Pi.one_apply, mul_one]
  rw [← Complex.natCast_log, logOscillatingSmoothPower_eq_re hε, ← hρ]
  have h1 : (Real.log d : ℂ) / (d : ℂ) ^ s =
      ((d : ℝ) : ℂ) ^ (ρ - 1) * (Real.log d : ℂ) / ((d : ℝ) : ℂ) := by
    rw [show (d : ℂ) = ((d : ℝ) : ℂ) by push_cast; rfl, hs, div_eq_mul_inv, ← Complex.cpow_neg,
      show -(2 - ρ) = ρ - 1 - 1 by ring, Complex.cpow_sub _ _ hdC, Complex.cpow_one]
    ring
  rw [h1, Complex.div_ofReal_re]

/-- The prefix of the log-twisted weight is `Re(∂_ρ D_ρ(n) + ζ'(2 − ρ) n)`. -/
theorem weightCenteredPrefix_logOscillatingSmoothPower_eq {ε : ℝ} (hε : 0 < ε) (t : ℝ) (n : ℕ) :
    weightCenteredPrefix (logOscillatingSmoothPower ε t)
        (∑' d : ℕ, logOscillatingSmoothPower ε t d / d) n =
      (∑ d ∈ Icc 1 n, ((d : ℝ) : ℂ) ^ (oscillationExponent ε t - 1) * (Real.log d : ℂ) *
          ((n / d : ℕ) : ℂ) + deriv riemannZeta (2 - oscillationExponent ε t) * n).re := by
  rw [weightCenteredPrefix, sum_Icc_sum_divisors_eq_floor,
    (hasSum_logOscillatingSmoothPower_div hε t).tsum_eq, add_re, Complex.re_sum, sub_eq_add_neg]
  congr 1
  · refine sum_congr rfl fun d _ => ?_
    rw [logOscillatingSmoothPower_eq_re hε, show ((n / d : ℕ) : ℂ) = (((n / d : ℕ) : ℝ) : ℂ) by
      push_cast; rfl]
    simp only [Complex.re_mul_ofReal]
  · rw [show (n : ℂ) = ((n : ℝ) : ℂ) by push_cast; rfl, Complex.re_mul_ofReal, neg_re]
    ring

/-- **The prefix asymptotic of the log-twisted weight.** For `0 < ε ≤ 1/2` and `n ≥ 1`,
`|A(n) − Re(n^ρ(b + a log n))| ≤ (2K/ε)(√n)^{1−ε/2}` with `a = ζ(ρ)/ρ`, `b = ζ'(ρ)/ρ − ζ(ρ)/ρ²`. -/
theorem abs_weightCenteredPrefix_logOscillatingSmoothPower_sub_le {ε : ℝ} (hε : 0 < ε)
    (hε2 : ε ≤ 1 / 2) (t : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    |weightCenteredPrefix (logOscillatingSmoothPower ε t)
        (∑' d : ℕ, logOscillatingSmoothPower ε t d / d) n -
      (((n : ℝ) : ℂ) ^ oscillationExponent ε t *
        ((deriv riemannZeta (oscillationExponent ε t) / oscillationExponent ε t -
          riemannZeta (oscillationExponent ε t) / oscillationExponent ε t ^ 2) +
        riemannZeta (oscillationExponent ε t) / oscillationExponent ε t *
          (Real.log n : ℂ))).re| ≤
      discRate ε t * Real.sqrt n ^ (1 - ε / 2) / (ε / 2) := by
  set ρ := oscillationExponent ε t with hρ
  have hre : ρ.re = 1 - ε := oscillationExponent_re ε t
  have h0 : ρ ≠ 0 := fun h => by rw [h, zero_re] at hre; linarith
  have h1 : ρ ≠ 1 := fun h => by rw [h, one_re] at hre; linarith
  have hd := deriv_floorRemainder h0 h1 hn
  rw [weightCenteredPrefix_logOscillatingSmoothPower_eq hε, ← sub_re, ← hρ, ← hd]
  exact (Complex.abs_re_le_norm _).trans (norm_deriv_floorRemainder_le hε hε2 hn)

/-! ### Sufficiency: a double zero pays the receiver -/

/-- **A double zero pays the log-twisted weight.** For `0 < ε ≤ 1/2`, if `ζ(ρ) = ζ'(ρ) = 0` at
`ρ = 1 − ε + it` then the receiver of `d^{-ε} cos(t log d) log d` is bounded. -/
theorem receiverBounded_logOscillatingSmoothPower_of_deriv_eq_zero {ε : ℝ} (hε : 0 < ε)
    (hε2 : ε ≤ 1 / 2) (t : ℝ) (hz : riemannZeta (oscillationExponent ε t) = 0)
    (hz' : deriv riemannZeta (oscillationExponent ε t) = 0) :
    ReceiverBounded (logOscillatingSmoothPower ε t) := by
  refine ⟨(discRate ε t / (ε / 2)) ^ 2 * (1 + 1 / (ε / 2)), fun T => ?_⟩
  rw [weightPronicEnergy]
  refine sum_sq_le_of_abs_le_sqrt_rpow (ε := ε / 2) (by linarith) (fun n hn => ?_) T
  have h := abs_weightCenteredPrefix_logOscillatingSmoothPower_sub_le hε hε2 t hn
  simp only [hz, hz', zero_div, sub_zero, zero_mul, add_zero, mul_zero, zero_re] at h
  rwa [mul_div_right_comm] at h

/-! ### Necessity: harmonic windows -/

/-- **A paid receiver bounds the logarithmic energy of its main term.** If the prefix of a paid
weight is `n^{1−ε} u(n)` up to `K (√n)^{1−δ}`, with `ε ≤ 1/2` and `δ > 0`, then
`Σ_{n ≤ T} u(n)²/n` is bounded. -/
theorem exists_sum_sq_div_le_of_receiverBounded {c : ℕ → ℝ} (hB : ReceiverBounded c)
    {ε δ K : ℝ} (hε2 : ε ≤ 1 / 2) (hδ : 0 < δ) {u : ℕ → ℝ}
    (hrem : ∀ n, 1 ≤ n →
      |weightCenteredPrefix c (∑' d : ℕ, c d / d) n - (n : ℝ) ^ (1 - ε) * u n| ≤
        K * Real.sqrt n ^ (1 - δ)) :
    ∃ C : ℝ, ∀ T : ℕ, ∑ n ∈ Icc 1 T, u n ^ 2 / n ≤ C := by
  obtain ⟨E, hE⟩ := hB
  set A := weightCenteredPrefix c (∑' d : ℕ, c d / d) with hA
  set B := Real.sqrt E + |K| * Real.sqrt (1 + 1 / δ) with hBdef
  have hMnorm : ∀ T, pronicNorm (fun n => (n : ℝ) ^ (1 - ε) * u n) T ≤ B := by
    intro T
    have h1 : pronicNorm A T ≤ Real.sqrt E := by
      have h := hE T
      rw [weightPronicEnergy_eq_sq_pronicNorm] at h
      have h' := Real.sqrt_le_sqrt h
      rwa [Real.sqrt_sq (pronicNorm_nonneg _ _)] at h'
    have h2 : pronicNorm (fun n => A n - (n : ℝ) ^ (1 - ε) * u n) T ≤
        |K| * Real.sqrt (1 + 1 / δ) := by
      have h := sum_sq_le_of_abs_le_sqrt_rpow hδ
        (f := fun n => A n - (n : ℝ) ^ (1 - ε) * u n) hrem T
      rw [pronicNorm]
      calc Real.sqrt _ ≤ Real.sqrt (K ^ 2 * (1 + 1 / δ)) := Real.sqrt_le_sqrt h
        _ = |K| * Real.sqrt (1 + 1 / δ) := by
            rw [Real.sqrt_mul (sq_nonneg K), Real.sqrt_sq_eq_abs]
    have h3 := pronicNorm_add_le A (fun n => (-1) * (A n - (n : ℝ) ^ (1 - ε) * u n)) T
    rw [pronicNorm_smul, abs_neg, abs_one, one_mul] at h3
    have h4 : pronicNorm (fun n => (n : ℝ) ^ (1 - ε) * u n) T =
        pronicNorm (fun n => A n + (-1) * (A n - (n : ℝ) ^ (1 - ε) * u n)) T :=
      pronicNorm_congr fun n _ => by ring
    rw [h4, hBdef]
    linarith
  refine ⟨2 * B ^ 2, fun T => ?_⟩
  have hMsq : ∑ n ∈ Icc 1 T, ((n : ℝ) ^ (1 - ε) * u n) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) ≤
      B ^ 2 := by
    have h := hMnorm T
    rw [pronicNorm] at h
    have hs0 : 0 ≤ ∑ n ∈ Icc 1 T, ((n : ℝ) ^ (1 - ε) * u n) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) :=
      sum_nonneg fun n _ => by positivity
    calc _ = Real.sqrt (∑ n ∈ Icc 1 T,
            ((n : ℝ) ^ (1 - ε) * u n) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))) ^ 2 :=
          (Real.sq_sqrt hs0).symm
      _ ≤ B ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h 2
  have hterm : ∀ n ∈ Icc 1 T, u n ^ 2 / n ≤
      2 * (((n : ℝ) ^ (1 - ε) * u n) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))) := by
    intro n hn
    have hn1 := (mem_Icc.mp hn).1
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    have hpow : (n : ℝ) ≤ ((n : ℝ) ^ (1 - ε)) ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le]
      calc (n : ℝ) = (n : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ (n : ℝ) ^ ((1 - ε) * ((2 : ℕ) : ℝ)) :=
            Real.rpow_le_rpow_of_exponent_le hnR (by push_cast; linarith)
    rw [mul_pow, div_le_iff₀ hn0, mul_comm 2, mul_assoc]
    have hpr : (0 : ℝ) < (n : ℝ) * ((n : ℝ) + 1) := by positivity
    rw [div_mul_eq_mul_div, le_div_iff₀ hpr]
    have hu2 : 0 ≤ u n ^ 2 := sq_nonneg _
    calc u n ^ 2 * ((n : ℝ) * ((n : ℝ) + 1)) ≤ u n ^ 2 * (2 * (n : ℝ) * n) :=
          mul_le_mul_of_nonneg_left (by nlinarith) hu2
      _ = ((n : ℝ) * u n ^ 2) * (2 * n) := by ring
      _ ≤ (((n : ℝ) ^ (1 - ε)) ^ 2 * u n ^ 2) * (2 * n) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hpow hu2) (by positivity)
  calc _ ≤ ∑ n ∈ Icc 1 T, 2 * (((n : ℝ) ^ (1 - ε) * u n) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))) :=
        sum_le_sum hterm
    _ = 2 * ∑ n ∈ Icc 1 T, ((n : ℝ) ^ (1 - ε) * u n) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) := by
        rw [mul_sum]
    _ ≤ 2 * B ^ 2 := by linarith

/-- Window sums are differences of prefix sums. -/
theorem sum_Ioc_eq_sub {M : Type*} [AddCommGroup M] (f : ℕ → M) {N T : ℕ} (h : N ≤ T) :
    ∑ n ∈ Ioc N T, f n = ∑ n ∈ Icc 1 T, f n - ∑ n ∈ Icc 1 N, f n := by
  have e : ∀ m, Icc 1 m = Ioc 0 m := fun m => by ext d; simp only [mem_Icc, mem_Ioc]; omega
  rw [e, e, ← sum_Ioc_consecutive f (Nat.zero_le N) h, add_sub_cancel_left]

/-- `Σ_{N<n≤N²} 1/n ≥ log N − 1`. -/
theorem log_sub_one_le_sum_Ioc_one_div {N : ℕ} (hN : 1 ≤ N) :
    Real.log N - 1 ≤ ∑ n ∈ Ioc N (N ^ 2), 1 / (n : ℝ) := by
  rw [sum_Ioc_eq_sub _ (le_self_pow hN two_ne_zero)]
  have h1 := log_succ_le_sum_Icc_one_div (N ^ 2)
  have h2 := RHTower.Sieve.sum_Icc_one_div_le_one_add_log N
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have h3 : Real.log ((N : ℝ) ^ 2) ≤ Real.log (((N ^ 2 : ℕ) : ℝ) + 1) :=
    Real.log_le_log (by positivity) (by push_cast; linarith)
  rw [Real.log_pow] at h3
  push_cast at h1 h3
  linarith

/-- `Σ_{N<n≤N²} 1/n ≤ 1 + 2 log N`. -/
theorem sum_Ioc_one_div_le {N : ℕ} (hN : 1 ≤ N) :
    ∑ n ∈ Ioc N (N ^ 2), 1 / (n : ℝ) ≤ 1 + 2 * Real.log N := by
  rw [sum_Ioc_eq_sub _ (le_self_pow hN two_ne_zero)]
  have h1 := RHTower.Sieve.sum_Icc_one_div_le_one_add_log (N ^ 2)
  have h2 : 0 ≤ ∑ n ∈ Icc 1 N, 1 / (n : ℝ) := sum_nonneg fun n _ => by positivity
  rw [Nat.cast_pow, Real.log_pow] at h1
  push_cast at h1
  linarith

/-- `Re(z)² = (|z|² + Re(z²))/2`. -/
theorem re_sq_eq_half (z : ℂ) : z.re ^ 2 = (‖z‖ ^ 2 + (z ^ 2).re) / 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, sq z, Complex.mul_re]; ring

theorem abs_re_mul_cpow_le (c : ℂ) (t : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    |(c * ((n : ℝ) : ℂ) ^ ((t : ℂ) * I)).re| ≤ ‖c‖ := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hw : ‖((n : ℝ) : ℂ) ^ ((t : ℂ) * I)‖ = 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hn0]; simp
  calc _ ≤ ‖c * ((n : ℝ) : ℂ) ^ ((t : ℂ) * I)‖ := Complex.abs_re_le_norm _
    _ = ‖c‖ := by rw [norm_mul, hw, mul_one]

/-- The bound for the oscillating harmonic sums `Σ_{n ≤ T} n^{iτ}/n`. -/
def oscHarmonicBound (τ : ℝ) : ℝ :=
  1 / ‖(τ : ℂ) * I‖ + ‖riemannZeta (1 - (τ : ℂ) * I)‖ + partialSumRate (1 - (τ : ℂ) * I)

/-- **The oscillating harmonic sums are bounded**: `‖Σ_{n ≤ T} n^{iτ}/n‖ ≤ B_τ` for `τ ≠ 0`. -/
theorem norm_sum_Icc_cpow_div_le {τ : ℝ} (hτ : τ ≠ 0) (T : ℕ) :
    ‖∑ n ∈ Icc 1 T, ((n : ℝ) : ℂ) ^ ((τ : ℂ) * I) / ((n : ℝ) : ℂ)‖ ≤ oscHarmonicBound τ := by
  set w : ℂ := 1 - (τ : ℂ) * I with hw
  have hwre : 0 < w.re := by simp [hw]
  have hwne : w ≠ 1 := by
    intro h
    have := congrArg Complex.im h
    simp [hw] at this
    exact hτ this
  have hrate0 := partialSumRate_nonneg hwre
  rcases Nat.eq_zero_or_pos T with rfl | hT
  · rw [show Icc 1 0 = (∅ : Finset ℕ) by simp, sum_empty, norm_zero]
    unfold oscHarmonicBound
    exact add_nonneg (by positivity) hrate0
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
  have hcp : ∑ n ∈ Icc 1 T, ((n : ℝ) : ℂ) ^ ((τ : ℂ) * I) / ((n : ℝ) : ℂ) =
      cpowPartialSum w T := by
    rw [cpowPartialSum]
    refine sum_congr rfl fun n hn => ?_
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
    have hnC : ((n : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hn0.ne'
    rw [hw, show -(1 - (τ : ℂ) * I) = (τ : ℂ) * I - 1 by ring, Complex.cpow_sub _ _ hnC,
      Complex.cpow_one]
  have h := norm_cpowPartialSum_sub_le hwre hwne hT le_rfl (by linarith)
  rw [show (1 : ℂ) - w = (τ : ℂ) * I by rw [hw]; ring] at h
  have hT1 : ‖((T : ℝ) : ℂ) ^ ((τ : ℂ) * I)‖ = 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hT0]; simp
  have hTpow : (T : ℝ) ^ (-w.re) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hT) (by linarith)
  rw [hcp]
  calc ‖cpowPartialSum w T‖ ≤ ‖((T : ℝ) : ℂ) ^ ((τ : ℂ) * I) / ((τ : ℂ) * I)‖ +
        ‖riemannZeta w‖ +
        ‖cpowPartialSum w T - ((T : ℝ) : ℂ) ^ ((τ : ℂ) * I) / ((τ : ℂ) * I) - riemannZeta w‖ := by
        have e : cpowPartialSum w T = ((T : ℝ) : ℂ) ^ ((τ : ℂ) * I) / ((τ : ℂ) * I) +
            riemannZeta w + (cpowPartialSum w T - ((T : ℝ) : ℂ) ^ ((τ : ℂ) * I) / ((τ : ℂ) * I) -
              riemannZeta w) := by ring
        exact (congrArg norm e).le.trans
          ((norm_add_le _ _).trans (add_le_add_left (norm_add_le _ _) _))
    _ ≤ 1 / ‖(τ : ℂ) * I‖ + ‖riemannZeta w‖ + partialSumRate w * 1 := by
        rw [norm_div, hT1]
        gcongr
        exact h.trans (mul_le_mul_of_nonneg_left hTpow hrate0)
    _ = oscHarmonicBound τ := by rw [mul_one, oscHarmonicBound]

/-- **Window energy of an oscillation.** For `t ≠ 0` and `N ≤ T`,
`Σ_{N<n≤T} Re(c n^{it})²/n ≥ (|c|²/2) Σ_{N<n≤T} 1/n − |c|² B_{2t}`. -/
theorem sum_Ioc_re_sq_div_ge {t : ℝ} (ht : t ≠ 0) (c : ℂ) {N T : ℕ} (hNT : N ≤ T) :
    ‖c‖ ^ 2 / 2 * ∑ n ∈ Ioc N T, 1 / (n : ℝ) - ‖c‖ ^ 2 * oscHarmonicBound (2 * t) ≤
      ∑ n ∈ Ioc N T, (c * ((n : ℝ) : ℂ) ^ ((t : ℂ) * I)).re ^ 2 / n := by
  set S := ∑ n ∈ Ioc N T, ((n : ℝ) : ℂ) ^ (((2 * t : ℝ) : ℂ) * I) / ((n : ℝ) : ℂ) with hS
  have hterm : ∀ n ∈ Ioc N T, (c * ((n : ℝ) : ℂ) ^ ((t : ℂ) * I)).re ^ 2 / n =
      ‖c‖ ^ 2 / 2 * (1 / (n : ℝ)) +
        (c ^ 2 * (((n : ℝ) : ℂ) ^ (((2 * t : ℝ) : ℂ) * I) / ((n : ℝ) : ℂ))).re / 2 := by
    intro n hn
    have hn1 : 1 ≤ n := by have := (mem_Ioc.mp hn).1; omega
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have hnC : ((n : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hn0.ne'
    have hw : ‖((n : ℝ) : ℂ) ^ ((t : ℂ) * I)‖ = 1 := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hn0]; simp
    have hz2 : (c * ((n : ℝ) : ℂ) ^ ((t : ℂ) * I)) ^ 2 =
        c ^ 2 * ((n : ℝ) : ℂ) ^ (((2 * t : ℝ) : ℂ) * I) := by
      rw [mul_pow, sq (((n : ℝ) : ℂ) ^ ((t : ℂ) * I)), ← Complex.cpow_add _ _ hnC]
      push_cast; ring_nf
    rw [re_sq_eq_half, norm_mul, hw, mul_one, hz2, ← mul_div_assoc (c ^ 2),
      Complex.div_ofReal_re]
    ring
  have hsum : ∑ n ∈ Ioc N T, (c * ((n : ℝ) : ℂ) ^ ((t : ℂ) * I)).re ^ 2 / n =
      ‖c‖ ^ 2 / 2 * ∑ n ∈ Ioc N T, 1 / (n : ℝ) + (c ^ 2 * S).re / 2 := by
    rw [sum_congr rfl hterm, sum_add_distrib, ← mul_sum, ← sum_div, ← Complex.re_sum, ← mul_sum]
  have hS2 : ‖S‖ ≤ 2 * oscHarmonicBound (2 * t) := by
    rw [hS, sum_Ioc_eq_sub _ hNT]
    have h1 := norm_sum_Icc_cpow_div_le (mul_ne_zero two_ne_zero ht) T
    have h2 := norm_sum_Icc_cpow_div_le (mul_ne_zero two_ne_zero ht) N
    exact (norm_sub_le _ _).trans (by linarith)
  have hre : -(‖c‖ ^ 2 * (2 * oscHarmonicBound (2 * t))) ≤ (c ^ 2 * S).re := by
    refine (abs_le.mp ((Complex.abs_re_le_norm _).trans ?_)).1
    rw [norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_left hS2 (by positivity)
  rw [hsum]
  linarith

/-- **Logarithmic amplification beats the harmonic window.** If `|w| ≤ β` and the window energies
of `v` satisfy `Σ_{N<n≤N²} v(n)²/n ≥ κ(log N − 1) − κ'` with `κ > 0`, then
`Σ_{n ≤ T} (w(n) + v(n) log n)²/n` is unbounded: on the window `log n ≥ log N` amplifies the
energy to order `(log N)³`, against the `O(log N)` window mass of `w`. -/
theorem exists_lt_sum_sq_div_of_window {v w : ℕ → ℝ} {β κ κ' : ℝ} (hκ : 0 < κ)
    (hw : ∀ n, 1 ≤ n → |w n| ≤ β)
    (hv : ∀ N : ℕ, 1 ≤ N → κ * (Real.log N - 1) - κ' ≤ ∑ n ∈ Ioc N (N ^ 2), v n ^ 2 / n)
    (C : ℝ) : ∃ T : ℕ, C < ∑ n ∈ Icc 1 T, (w n + Real.log n * v n) ^ 2 / n := by
  have hβ : 0 ≤ β := (abs_nonneg _).trans (hw 1 le_rfl)
  set D := |C| + 3 * β ^ 2 + 1 with hD
  have hD0 : 0 < D := by positivity
  obtain ⟨N, hN⟩ := exists_nat_gt (Real.exp (1 + (|κ'| + 2 * D) / κ))
  have hN0 : (0 : ℝ) < N := lt_trans (Real.exp_pos _) hN
  have hN1 : 1 ≤ N := Nat.cast_pos.mp hN0
  set X := Real.log N with hXdef
  have hX : 1 + (|κ'| + 2 * D) / κ < X := by
    rw [hXdef, Real.lt_log_iff_exp_lt hN0]; exact hN
  have hX1 : 1 ≤ X := by
    have : 0 ≤ (|κ'| + 2 * D) / κ := by positivity
    linarith
  -- the window `N < n ≤ N²`
  have hwin : X ^ 2 / 2 * (κ * (X - 1) - κ') - β ^ 2 * (1 + 2 * X) ≤
      ∑ n ∈ Ioc N (N ^ 2), (w n + Real.log n * v n) ^ 2 / n := by
    have hterm : ∀ n ∈ Ioc N (N ^ 2), X ^ 2 / 2 * (v n ^ 2 / n) - β ^ 2 * (1 / (n : ℝ)) ≤
        (w n + Real.log n * v n) ^ 2 / n := by
      intro n hn
      have hNn := (mem_Ioc.mp hn).1
      have hn1 : 1 ≤ n := by omega
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
      have hL : X ≤ Real.log n := Real.log_le_log hN0 (by exact_mod_cast hNn.le)
      have hw2 : w n ^ 2 ≤ β ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hw n hn1) 2
      have hLv : X ^ 2 * v n ^ 2 ≤ (Real.log n * v n) ^ 2 := by
        rw [mul_pow]
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by linarith) hL 2) (sq_nonneg _)
      have hkey : X ^ 2 / 2 * v n ^ 2 - β ^ 2 ≤ (w n + Real.log n * v n) ^ 2 := by
        nlinarith [sq_nonneg (2 * w n + Real.log n * v n)]
      have e : X ^ 2 / 2 * (v n ^ 2 / n) - β ^ 2 * (1 / (n : ℝ)) =
          (X ^ 2 / 2 * v n ^ 2 - β ^ 2) / n := by ring
      rw [e]
      exact div_le_div_of_nonneg_right hkey hn0.le
    have h1 := hv N hN1
    have h2 := sum_Ioc_one_div_le hN1
    rw [← hXdef] at h1 h2
    have hX2 : 0 ≤ X ^ 2 / 2 := by positivity
    calc X ^ 2 / 2 * (κ * (X - 1) - κ') - β ^ 2 * (1 + 2 * X)
        ≤ X ^ 2 / 2 * ∑ n ∈ Ioc N (N ^ 2), v n ^ 2 / n -
            β ^ 2 * ∑ n ∈ Ioc N (N ^ 2), 1 / (n : ℝ) := by
          linarith [mul_le_mul_of_nonneg_left h1 hX2, mul_le_mul_of_nonneg_left h2 (sq_nonneg β)]
      _ = ∑ n ∈ Ioc N (N ^ 2), (X ^ 2 / 2 * (v n ^ 2 / n) - β ^ 2 * (1 / (n : ℝ))) := by
          rw [sum_sub_distrib, mul_sum, mul_sum]
      _ ≤ _ := sum_le_sum hterm
  have hsub : ∑ n ∈ Ioc N (N ^ 2), (w n + Real.log n * v n) ^ 2 / n ≤
      ∑ n ∈ Icc 1 (N ^ 2), (w n + Real.log n * v n) ^ 2 / n := by
    refine sum_le_sum_of_subset_of_nonneg (fun n hn => ?_) (fun n _ _ => by positivity)
    rw [mem_Ioc] at hn
    rw [mem_Icc]
    omega
  -- the cubic window energy beats `C`
  have hκX : 2 * D < κ * (X - 1) - κ' := by
    have h1 : (|κ'| + 2 * D) / κ < X - 1 := by linarith
    rw [div_lt_iff₀ hκ] at h1
    linarith [le_abs_self κ']
  have h1 := mul_le_mul_of_nonneg_left hκX.le (by positivity : (0 : ℝ) ≤ X ^ 2 / 2)
  have h2 := mul_le_mul_of_nonneg_right (show X ≤ X ^ 2 by nlinarith) hD0.le
  have h3 := mul_le_mul_of_nonneg_left (show 1 + 2 * X ≤ 3 * X by linarith) (sq_nonneg β)
  have h5 : |C| ≤ X * |C| := le_mul_of_one_le_left (abs_nonneg C) hX1
  have h6 : X * D = X * |C| + 3 * β ^ 2 * X + X := by rw [hD]; ring
  exact ⟨N ^ 2, by linarith [le_abs_self C]⟩

/-! ### Necessity: a paid log-twisted receiver forces a double zero -/

/-- **A paid log-twisted weight forces a double zero.** For `0 < ε ≤ 1/2`, if the receiver of
`d^{-ε} cos(t log d) log d` is bounded then `ζ(ρ) = ζ'(ρ) = 0`. The main term is
`n^{1−ε} Re(n^{it}(b + a log n))`: when `a ≠ 0` the factor `log n` amplifies its window energy
(`exists_lt_sum_sq_div_of_window`), and when `a = 0 ≠ b` the harmonic energy of `Re(b n^{it})`
diverges. -/
theorem zeta_eq_zero_and_deriv_eq_zero_of_receiverBounded {ε : ℝ} (hε : 0 < ε)
    (hε2 : ε ≤ 1 / 2) (t : ℝ) (hB : ReceiverBounded (logOscillatingSmoothPower ε t)) :
    riemannZeta (oscillationExponent ε t) = 0 ∧
      deriv riemannZeta (oscillationExponent ε t) = 0 := by
  set ρ := oscillationExponent ε t with hρ
  have hre : ρ.re = 1 - ε := oscillationExponent_re ε t
  have hρ0 : ρ ≠ 0 := fun h => by rw [h, zero_re] at hre; linarith
  obtain ⟨a, ha⟩ : ∃ a : ℂ, a = riemannZeta ρ / ρ := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ℂ, b = deriv riemannZeta ρ / ρ - riemannZeta ρ / ρ ^ 2 := ⟨_, rfl⟩
  have hrem : ∀ n, 1 ≤ n →
      |weightCenteredPrefix (logOscillatingSmoothPower ε t)
          (∑' d : ℕ, logOscillatingSmoothPower ε t d / d) n -
        (n : ℝ) ^ (1 - ε) * (((n : ℝ) : ℂ) ^ ((t : ℂ) * I) * (b + a * (Real.log n : ℂ))).re| ≤
        discRate ε t / (ε / 2) * Real.sqrt n ^ (1 - ε / 2) := by
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hsplit : ((n : ℝ) : ℂ) ^ ρ =
        (((n : ℝ) ^ (1 - ε) : ℝ) : ℂ) * ((n : ℝ) : ℂ) ^ ((t : ℂ) * I) := by
      rw [hρ, oscillationExponent, Complex.cpow_add _ _ (by exact_mod_cast hn0.ne'),
        Complex.ofReal_cpow hn0.le]
    have hM : (((n : ℝ) : ℂ) ^ ρ * (b + a * (Real.log n : ℂ))).re =
        (n : ℝ) ^ (1 - ε) * (((n : ℝ) : ℂ) ^ ((t : ℂ) * I) * (b + a * (Real.log n : ℂ))).re := by
      rw [hsplit, mul_assoc, Complex.re_ofReal_mul]
    have h := abs_weightCenteredPrefix_logOscillatingSmoothPower_sub_le hε hε2 t hn
    rw [← hρ, ← hb, ← ha, hM, mul_div_right_comm] at h
    exact h
  obtain ⟨C, hC⟩ :=
    exists_sum_sq_div_le_of_receiverBounded hB hε2 (by linarith : (0 : ℝ) < ε / 2) hrem
  -- `u(n) = Re(b n^{it}) + log n · Re(a n^{it})`
  have hu : ∀ n : ℕ, (((n : ℝ) : ℂ) ^ ((t : ℂ) * I) * (b + a * (Real.log n : ℂ))).re =
      (b * ((n : ℝ) : ℂ) ^ ((t : ℂ) * I)).re +
        Real.log n * (a * ((n : ℝ) : ℂ) ^ ((t : ℂ) * I)).re := by
    intro n
    rw [show ((n : ℝ) : ℂ) ^ ((t : ℂ) * I) * (b + a * (Real.log n : ℂ)) =
        b * ((n : ℝ) : ℂ) ^ ((t : ℂ) * I) +
          (Real.log n : ℂ) * (a * ((n : ℝ) : ℂ) ^ ((t : ℂ) * I)) by ring,
      add_re, Complex.re_ofReal_mul]
  have hC' : ∀ T : ℕ, ∑ n ∈ Icc 1 T, ((b * ((n : ℝ) : ℂ) ^ ((t : ℂ) * I)).re +
      Real.log n * (a * ((n : ℝ) : ℂ) ^ ((t : ℂ) * I)).re) ^ 2 / n ≤ C := by
    intro T
    have h := hC T
    simp only [hu] at h
    exact h
  have hwb : ∀ n : ℕ, 1 ≤ n → |(b * ((n : ℝ) : ℂ) ^ ((t : ℂ) * I)).re| ≤ ‖b‖ :=
    fun n hn => abs_re_mul_cpow_le b t hn
  rcases eq_or_ne t 0 with ht0 | ht0
  · -- `t = 0`: `a = ζ(1 − ε)/(1 − ε)` has negative real part
    exfalso
    have hρr : ρ = ((1 - ε : ℝ) : ℂ) := by rw [hρ, oscillationExponent, ht0]; simp
    have hare : a.re < 0 := by
      have hz := riemannZeta_re_le_of_lt_one (σ := 1 - ε) (by linarith) (by linarith)
      rw [ha, hρr, Complex.div_ofReal_re]
      have : -(1 - ε) / (1 - (1 - ε)) < 0 := by
        apply div_neg_of_neg_of_pos <;> linarith
      exact div_neg_of_neg_of_pos (by linarith) (by linarith)
    have hv0 : ∀ n : ℕ, (a * ((n : ℝ) : ℂ) ^ ((t : ℂ) * I)).re = a.re := fun n => by simp [ht0]
    have hv : ∀ N : ℕ, 1 ≤ N → a.re ^ 2 * (Real.log N - 1) - 0 ≤
        ∑ n ∈ Ioc N (N ^ 2), (a * ((n : ℝ) : ℂ) ^ ((t : ℂ) * I)).re ^ 2 / n := by
      intro N hN
      have e : ∑ n ∈ Ioc N (N ^ 2), (a * ((n : ℝ) : ℂ) ^ ((t : ℂ) * I)).re ^ 2 / (n : ℝ) =
          a.re ^ 2 * ∑ n ∈ Ioc N (N ^ 2), 1 / (n : ℝ) := by
        rw [mul_sum]; exact sum_congr rfl fun n _ => by rw [hv0]; ring
      rw [e, sub_zero]
      exact mul_le_mul_of_nonneg_left (log_sub_one_le_sum_Ioc_one_div hN) (sq_nonneg _)
    obtain ⟨T, hT⟩ := exists_lt_sum_sq_div_of_window ((by nlinarith : (0 : ℝ) < a.re ^ 2)) hwb hv C
    exact absurd (hC' T) (not_le.mpr hT)
  · -- `t ≠ 0`: first `a = 0`, then `b = 0`
    have ha0 : a = 0 := by
      by_contra ha0
      have hna : 0 < ‖a‖ ^ 2 := by positivity
      have hv : ∀ N : ℕ, 1 ≤ N →
          ‖a‖ ^ 2 / 2 * (Real.log N - 1) - ‖a‖ ^ 2 * oscHarmonicBound (2 * t) ≤
            ∑ n ∈ Ioc N (N ^ 2), (a * ((n : ℝ) : ℂ) ^ ((t : ℂ) * I)).re ^ 2 / n := by
        intro N hN
        have h1 := sum_Ioc_re_sq_div_ge ht0 a (le_self_pow hN two_ne_zero)
        have h2 := mul_le_mul_of_nonneg_left (log_sub_one_le_sum_Ioc_one_div hN)
          (by positivity : (0 : ℝ) ≤ ‖a‖ ^ 2 / 2)
        linarith
      obtain ⟨T, hT⟩ := exists_lt_sum_sq_div_of_window (by positivity) hwb hv C
      exact absurd (hC' T) (not_le.mpr hT)
    have hb0 : b = 0 := by
      by_contra hb0
      have hnb : 0 < ‖b‖ ^ 2 := by positivity
      obtain ⟨T, -, hT⟩ := not_bddAbove_sum_Icc_one_div
        ((C + ‖b‖ ^ 2 * oscHarmonicBound (2 * t)) / (‖b‖ ^ 2 / 2))
      have e : Icc 1 T = Ioc 0 T := by ext d; simp only [mem_Icc, mem_Ioc]; omega
      have h1 := sum_Ioc_re_sq_div_ge ht0 b (Nat.zero_le T)
      rw [← e] at h1
      have h2 := hC' T
      simp only [ha0, zero_mul, zero_re, mul_zero, add_zero] at h2
      rw [div_lt_iff₀ (by positivity)] at hT
      linarith
    have hz : riemannZeta ρ = 0 := by
      rw [ha] at ha0; exact (div_eq_zero_iff.mp ha0).resolve_right hρ0
    refine ⟨hz, ?_⟩
    rw [hb, hz, zero_div, sub_zero] at hb0
    exact (div_eq_zero_iff.mp hb0).resolve_right hρ0

/-! ### The multiplicity law -/

/-- **The log-twisted oscillating smooth power is paid exactly at the double zeros of ζ.** For
`0 < ε ≤ 1/2` and `t ∈ ℝ`, the receiver of `d^{-ε} cos(t log d) log d` is bounded if and only if
`ζ(1 − ε + it) = ζ'(1 − ε + it) = 0`. -/
theorem receiverBounded_logOscillatingSmoothPower_iff {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    (t : ℝ) :
    ReceiverBounded (logOscillatingSmoothPower ε t) ↔
      riemannZeta (((1 - ε : ℝ) : ℂ) + (t : ℂ) * I) = 0 ∧
        deriv riemannZeta (((1 - ε : ℝ) : ℂ) + (t : ℂ) * I) = 0 :=
  ⟨zeta_eq_zero_and_deriv_eq_zero_of_receiverBounded hε hε2 t,
    fun h => receiverBounded_logOscillatingSmoothPower_of_deriv_eq_zero hε hε2 t h.1 h.2⟩

/-- **At half damping the paid log-twisted frequencies are the multiple critical zeros**:
`d^{-1/2} cos(t log d) log d` is paid iff `1/2 + it` is a zero of `ζ` of order at least two. -/
theorem receiverBounded_logOscillatingSmoothPower_half_iff (t : ℝ) :
    ReceiverBounded (logOscillatingSmoothPower (1 / 2) t) ↔
      riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * I) = 0 ∧
        deriv riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * I) = 0 := by
  rw [receiverBounded_logOscillatingSmoothPower_iff (by norm_num) le_rfl t]
  norm_num

/-- **Simplicity of the zeros in receiver form**: every zero of `ζ` with `1/2 ≤ Re s < 1` is
simple iff no log-twisted oscillating smooth power `d^{-ε} cos(t log d) log d`, `0 < ε ≤ 1/2`,
has a bounded receiver. -/
theorem forall_simple_zero_iff_forall_not_receiverBounded :
    (∀ s : ℂ, 1 / 2 ≤ s.re → s.re < 1 → riemannZeta s = 0 → deriv riemannZeta s ≠ 0) ↔
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 → ∀ t : ℝ,
        ¬ ReceiverBounded (logOscillatingSmoothPower ε t) := by
  constructor
  · intro h ε hε hε2 t hB
    obtain ⟨hz, hz'⟩ := (receiverBounded_logOscillatingSmoothPower_iff hε hε2 t).1 hB
    have hre : (((1 - ε : ℝ) : ℂ) + (t : ℂ) * I).re = 1 - ε := oscillationExponent_re ε t
    exact h _ (by rw [hre]; linarith) (by rw [hre]; linarith) hz hz'
  · intro h s hs1 hs2 hz hz'
    have hε : 0 < 1 - s.re := by linarith
    have hε2 : 1 - s.re ≤ 1 / 2 := by linarith
    have hs : ((1 - (1 - s.re) : ℝ) : ℂ) + (s.im : ℂ) * I = s := by
      apply Complex.ext <;> simp
    apply h (1 - s.re) hε hε2 s.im
    rw [receiverBounded_logOscillatingSmoothPower_iff hε hε2, hs]
    exact ⟨hz, hz'⟩

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
