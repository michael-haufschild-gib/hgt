import GaloisForLFunctions.RHTower.RobinLcmCriterion

/-!
# Robin's inequality at `lcm(1, …, n)` is equivalent to the Riemann hypothesis

`RH ⟺ σ(L_n) < e^γ L_n log log L_n` for all large `n`, `L_n = lcm(1, …, n)`.

The converse runs through the Mertens remainder `G(T) = R(e^T) - (ψ(e^T) - e^T)/(e^T T)`.  In the
decomposition `D(n) = Δ(n) + G(log n) + [second-order ψ-term] - E(n)` of the Robin defect, the prime
tails `Δ` and the second-order term are nonnegative, so `D(n) < 0` forces `G(log n) < E(n)`, and
`E(n) = O(1/(√n log n))` unconditionally.  Interpolating between integers gives
`G(s) ≤ B e^{-s/2}/s` for all large real `s`.  The inversion
`v(T) = v(W) - G(W) r(W) + G(T) r(T) + ∫_T^W G q` of the lag primitive `v`, evaluated at points `W`
where `R(e^W) > 0` (Littlewood) and `v(W)`, `(ψ(e^W) - e^W)e^{-W}` are small (prime number theorem,
`Φ(L) = o(e^{L/2})`), gives `v(T) ≤ 3B e^{-T/2}`, hence an upper bound for the lag function `Φ` on
`[0, ∞)`, hence every zero of `ξ` has real part at most `½`.
-/

open MeasureTheory Set Filter Topology
open ArithmeticFunction (sigma)
open GaloisForLFunctions.RHTower

namespace RHTower

noncomputable section

/-! ## The lag primitive vanishes at infinity -/

/-- **`v(T) → 0` unconditionally**, from `Φ(L) = o(e^{L/2})`. -/
theorem tendsto_mertensLagPrimitive_zero : Tendsto mertensLagPrimitive atTop (𝓝 0) := by
  have h1 := tendsto_weilLagFunctionReal_mul_exp_neg_half
  have h2 : Tendsto (fun L : ℝ => (Real.log (2 * Real.pi) + 1) * Real.exp (-L)) atTop (𝓝 0) := by
    have := Real.tendsto_exp_neg_atTop_nhds_zero.const_mul (Real.log (2 * Real.pi) + 1)
    rwa [mul_zero] at this
  have hsum := h1.add h2
  rw [add_zero] at hsum
  have h2' : Tendsto (fun L : ℝ => -((Real.log (2 * Real.pi) + 1) * Real.exp (-L))) atTop
      (𝓝 0) := by
    have := h2.neg
    rwa [neg_zero] at this
  have hlow := h1.add h2'
  rw [add_zero] at hlow
  have hl2 : 0 < Real.log (2 * Real.pi) := Real.log_pos (by linarith [Real.pi_gt_three])
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hsum ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with L hL
    have hS0 := trivialZeroSeriesReal_nonneg (Real.one_le_exp hL.le)
    have hS1 := trivialZeroSeriesReal_le_one (Real.one_le_exp hL.le)
    have hid := exp_mul_mertensLagPrimitive_eq hL
    have hv : mertensLagPrimitive L = weilLagFunctionReal L * Real.exp (-L / 2)
        + (Real.log (2 * Real.pi) - trivialZeroSeriesReal (Real.exp L)) * Real.exp (-L) := by
      have hE : Real.exp L * Real.exp (-L) = 1 := by rw [← Real.exp_add]; simp
      have hH : Real.exp (L / 2) * Real.exp (-L) = Real.exp (-L / 2) := by
        rw [← Real.exp_add]; ring_nf
      calc mertensLagPrimitive L = Real.exp (-L) * (Real.exp L * mertensLagPrimitive L) := by
            rw [← mul_assoc, mul_comm (Real.exp (-L)), hE, one_mul]
        _ = _ := by rw [hid]; linear_combination weilLagFunctionReal L * hH
    rw [hv]
    have hE0 := Real.exp_pos (-L)
    nlinarith
  · filter_upwards [eventually_gt_atTop 0] with L hL
    have hS0 := trivialZeroSeriesReal_nonneg (Real.one_le_exp hL.le)
    have hid := exp_mul_mertensLagPrimitive_eq hL
    have hv : mertensLagPrimitive L = weilLagFunctionReal L * Real.exp (-L / 2)
        + (Real.log (2 * Real.pi) - trivialZeroSeriesReal (Real.exp L)) * Real.exp (-L) := by
      have hE : Real.exp L * Real.exp (-L) = 1 := by rw [← Real.exp_add]; simp
      have hH : Real.exp (L / 2) * Real.exp (-L) = Real.exp (-L / 2) := by
        rw [← Real.exp_add]; ring_nf
      calc mertensLagPrimitive L = Real.exp (-L) * (Real.exp L * mertensLagPrimitive L) := by
            rw [← mul_assoc, mul_comm (Real.exp (-L)), hE, one_mul]
        _ = _ := by rw [hid]; linear_combination weilLagFunctionReal L * hH
    rw [hv]
    have hE0 := Real.exp_pos (-L)
    nlinarith

/-- `(ψ(x) - x)/x → 0`. -/
theorem tendsto_chebyshevError_div_self :
    Tendsto (fun x : ℝ => (Chebyshev.psi x - x) / x) atTop (𝓝 0) := by
  have h := tendsto_psi_div_self.sub_const 1
  rw [sub_self] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  field_simp

/-- **The boundary bracket is frequently small.**  For every `ε > 0` there are arbitrarily large
`W` with `v(W) - G(W) r(W) < ε`. -/
theorem frequently_lag_bracket_lt {ε : ℝ} (hε : 0 < ε) :
    ∃ᶠ W : ℝ in atTop,
      mertensLagPrimitive W - mertensErrorRemainder W * (W ^ 2 / (1 + W)) < ε := by
  have hb : (1 / 4 : ℝ) < zeroReSup := by linarith [half_le_zeroReSup]
  have hv : ∀ᶠ x : ℝ in atTop, mertensLagPrimitive (Real.log x) < ε / 2 :=
    Real.tendsto_log_atTop.eventually (tendsto_mertensLagPrimitive_zero.eventually
      (gt_mem_nhds (half_pos hε)))
  have hE : ∀ᶠ x : ℝ in atTop, |(Chebyshev.psi x - x) / x| < ε / 2 := by
    have := (tendsto_iff_norm_sub_tendsto_zero.mp tendsto_chebyshevError_div_self).eventually
      (gt_mem_nhds (half_pos hε))
    simpa only [sub_zero, Real.norm_eq_abs] using this
  refine Real.tendsto_log_atTop.frequently ?_
  refine ((frequently_rpow_lt_mertensError hb).and_eventually
    ((hv.and hE).and (eventually_ge_atTop (Real.exp 1)))).mono fun x hxx => ?_
  obtain ⟨hR, ⟨hvx, hEx⟩, hx⟩ := hxx
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos 1) hx
  have hlx : 1 ≤ Real.log x := by rw [Real.le_log_iff_exp_le hx0]; exact hx
  have hR0 : 0 < mertensError x := lt_trans (Real.rpow_pos_of_pos hx0 _) hR
  set W := Real.log x with hW
  have hW0 : 0 < W := by linarith
  have hr0 : 0 ≤ W ^ 2 / (1 + W) := by positivity
  have hrW : W ^ 2 / (1 + W) ≤ W := by rw [div_le_iff₀ (by linarith)]; nlinarith
  rw [mertensErrorRemainder, hW, Real.exp_log hx0, ← hW]
  have hkey : (Chebyshev.psi x - x) / (x * W) * (W ^ 2 / (1 + W))
      ≤ |(Chebyshev.psi x - x) / x| := by
    have e : (Chebyshev.psi x - x) / (x * W) * (W ^ 2 / (1 + W))
        = (Chebyshev.psi x - x) / x * (W ^ 2 / (1 + W) / W) := by
      field_simp
    rw [e]
    have hq0 : 0 ≤ W ^ 2 / (1 + W) / W := by positivity
    have hq1 : W ^ 2 / (1 + W) / W ≤ 1 := by rw [div_le_one hW0]; exact hrW
    calc (Chebyshev.psi x - x) / x * (W ^ 2 / (1 + W) / W)
        ≤ |(Chebyshev.psi x - x) / x| * (W ^ 2 / (1 + W) / W) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) hq0
      _ ≤ |(Chebyshev.psi x - x) / x| := mul_le_of_le_one_right (abs_nonneg _) hq1
  have hRr : 0 ≤ mertensError x * (W ^ 2 / (1 + W)) := mul_nonneg hR0.le hr0
  have e2 : mertensLagPrimitive W - (mertensError x - (Chebyshev.psi x - x) / (x * W))
      * (W ^ 2 / (1 + W))
      = mertensLagPrimitive W - mertensError x * (W ^ 2 / (1 + W))
        + (Chebyshev.psi x - x) / (x * W) * (W ^ 2 / (1 + W)) := by ring
  rw [e2]
  linarith

/-! ## From a remainder bound to an upper bound for the lag -/

/-- **The upper inversion.**  If `G(s) ≤ B e^{-s/2}/s` for `s ≥ T₀ ≥ 1`, then
`v(T) ≤ 3B e^{-T/2}` for `T ≥ T₀`. -/
theorem mertensLagPrimitive_le_of_remainder_le {B T₀ : ℝ} (hB : 0 ≤ B) (hT₀ : 1 ≤ T₀)
    (hG : ∀ s, T₀ ≤ s → mertensErrorRemainder s ≤ B * Real.exp (-s / 2) / s) {T : ℝ}
    (hT : T₀ ≤ T) : mertensLagPrimitive T ≤ 3 * B * Real.exp (-T / 2) := by
  have hT1 : 1 ≤ T := le_trans hT₀ hT
  have hT0 : 0 < T := by linarith
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  obtain ⟨W, hW, hTW⟩ := ((frequently_lag_bracket_lt hε).and_eventually
    (eventually_ge_atTop T)).exists
  have hinv := mertensLagPrimitive_eq_inversion hT1 hTW
  -- the boundary term at `T`
  have hGT : mertensErrorRemainder T * (T ^ 2 / (1 + T)) ≤ B * Real.exp (-T / 2) := by
    have hr0 : 0 ≤ T ^ 2 / (1 + T) := by positivity
    calc mertensErrorRemainder T * (T ^ 2 / (1 + T))
        ≤ B * Real.exp (-T / 2) / T * (T ^ 2 / (1 + T)) :=
          mul_le_mul_of_nonneg_right (hG T hT) hr0
      _ = B * Real.exp (-T / 2) * (T / (1 + T)) := by field_simp
      _ ≤ B * Real.exp (-T / 2) * 1 := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [div_le_one (by linarith)]; linarith
      _ = B * Real.exp (-T / 2) := mul_one _
  -- the integral
  have hint : ∫ s in T..W, mertensErrorRemainder s * (s * (s + 2) / (1 + s) ^ 2)
      ≤ 2 * B * Real.exp (-T / 2) := by
    have hGc := continuousOn_mertensErrorRemainder W
    have hqc : ContinuousOn (fun s : ℝ => s * (s + 2) / (1 + s) ^ 2) (uIcc T W) :=
      (continuousOn_id.mul (continuousOn_id.add continuousOn_const)).div
        ((continuousOn_const.add continuousOn_id).pow 2) fun s hs => by
          rw [uIcc_of_le hTW] at hs
          have : 0 < s := by linarith [hs.1]
          positivity
    have hGqi : IntervalIntegrable (fun s => mertensErrorRemainder s
        * (s * (s + 2) / (1 + s) ^ 2)) volume T W := by
      refine ContinuousOn.intervalIntegrable ?_
      refine (hGc.mono ?_).mul hqc
      intro s hs
      rw [uIcc_of_le hTW] at hs
      exact ⟨le_trans hT1 hs.1, hs.2⟩
    have hmono : ∫ s in T..W, mertensErrorRemainder s * (s * (s + 2) / (1 + s) ^ 2)
        ≤ ∫ s in T..W, (B / T * Real.exp (-s / 2) + 0 * Real.exp ((2 * 0 - 2) * s)) := by
      refine intervalIntegral.integral_mono_on hTW hGqi
        (Continuous.intervalIntegrable (by fun_prop) _ _) fun s hs => ?_
      have hs0 : 0 < s := by linarith [hs.1]
      have hq0 : 0 ≤ s * (s + 2) / (1 + s) ^ 2 := by positivity
      have hq1 : s * (s + 2) / (1 + s) ^ 2 ≤ 1 := by
        rw [div_le_one (by positivity)]; nlinarith
      have hE0 : 0 ≤ B * Real.exp (-s / 2) / s := by positivity
      calc mertensErrorRemainder s * (s * (s + 2) / (1 + s) ^ 2)
          ≤ B * Real.exp (-s / 2) / s * (s * (s + 2) / (1 + s) ^ 2) :=
            mul_le_mul_of_nonneg_right (hG s (le_trans hT hs.1)) hq0
        _ ≤ B * Real.exp (-s / 2) / s := mul_le_of_le_one_right hE0 hq1
        _ ≤ B * Real.exp (-s / 2) / T :=
            div_le_div_of_nonneg_left (by positivity) hT0 hs.1
        _ = B / T * Real.exp (-s / 2) + 0 * Real.exp ((2 * 0 - 2) * s) := by ring
    have h2 := integral_exp_weight_le (c₁ := B / T) (c₂ := 0) (b := 0) T W (by positivity)
      le_rfl (by norm_num)
    have hBT : 2 * (B / T) * Real.exp (-T / 2) ≤ 2 * B * Real.exp (-T / 2) := by
      have : B / T ≤ B := div_le_self hB hT1
      have := Real.exp_pos (-T / 2)
      nlinarith
    simp only [zero_mul, zero_div, add_zero] at h2 hmono
    linarith
  linarith

/-- **An upper bound for the lag function.**  If `G(s) ≤ B e^{-s/2}/s` for `s ≥ T₀ ≥ 1`, then
`Φ(L) ≤ 3B + 1` for `L ≥ T₀`. -/
theorem weilLagFunctionReal_le_of_remainder_le {B T₀ : ℝ} (hB : 0 ≤ B) (hT₀ : 1 ≤ T₀)
    (hG : ∀ s, T₀ ≤ s → mertensErrorRemainder s ≤ B * Real.exp (-s / 2) / s) {L : ℝ}
    (hL : T₀ ≤ L) : weilLagFunctionReal L ≤ 3 * B + 1 := by
  have hL0 : 0 < L := by linarith
  have hv := mertensLagPrimitive_le_of_remainder_le hB hT₀ hG hL
  rw [weilLagFunctionReal_eq_lagPrimitive hL0]
  have hS1 := trivialZeroSeriesReal_le_one (Real.one_le_exp hL0.le)
  have hl2 : 0 < Real.log (2 * Real.pi) := Real.log_pos (by linarith [Real.pi_gt_three])
  have hhalf : Real.exp (L / 2) * Real.exp (-L / 2) = 1 := by
    rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
  have hEm : Real.exp (-L / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hEp := Real.exp_pos (L / 2)
  have hEm0 := Real.exp_pos (-L / 2)
  have h1 : Real.exp (L / 2) * mertensLagPrimitive L ≤ 3 * B := by
    calc Real.exp (L / 2) * mertensLagPrimitive L
        ≤ Real.exp (L / 2) * (3 * B * Real.exp (-L / 2)) := mul_le_mul_of_nonneg_left hv hEp.le
      _ = 3 * B * (Real.exp (L / 2) * Real.exp (-L / 2)) := by ring
      _ = 3 * B := by rw [hhalf, mul_one]
  have h2 : -(Real.log (2 * Real.pi) - trivialZeroSeriesReal (Real.exp L)) * Real.exp (-L / 2)
      ≤ 1 := by
    have : -(Real.log (2 * Real.pi) - trivialZeroSeriesReal (Real.exp L)) ≤ 1 := by linarith
    nlinarith
  linarith

/-- **The remainder criterion.**  If `G(s) ≤ B e^{-s/2}/s` for all large `s`, the Riemann
hypothesis holds. -/
theorem riemannHypothesis_of_remainder_le {B T₀ : ℝ} (hB : 0 ≤ B) (hT₀ : 1 ≤ T₀)
    (hG : ∀ s, T₀ ≤ s → mertensErrorRemainder s ≤ B * Real.exp (-s / 2) / s) :
    RiemannHypothesis := by
  by_contra hRH
  obtain ⟨q, hq⟩ := exists_xiZeroCopy_re_gt_half_of_not_rh hRH
  have hM : ∀ L, 0 ≤ L → weilLagFunctionReal L
      ≤ max (3 * B + 1) (Real.exp (T₀ / 2) * lagWeightTotal) * Real.exp (0 * L) := by
    intro L hL
    rw [zero_mul, Real.exp_zero, mul_one]
    by_cases hLT : T₀ ≤ L
    · exact (weilLagFunctionReal_le_of_remainder_le hB hT₀ hG hLT).trans (le_max_left _ _)
    · refine le_trans ?_ (le_max_right _ _)
      have h1 := abs_weilLagFunctionReal_le L
      rw [abs_of_nonneg hL] at h1
      have h2 : Real.exp (L / 2) ≤ Real.exp (T₀ / 2) := Real.exp_le_exp.mpr (by linarith)
      have h3 := lagWeightTotal_nonneg
      calc weilLagFunctionReal L ≤ |weilLagFunctionReal L| := le_abs_self _
        _ ≤ Real.exp (L / 2) * lagWeightTotal := h1
        _ ≤ Real.exp (T₀ / 2) * lagWeightTotal := mul_le_mul_of_nonneg_right h2 h3
  have := re_le_half_add_of_weilLagFunctionReal_le_exp le_rfl (by norm_num) hM q
  linarith


/-- **The one-sided remainder criterion.**  RH holds if and only if
`G(T) ≤ B e^{-T/2}/T` for all large `T`. -/
theorem riemannHypothesis_iff_mertensErrorRemainder_le :
    RiemannHypothesis ↔ ∃ B T₀ : ℝ, 0 ≤ B ∧ 1 ≤ T₀ ∧
      ∀ s, T₀ ≤ s → mertensErrorRemainder s ≤ B * Real.exp (-s / 2) / s := by
  constructor
  · intro hRH
    have ha := poleSharpConstant_pos
    refine ⟨poleSharpConstant + 3, 4, by linarith, by norm_num, fun s hs => ?_⟩
    have hs0 : 0 < s := by linarith
    have h := (le_abs_self _).trans (abs_mertensErrorRemainder_le_sharp_of_riemannHypothesis hRH hs)
    have h10 : 10 / s ≤ 3 := by rw [div_le_iff₀ hs0]; linarith
    have hE : 0 ≤ Real.exp (-s / 2) / s := by positivity
    calc mertensErrorRemainder s ≤ (poleSharpConstant + 10 / s) * (Real.exp (-s / 2) / s) := h
      _ ≤ (poleSharpConstant + 3) * (Real.exp (-s / 2) / s) :=
          mul_le_mul_of_nonneg_right (by linarith) hE
      _ = (poleSharpConstant + 3) * Real.exp (-s / 2) / s := by ring
  · rintro ⟨B, T₀, hB, hT₀, hG⟩
    exact riemannHypothesis_of_remainder_le hB hT₀ hG

/-! ## From Robin's inequality at `L_n` to the remainder bound -/

/-- At an integer where Robin's inequality holds, `G(log n) < E(n)`. -/
theorem mertensErrorRemainder_log_lt_of_robinLcmDefect_neg {n : ℕ} (hn : 4 ≤ n)
    (hψ : 1 < Chebyshev.psi n) (hD : robinLcmDefect n < 0) :
    mertensErrorRemainder (Real.log n) < robinExponentDeficit n := by
  have hn4 : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hΔ := (mertensProductError_sub_mem hn4).1
  have hbr := log_log_le_add_div (by linarith : (1 : ℝ) < n) hψ
  rw [robinLcmDefect_eq (by omega)] at hD
  linarith

/-- `G(log n) ≤ E(n) + D(n)` for `n ≥ 4` with `ψ(n) > 1`. -/
theorem mertensErrorRemainder_log_le_add_robinLcmDefect {n : ℕ} (hn : 4 ≤ n)
    (hψ : 1 < Chebyshev.psi n) :
    mertensErrorRemainder (Real.log n) ≤ robinExponentDeficit n + robinLcmDefect n := by
  have hn4 : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hΔ := (mertensProductError_sub_mem hn4).1
  have hbr := log_log_le_add_div (by linarith : (1 : ℝ) < n) hψ
  rw [robinLcmDefect_eq (by omega)]
  linarith

/-- `ψ(x) = ψ(⌊x⌋)`. -/
theorem psi_eq_psi_floor (x : ℝ) : Chebyshev.psi x = Chebyshev.psi (⌊x⌋₊ : ℝ) := by
  rw [Chebyshev.psi_eq_sum_Icc, Chebyshev.psi_eq_sum_Icc, Nat.floor_natCast]

/-- **Interpolation between integers.**  For `x ≥ 4` and `n = ⌊x⌋`:
`G(log x) ≤ G(log n) + 12/(x log n)`. -/
theorem mertensErrorRemainder_log_le_floor {x : ℝ} (hx : 4 ≤ x) :
    mertensErrorRemainder (Real.log x)
      ≤ mertensErrorRemainder (Real.log (⌊x⌋₊ : ℝ)) + 12 / (x * Real.log (⌊x⌋₊ : ℝ)) := by
  set n := ⌊x⌋₊ with hn
  have hx0 : 0 < x := by linarith
  have hn4 : (4 : ℝ) ≤ n := by
    rw [hn]; exact_mod_cast Nat.le_floor (by exact_mod_cast hx)
  have hn0 : (0 : ℝ) < n := by linarith
  have hnx : (n : ℝ) ≤ x := Nat.floor_le hx0.le
  have hxn : x < n + 1 := Nat.lt_floor_add_one x
  have ha : 1 ≤ Real.log n := by
    rw [Real.le_log_iff_exp_le hn0]
    have := Real.exp_one_lt_d9; linarith
  have hab : Real.log n ≤ Real.log x := Real.log_le_log hn0 hnx
  have hb : 1 ≤ Real.log x := le_trans ha hab
  have hψn : 0 ≤ Chebyshev.psi n := Chebyshev.psi_nonneg _
  have hψ6 : Chebyshev.psi n ≤ 6 * n := by
    have h := Chebyshev.psi_le_const_mul_self hn0.le
    have hl4 : Real.log 4 < 2 := by
      have := Real.log_two_lt_d9
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; linarith
    nlinarith
  have hpx : Chebyshev.psi x = Chebyshev.psi n := psi_eq_psi_floor x
  have hAx : mertensPowerSum x = mertensPowerSum n := by
    unfold mertensPowerSum; rw [Nat.floor_natCast]
  rw [mertensErrorRemainder, mertensErrorRemainder, Real.exp_log hx0, Real.exp_log hn0,
    mertensError, mertensError, hpx, hAx]
  -- the three pieces
  have hll : Real.log (Real.log n) ≤ Real.log (Real.log x) :=
    Real.log_le_log (by linarith) hab
  have hinv : 1 / Real.log x ≤ 1 / Real.log n := one_div_le_one_div_of_le (by linarith) hab
  have hba : Real.log x - Real.log n ≤ x / n - 1 := by
    rw [← Real.log_div hx0.ne' hn0.ne']; exact Real.log_le_sub_one_of_pos (by positivity)
  have hdiff : x * Real.log x - n * Real.log n ≤ 2 * Real.log x := by
    have h1 : (x - n) * Real.log x ≤ Real.log x := by
      have : x - n ≤ 1 := by linarith
      nlinarith
    have h2 : (n : ℝ) * (Real.log x - Real.log n) ≤ x - n := by
      have := mul_le_mul_of_nonneg_left hba hn0.le
      have e : (n : ℝ) * (x / n - 1) = x - n := by field_simp
      linarith
    nlinarith
  have hψpart : Chebyshev.psi n / (n * Real.log n) - Chebyshev.psi n / (x * Real.log x)
      ≤ 12 / (x * Real.log n) := by
    have hla : 0 < Real.log n := by linarith
    have hlb : 0 < Real.log x := by linarith
    have e : Chebyshev.psi n / (n * Real.log n) - Chebyshev.psi n / (x * Real.log x)
        = Chebyshev.psi n * (x * Real.log x - n * Real.log n)
          / (n * Real.log n * (x * Real.log x)) := by
      field_simp
    rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : Chebyshev.psi n * (x * Real.log x - n * Real.log n)
        ≤ 6 * n * (2 * Real.log x) := by
      rcases le_or_gt 0 (x * Real.log x - n * Real.log n) with h | h
      · exact mul_le_mul hψ6 hdiff h (by positivity)
      · nlinarith
    have hpos : 0 ≤ x * Real.log n := by positivity
    nlinarith
  have e : mertensPowerSum n - Real.log (Real.log x) - Real.eulerMascheroniConstant
        - (Chebyshev.psi n - x) / (x * Real.log x)
      - (mertensPowerSum n - Real.log (Real.log n) - Real.eulerMascheroniConstant
        - (Chebyshev.psi n - n) / (n * Real.log n))
      = -(Real.log (Real.log x) - Real.log (Real.log n)) + (1 / Real.log x - 1 / Real.log n)
        + (Chebyshev.psi n / (n * Real.log n) - Chebyshev.psi n / (x * Real.log x)) := by
    have hla : Real.log n ≠ 0 := by linarith
    have hlb : Real.log x ≠ 0 := by linarith
    field_simp
    ring
  linarith


/-- **A small Robin defect at `L_n` for all large `n` implies the Riemann hypothesis**:
`D(n) ≤ 1/(√n log n)` eventually suffices. -/
theorem riemannHypothesis_of_eventually_robinLcmDefect_le
    (h : ∀ᶠ n : ℕ in atTop, robinLcmDefect n ≤ 1 / (Real.sqrt n * Real.log n)) :
    RiemannHypothesis := by
  have hE : ∀ᶠ n : ℕ in atTop, robinExponentDeficit n * (Real.sqrt n * Real.log n) < 3 :=
    tendsto_robinExponentDeficit_scaled.eventually (gt_mem_nhds (by norm_num))
  obtain ⟨N, hN⟩ := eventually_atTop.mp ((h.and eventually_one_lt_psi_natCast).and hE)
  set N' := max N 4 with hN'
  have hint : ∀ n : ℕ, N' ≤ n →
      mertensErrorRemainder (Real.log n) ≤ 4 / (Real.sqrt n * Real.log n) := by
    intro n hn
    obtain ⟨⟨hD, hψ⟩, hEn⟩ := hN n (le_trans (le_max_left _ _) hn)
    have hn4 : 4 ≤ n := le_trans (le_max_right _ _) hn
    have h1 := mertensErrorRemainder_log_le_add_robinLcmDefect hn4 hψ
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hpos : 0 < Real.sqrt n * Real.log n :=
      mul_pos (Real.sqrt_pos.mpr hn0) (Real.log_pos (by exact_mod_cast (by omega : 1 < n)))
    have : robinExponentDeficit n ≤ 3 / (Real.sqrt n * Real.log n) := by
      rw [le_div_iff₀ hpos]; linarith
    have e : 4 / (Real.sqrt n * Real.log n)
        = 3 / (Real.sqrt n * Real.log n) + 1 / (Real.sqrt n * Real.log n) := by ring
    linarith
  have hN'4 : (4 : ℝ) ≤ N' := by exact_mod_cast le_max_right N 4
  refine riemannHypothesis_of_remainder_le (B := 40) (T₀ := Real.log (N' + 1)) (by norm_num)
    ?_ ?_
  · rw [Real.le_log_iff_exp_le (by positivity)]
    have := Real.exp_one_lt_d9; linarith
  · intro s hs
    have hx : (N' : ℝ) + 1 ≤ Real.exp s := by
      rw [← Real.exp_log (by positivity : (0 : ℝ) < N' + 1)]; exact Real.exp_le_exp.mpr hs
    set x := Real.exp s with hxdef
    have hx4 : 4 ≤ x := by linarith
    have hx0 : 0 < x := by linarith
    have hnN : N' ≤ ⌊x⌋₊ := Nat.le_floor (by linarith)
    set n := ⌊x⌋₊ with hn
    have hn4 : (4 : ℝ) ≤ n := le_trans hN'4 (by exact_mod_cast hnN)
    have hn0 : (0 : ℝ) < n := by linarith
    have hnx : (n : ℝ) ≤ x := Nat.floor_le hx0.le
    have hxn : x < n + 1 := Nat.lt_floor_add_one x
    have hlogx : Real.log x = s := Real.log_exp s
    have h1 := mertensErrorRemainder_log_le_floor hx4
    rw [← hn, hlogx] at h1
    have h2 := hint n hnN
    have hs1 : 1 ≤ s := by
      rw [← hlogx, Real.le_log_iff_exp_le hx0]; have := Real.exp_one_lt_d9; linarith
    have hs0 : 0 < s := by linarith
    have hla : 0 < Real.log n := Real.log_pos (by linarith)
    have hsx : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
    have hsn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn0
    have hsqx : Real.sqrt x ≤ 2 * Real.sqrt n := by
      by_contra hc
      push Not at hc
      have h4 : (2 * Real.sqrt n) ^ 2 < Real.sqrt x ^ 2 :=
        pow_lt_pow_left₀ hc (by positivity) two_ne_zero
      rw [mul_pow, Real.sq_sqrt hn0.le, Real.sq_sqrt hx0.le] at h4
      linarith
    have hlx2 : s ≤ 2 * Real.log n := by
      rw [← hlogx, ← Real.log_rpow hn0, Real.rpow_two]
      exact Real.log_le_log hx0 (by nlinarith)
    have hsxx : Real.sqrt x ≤ x := by
      rw [Real.sqrt_le_left (by linarith)]; nlinarith
    have hexp : Real.exp (-s / 2) = 1 / Real.sqrt x := by
      rw [hxdef, show -s / 2 = -(s / 2) by ring, Real.exp_neg, Real.exp_half, one_div]
    have hb1 : 4 / (Real.sqrt n * Real.log n) ≤ 16 / (Real.sqrt x * s) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have := mul_le_mul hsqx hlx2 hs0.le (by positivity)
      nlinarith
    have hb2 : 12 / (x * Real.log n) ≤ 24 / (Real.sqrt x * s) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have := mul_le_mul hsxx hlx2 hs0.le hx0.le
      nlinarith
    have hval : 40 * Real.exp (-s / 2) / s = 16 / (Real.sqrt x * s) + 24 / (Real.sqrt x * s) := by
      rw [hexp]; field_simp; norm_num
    rw [hval]
    linarith

/-- **Robin's inequality at `L_n` for all large `n` implies the Riemann hypothesis.** -/
theorem riemannHypothesis_of_eventually_robin_lcmUpto
    (h : ∀ᶠ n : ℕ in atTop, (sigma 1 (Nat.lcmUpto n) : ℝ)
      < Real.exp Real.eulerMascheroniConstant * Nat.lcmUpto n
        * Real.log (Real.log (Nat.lcmUpto n))) :
    RiemannHypothesis := by
  refine riemannHypothesis_of_eventually_robinLcmDefect_le ?_
  filter_upwards [h, eventually_one_lt_psi_natCast] with n hR hψ
  have hD := (robin_lcmUpto_iff hψ).mp hR
  have : 0 ≤ 1 / (Real.sqrt n * Real.log n) :=
    div_nonneg zero_le_one (mul_nonneg (Real.sqrt_nonneg _) (Real.log_natCast_nonneg n))
  linarith

/-- **Robin's criterion at `lcm(1, …, n)`.**  The Riemann hypothesis holds if and only if
`σ(L_n) < e^γ L_n log log L_n` for all large `n`, `L_n = lcm(1, …, n)`. -/
theorem riemannHypothesis_iff_eventually_robin_lcmUpto :
    RiemannHypothesis ↔ ∀ᶠ n : ℕ in atTop, (sigma 1 (Nat.lcmUpto n) : ℝ)
      < Real.exp Real.eulerMascheroniConstant * Nat.lcmUpto n
        * Real.log (Real.log (Nat.lcmUpto n)) :=
  ⟨eventually_robin_lcmUpto_of_riemannHypothesis, riemannHypothesis_of_eventually_robin_lcmUpto⟩

end

end RHTower
