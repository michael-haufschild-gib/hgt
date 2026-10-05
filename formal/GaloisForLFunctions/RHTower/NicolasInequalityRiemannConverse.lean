import GaloisForLFunctions.RHTower.RobinLcmRiemannCriterion

/-!
# Nicolas's criterion: the converse without restriction on `Θ`

If `N_k/φ(N_k) > e^γ log log N_k` for all large primorials `N_k`, the Riemann hypothesis holds.

Write `G(T) = R(e^T) - (ψ(e^T) - e^T)/(e^T T)` for the Mertens remainder and
`s(T) = G(T) e^{T/2} T` for its scaled form.

* A lower bound `G(T) ≥ -B e^{-T/2}/T` for all large `T` implies RH: the inversion of `G` into the
  lag primitive `v` has an unconditional tail (`v → 0`, and the boundary bracket is frequently
  `> -ε` at points where `R < 0`), and the lag receiver with exponent `0` closes.
* `s(T) ≥ -K` for arbitrarily large `T` once `K > a₁ + 1`: otherwise `G ≤ 0` eventually, which is
  RH by the upper criterion, and under RH `s(T) - Φ(T) → 0` with `|Φ| ≤ a₁`.
* If `s(T*) < -K` lies between two points where `s ≥ -K`, the minimum `T_m` of `s` on that range is
  interior.  Comparing `G(T_m ± h)` with `s(T_m ± h) ≥ s(T_m)`, using that `ψ` is monotone and grows
  by at most `log y` across an interval of length one, gives
  `|ψ(x_m) - x_m| ≤ 2 T_m |G(T_m)| x_m + log(x_m + 1)`, `x_m = e^{T_m}`.  Hence the second-order
  term of the Nicolas defect is at most `140 T G² + o(1/(√x log x))`, and since `T |G(T)| → 0`
  unconditionally, the upper bound for the Nicolas defect makes it negative at `x_m`.

So the Nicolas inequality for all large primorials forces `s ≥ -K` eventually, hence RH.
-/

open MeasureTheory Set Filter Topology
open GaloisForLFunctions.RHTower

namespace RHTower

noncomputable section

/-! ## The lower one-sided remainder criterion -/

/-- For every `ε > 0` there are arbitrarily large `W` with `v(W) - G(W) r(W) > -ε`. -/
theorem frequently_lag_bracket_gt {ε : ℝ} (hε : 0 < ε) :
    ∃ᶠ W : ℝ in atTop,
      -ε < mertensLagPrimitive W - mertensErrorRemainder W * (W ^ 2 / (1 + W)) := by
  have hb : (1 / 4 : ℝ) < zeroReSup := by linarith [half_le_zeroReSup]
  have hv : ∀ᶠ x : ℝ in atTop, -(ε / 2) < mertensLagPrimitive (Real.log x) :=
    Real.tendsto_log_atTop.eventually (tendsto_mertensLagPrimitive_zero.eventually
      (lt_mem_nhds (by linarith)))
  have hE : ∀ᶠ x : ℝ in atTop, |(Chebyshev.psi x - x) / x| < ε / 2 := by
    have := (tendsto_iff_norm_sub_tendsto_zero.mp tendsto_chebyshevError_div_self).eventually
      (gt_mem_nhds (half_pos hε))
    simpa only [sub_zero, Real.norm_eq_abs] using this
  refine Real.tendsto_log_atTop.frequently ?_
  refine ((frequently_mertensError_lt_neg_rpow hb).and_eventually
    ((hv.and hE).and (eventually_ge_atTop (Real.exp 1)))).mono fun x hxx => ?_
  obtain ⟨hR, ⟨hvx, hEx⟩, hx⟩ := hxx
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos 1) hx
  have hlx : 1 ≤ Real.log x := by rw [Real.le_log_iff_exp_le hx0]; exact hx
  have hR0 : mertensError x < 0 := lt_trans hR (neg_lt_zero.mpr (Real.rpow_pos_of_pos hx0 _))
  set W := Real.log x with hW
  have hW0 : 0 < W := by linarith
  have hr0 : 0 ≤ W ^ 2 / (1 + W) := by positivity
  have hrW : W ^ 2 / (1 + W) ≤ W := by rw [div_le_iff₀ (by linarith)]; nlinarith
  rw [mertensErrorRemainder, hW, Real.exp_log hx0, ← hW]
  have hkey : -|(Chebyshev.psi x - x) / x|
      ≤ (Chebyshev.psi x - x) / (x * W) * (W ^ 2 / (1 + W)) := by
    have e : (Chebyshev.psi x - x) / (x * W) * (W ^ 2 / (1 + W))
        = (Chebyshev.psi x - x) / x * (W ^ 2 / (1 + W) / W) := by
      field_simp
    rw [e]
    have hq0 : 0 ≤ W ^ 2 / (1 + W) / W := by positivity
    have hq1 : W ^ 2 / (1 + W) / W ≤ 1 := by rw [div_le_one hW0]; exact hrW
    have h1 : -|(Chebyshev.psi x - x) / x| * (W ^ 2 / (1 + W) / W)
        ≤ (Chebyshev.psi x - x) / x * (W ^ 2 / (1 + W) / W) :=
      mul_le_mul_of_nonneg_right (neg_abs_le _) hq0
    have h2 : -|(Chebyshev.psi x - x) / x|
        ≤ -|(Chebyshev.psi x - x) / x| * (W ^ 2 / (1 + W) / W) := by
      have := abs_nonneg ((Chebyshev.psi x - x) / x)
      nlinarith
    linarith
  have hRr : mertensError x * (W ^ 2 / (1 + W)) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hR0.le hr0
  have e2 : mertensLagPrimitive W - (mertensError x - (Chebyshev.psi x - x) / (x * W))
      * (W ^ 2 / (1 + W))
      = mertensLagPrimitive W - mertensError x * (W ^ 2 / (1 + W))
        + (Chebyshev.psi x - x) / (x * W) * (W ^ 2 / (1 + W)) := by ring
  rw [e2]
  linarith

/-- **The lower inversion.**  If `G(s) ≥ -B e^{-s/2}/s` for `s ≥ T₀ ≥ 1`, then
`v(T) ≥ -3B e^{-T/2}` for `T ≥ T₀`. -/
theorem mertensLagPrimitive_ge_of_remainder_ge_exp {B T₀ : ℝ} (hB : 0 ≤ B) (hT₀ : 1 ≤ T₀)
    (hG : ∀ s, T₀ ≤ s → -(B * Real.exp (-s / 2) / s) ≤ mertensErrorRemainder s) {T : ℝ}
    (hT : T₀ ≤ T) : -(3 * B * Real.exp (-T / 2)) ≤ mertensLagPrimitive T := by
  have hT1 : 1 ≤ T := le_trans hT₀ hT
  have hT0 : 0 < T := by linarith
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  obtain ⟨W, hW, hTW⟩ := ((frequently_lag_bracket_gt hε).and_eventually
    (eventually_ge_atTop T)).exists
  have hinv := mertensLagPrimitive_eq_inversion hT1 hTW
  have hGT : -(B * Real.exp (-T / 2)) ≤ mertensErrorRemainder T * (T ^ 2 / (1 + T)) := by
    have hr0 : 0 ≤ T ^ 2 / (1 + T) := by positivity
    have hrT : T ^ 2 / (1 + T) / T ≤ 1 := by
      rw [div_le_one hT0, div_le_iff₀ (by linarith)]; nlinarith
    calc -(B * Real.exp (-T / 2)) ≤ -(B * Real.exp (-T / 2)) * (T ^ 2 / (1 + T) / T) := by
          have : 0 ≤ B * Real.exp (-T / 2) := by positivity
          have : 0 ≤ T ^ 2 / (1 + T) / T := by positivity
          nlinarith
      _ = -(B * Real.exp (-T / 2) / T) * (T ^ 2 / (1 + T)) := by field_simp
      _ ≤ mertensErrorRemainder T * (T ^ 2 / (1 + T)) :=
          mul_le_mul_of_nonneg_right (hG T hT) hr0
  have hint : -(2 * B * Real.exp (-T / 2))
      ≤ ∫ s in T..W, mertensErrorRemainder s * (s * (s + 2) / (1 + s) ^ 2) := by
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
    have hmono : ∫ s in T..W, -(B / T * Real.exp (-s / 2) + 0 * Real.exp ((2 * 0 - 2) * s))
        ≤ ∫ s in T..W, mertensErrorRemainder s * (s * (s + 2) / (1 + s) ^ 2) := by
      refine intervalIntegral.integral_mono_on hTW
        (Continuous.intervalIntegrable (by fun_prop) _ _) hGqi fun s hs => ?_
      have hs0 : 0 < s := by linarith [hs.1]
      have hq0 : 0 ≤ s * (s + 2) / (1 + s) ^ 2 := by positivity
      have hq1 : s * (s + 2) / (1 + s) ^ 2 ≤ 1 := by
        rw [div_le_one (by positivity)]; nlinarith
      have hE0 : 0 ≤ B * Real.exp (-s / 2) / s := by positivity
      have hsT : B * Real.exp (-s / 2) / s ≤ B * Real.exp (-s / 2) / T :=
        div_le_div_of_nonneg_left (by positivity) hT0 hs.1
      calc -(B / T * Real.exp (-s / 2) + 0 * Real.exp ((2 * 0 - 2) * s))
          = -(B * Real.exp (-s / 2) / T) := by ring
        _ ≤ -(B * Real.exp (-s / 2) / s) := by linarith
        _ ≤ -(B * Real.exp (-s / 2) / s) * (s * (s + 2) / (1 + s) ^ 2) := by nlinarith
        _ ≤ mertensErrorRemainder s * (s * (s + 2) / (1 + s) ^ 2) :=
            mul_le_mul_of_nonneg_right (hG s (le_trans hT hs.1)) hq0
    have h2 := integral_exp_weight_le (c₁ := B / T) (c₂ := 0) (b := 0) T W (by positivity)
      le_rfl (by norm_num)
    rw [intervalIntegral.integral_neg] at hmono
    have hBT : 2 * (B / T) * Real.exp (-T / 2) ≤ 2 * B * Real.exp (-T / 2) := by
      have : B / T ≤ B := div_le_self hB hT1
      have := Real.exp_pos (-T / 2)
      nlinarith
    simp only [zero_mul, zero_div, add_zero] at h2 hmono
    linarith
  linarith

/-- **A lower bound for the lag function.**  If `G(s) ≥ -B e^{-s/2}/s` for `s ≥ T₀ ≥ 1`, then
`Φ(L) ≥ -(3B + 6)` for `L ≥ T₀`. -/
theorem weilLagFunctionReal_ge_of_remainder_ge {B T₀ : ℝ} (hB : 0 ≤ B) (hT₀ : 1 ≤ T₀)
    (hG : ∀ s, T₀ ≤ s → -(B * Real.exp (-s / 2) / s) ≤ mertensErrorRemainder s) {L : ℝ}
    (hL : T₀ ≤ L) : -(3 * B + 6) ≤ weilLagFunctionReal L := by
  have hL0 : 0 < L := by linarith
  have hv := mertensLagPrimitive_ge_of_remainder_ge_exp hB hT₀ hG hL
  rw [weilLagFunctionReal_eq_lagPrimitive hL0]
  have hS0 := trivialZeroSeriesReal_nonneg (Real.one_le_exp hL0.le)
  have hl2 : Real.log (2 * Real.pi) ≤ 6 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 * Real.pi by positivity)
    linarith [Real.pi_lt_d2]
  have hhalf : Real.exp (L / 2) * Real.exp (-L / 2) = 1 := by
    rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
  have hEm : Real.exp (-L / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hEp := Real.exp_pos (L / 2)
  have hEm0 := Real.exp_pos (-L / 2)
  have h1 : -(3 * B) ≤ Real.exp (L / 2) * mertensLagPrimitive L := by
    calc -(3 * B) = Real.exp (L / 2) * (-(3 * B * Real.exp (-L / 2))) := by
          rw [show Real.exp (L / 2) * (-(3 * B * Real.exp (-L / 2)))
            = -(3 * B * (Real.exp (L / 2) * Real.exp (-L / 2))) by ring, hhalf, mul_one]
      _ ≤ Real.exp (L / 2) * mertensLagPrimitive L := mul_le_mul_of_nonneg_left hv hEp.le
  have h2 : (Real.log (2 * Real.pi) - trivialZeroSeriesReal (Real.exp L)) * Real.exp (-L / 2)
      ≤ 6 := by
    have : Real.log (2 * Real.pi) - trivialZeroSeriesReal (Real.exp L) ≤ 6 := by linarith
    have hpos : 0 ≤ Real.log (2 * Real.pi) - trivialZeroSeriesReal (Real.exp L)
        ∨ Real.log (2 * Real.pi) - trivialZeroSeriesReal (Real.exp L) < 0 := le_or_gt _ _
    rcases hpos with h | h
    · nlinarith
    · nlinarith
  linarith

/-- **The lower remainder criterion.**  If `G(s) ≥ -B e^{-s/2}/s` for all large `s`, the Riemann
hypothesis holds. -/
theorem riemannHypothesis_of_remainder_ge {B T₀ : ℝ} (hB : 0 ≤ B) (hT₀ : 1 ≤ T₀)
    (hG : ∀ s, T₀ ≤ s → -(B * Real.exp (-s / 2) / s) ≤ mertensErrorRemainder s) :
    RiemannHypothesis := by
  by_contra hRH
  obtain ⟨q, hq⟩ := exists_xiZeroCopy_re_gt_half_of_not_rh hRH
  have hM : ∀ L, 0 ≤ L → -(max (3 * B + 6) (Real.exp (T₀ / 2) * lagWeightTotal)
      * Real.exp (0 * L)) ≤ weilLagFunctionReal L := by
    intro L hL
    rw [zero_mul, Real.exp_zero, mul_one]
    by_cases hLT : T₀ ≤ L
    · exact le_trans (neg_le_neg (le_max_left _ _))
        (weilLagFunctionReal_ge_of_remainder_ge hB hT₀ hG hLT)
    · refine le_trans (neg_le_neg (le_max_right _ _)) ?_
      have h1 := abs_weilLagFunctionReal_le L
      rw [abs_of_nonneg hL] at h1
      have h2 : Real.exp (L / 2) ≤ Real.exp (T₀ / 2) := Real.exp_le_exp.mpr (by linarith)
      have h3 := lagWeightTotal_nonneg
      have h4 : Real.exp (L / 2) * lagWeightTotal ≤ Real.exp (T₀ / 2) * lagWeightTotal :=
        mul_le_mul_of_nonneg_right h2 h3
      linarith [neg_abs_le (weilLagFunctionReal L)]
  have := re_le_half_add_of_neg_exp_le_weilLagFunctionReal le_rfl (by norm_num) hM q
  linarith

/-- **The lower one-sided remainder criterion.**  RH holds if and only if
`G(T) ≥ -B e^{-T/2}/T` for all large `T`. -/
theorem riemannHypothesis_iff_mertensErrorRemainder_ge :
    RiemannHypothesis ↔ ∃ B T₀ : ℝ, 0 ≤ B ∧ 1 ≤ T₀ ∧
      ∀ s, T₀ ≤ s → -(B * Real.exp (-s / 2) / s) ≤ mertensErrorRemainder s := by
  constructor
  · intro hRH
    have ha := poleSharpConstant_pos
    refine ⟨poleSharpConstant + 3, 4, by linarith, by norm_num, fun s hs => ?_⟩
    have hs0 : 0 < s := by linarith
    have h := neg_abs_le (mertensErrorRemainder s) |>.trans' (neg_le_neg
      (abs_mertensErrorRemainder_le_sharp_of_riemannHypothesis hRH hs))
    have h10 : 10 / s ≤ 3 := by rw [div_le_iff₀ hs0]; linarith
    have hE : 0 ≤ Real.exp (-s / 2) / s := by positivity
    calc -((poleSharpConstant + 3) * Real.exp (-s / 2) / s)
        = -((poleSharpConstant + 3) * (Real.exp (-s / 2) / s)) := by ring
      _ ≤ -((poleSharpConstant + 10 / s) * (Real.exp (-s / 2) / s)) :=
          neg_le_neg (mul_le_mul_of_nonneg_right (by linarith) hE)
      _ ≤ mertensErrorRemainder s := h
  · rintro ⟨B, T₀, hB, hT₀, hG⟩
    exact riemannHypothesis_of_remainder_ge hB hT₀ hG


/-! ## The remainder is `o(1/T)` -/

/-- `G(U) ≤ δ` for arbitrarily large `U`. -/
theorem frequently_mertensErrorRemainder_le {δ : ℝ} (hδ : 0 < δ) :
    ∃ᶠ U : ℝ in atTop, mertensErrorRemainder U ≤ δ := by
  have hb : (1 / 4 : ℝ) < zeroReSup := by linarith [half_le_zeroReSup]
  have hE : ∀ᶠ x : ℝ in atTop, |(Chebyshev.psi x - x) / x| < δ := by
    have := (tendsto_iff_norm_sub_tendsto_zero.mp tendsto_chebyshevError_div_self).eventually
      (gt_mem_nhds hδ)
    simpa only [sub_zero, Real.norm_eq_abs] using this
  refine Real.tendsto_log_atTop.frequently ?_
  refine ((frequently_mertensError_lt_neg_rpow hb).and_eventually
    (hE.and (eventually_ge_atTop (Real.exp 1)))).mono fun x ⟨hR, hEx, hx⟩ => ?_
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos 1) hx
  have hlx : 1 ≤ Real.log x := by rw [Real.le_log_iff_exp_le hx0]; exact hx
  have hR0 : mertensError x < 0 := lt_trans hR (neg_lt_zero.mpr (Real.rpow_pos_of_pos hx0 _))
  rw [mertensErrorRemainder, Real.exp_log hx0]
  have h1 : -((Chebyshev.psi x - x) / (x * Real.log x)) ≤ |(Chebyshev.psi x - x) / x| := by
    rw [show (Chebyshev.psi x - x) / (x * Real.log x)
      = (Chebyshev.psi x - x) / x / Real.log x by field_simp]
    have h2 : |(Chebyshev.psi x - x) / x / Real.log x| ≤ |(Chebyshev.psi x - x) / x| := by
      rw [abs_div, abs_of_pos (by linarith : 0 < Real.log x)]
      exact div_le_self (abs_nonneg _) hlx
    linarith [neg_abs_le ((Chebyshev.psi x - x) / x / Real.log x)]
  linarith

/-- `G(U) ≥ -δ` for arbitrarily large `U`. -/
theorem frequently_mertensErrorRemainder_ge {δ : ℝ} (hδ : 0 < δ) :
    ∃ᶠ U : ℝ in atTop, -δ ≤ mertensErrorRemainder U := by
  have hb : (1 / 4 : ℝ) < zeroReSup := by linarith [half_le_zeroReSup]
  have hE : ∀ᶠ x : ℝ in atTop, |(Chebyshev.psi x - x) / x| < δ := by
    have := (tendsto_iff_norm_sub_tendsto_zero.mp tendsto_chebyshevError_div_self).eventually
      (gt_mem_nhds hδ)
    simpa only [sub_zero, Real.norm_eq_abs] using this
  refine Real.tendsto_log_atTop.frequently ?_
  refine ((frequently_rpow_lt_mertensError hb).and_eventually
    (hE.and (eventually_ge_atTop (Real.exp 1)))).mono fun x ⟨hR, hEx, hx⟩ => ?_
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos 1) hx
  have hlx : 1 ≤ Real.log x := by rw [Real.le_log_iff_exp_le hx0]; exact hx
  have hR0 : 0 < mertensError x := lt_trans (Real.rpow_pos_of_pos hx0 _) hR
  rw [mertensErrorRemainder, Real.exp_log hx0]
  have h1 : (Chebyshev.psi x - x) / (x * Real.log x) ≤ |(Chebyshev.psi x - x) / x| := by
    rw [show (Chebyshev.psi x - x) / (x * Real.log x)
      = (Chebyshev.psi x - x) / x / Real.log x by field_simp]
    have h2 : |(Chebyshev.psi x - x) / x / Real.log x| ≤ |(Chebyshev.psi x - x) / x| := by
      rw [abs_div, abs_of_pos (by linarith : 0 < Real.log x)]
      exact div_le_self (abs_nonneg _) hlx
    linarith [le_abs_self ((Chebyshev.psi x - x) / x / Real.log x)]
  linarith

/-- If `|v| ≤ η` on `[T, ∞)`, `T ≥ 1`, then `|G(T) - G(U)| ≤ 7η/T` for `U ≥ T`. -/
theorem abs_mertensErrorRemainder_sub_le_of_lag {η T U : ℝ} (hη : 0 ≤ η) (hT : 1 ≤ T)
    (hTU : T ≤ U) (hv : ∀ s, T ≤ s → |mertensLagPrimitive s| ≤ η) :
    |mertensErrorRemainder T - mertensErrorRemainder U| ≤ 7 * η / T := by
  have hT0 : 0 < T := by linarith
  have hU0 : 0 < U := by linarith
  rw [mertensErrorRemainder_sub_eq_lag hT hTU]
  have hh : ∀ t, T ≤ t → |(1 + t) / t ^ 2 * mertensLagPrimitive t| ≤ 2 * η / T := by
    intro t ht
    have ht0 : 0 < t := by linarith
    rw [abs_mul, abs_of_pos (by positivity)]
    have h1 : (1 + t) / t ^ 2 ≤ 2 / T := by
      rw [div_le_div_iff₀ (by positivity) hT0]; nlinarith
    calc (1 + t) / t ^ 2 * |mertensLagPrimitive t| ≤ 2 / T * η :=
          mul_le_mul h1 (hv t ht) (abs_nonneg _) (by positivity)
      _ = 2 * η / T := by ring
  have hint : |∫ t in T..U, (t + 2) / t ^ 3 * mertensLagPrimitive t| ≤ 3 * η / T := by
    have hpt : ∀ᵐ t ∂volume, t ∈ Ioc T U → ‖(t + 2) / t ^ 3 * mertensLagPrimitive t‖
        ≤ 3 * η * (1 / t ^ 2) := by
      refine Filter.Eventually.of_forall fun t ht => ?_
      have ht0 : 0 < t := by linarith [ht.1]
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity)]
      have ht1 : 1 ≤ t := by linarith [ht.1]
      have hk : (t + 2) / t ^ 3 ≤ 3 * (1 / t ^ 2) := by
        rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [pow_pos ht0 2]
      calc (t + 2) / t ^ 3 * |mertensLagPrimitive t| ≤ 3 * (1 / t ^ 2) * η :=
            mul_le_mul hk (hv t ht.1.le) (abs_nonneg _) (by positivity)
        _ = 3 * η * (1 / t ^ 2) := by ring
    have hc : ContinuousOn (fun t : ℝ => 3 * η * (1 / t ^ 2)) (uIcc T U) :=
      continuousOn_const.mul (continuousOn_const.div (continuousOn_id.pow 2) fun t ht => by
        rw [uIcc_of_le hTU] at ht
        have : 0 < t := by linarith [ht.1]
        positivity)
    have hle := intervalIntegral.norm_integral_le_of_norm_le hTU hpt hc.intervalIntegrable
    have hd : ∀ t ∈ uIcc T U, HasDerivAt (fun t : ℝ => -(3 * η) * t⁻¹) (3 * η * (1 / t ^ 2)) t := by
      intro t ht
      rw [uIcc_of_le hTU] at ht
      have ht0 : t ≠ 0 := by linarith [ht.1]
      have := (hasDerivAt_inv ht0).const_mul (-(3 * η))
      refine this.congr_deriv ?_
      field_simp
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable,
      Real.norm_eq_abs] at hle
    have hUi : 0 ≤ 3 * η * U⁻¹ := by positivity
    calc _ ≤ -(3 * η) * U⁻¹ - -(3 * η) * T⁻¹ := hle
      _ ≤ 3 * η * T⁻¹ := by linarith
      _ = 3 * η / T := by rw [div_eq_mul_inv]
  have hhT := hh T le_rfl
  have hhU := hh U hTU
  calc |(1 + T) / T ^ 2 * mertensLagPrimitive T - (1 + U) / U ^ 2 * mertensLagPrimitive U
        - ∫ t in T..U, (t + 2) / t ^ 3 * mertensLagPrimitive t|
      ≤ |(1 + T) / T ^ 2 * mertensLagPrimitive T - (1 + U) / U ^ 2 * mertensLagPrimitive U|
        + |∫ t in T..U, (t + 2) / t ^ 3 * mertensLagPrimitive t| := abs_sub _ _
    _ ≤ |(1 + T) / T ^ 2 * mertensLagPrimitive T| + |(1 + U) / U ^ 2 * mertensLagPrimitive U|
        + |∫ t in T..U, (t + 2) / t ^ 3 * mertensLagPrimitive t| := by gcongr; exact abs_sub _ _
    _ ≤ 2 * η / T + 2 * η / T + 3 * η / T := by gcongr
    _ = 7 * η / T := by ring

/-- **`T G(T) → 0` unconditionally**: `|G(T)| T ≤ ε` for all large `T`. -/
theorem eventually_abs_mertensErrorRemainder_mul_le {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, |mertensErrorRemainder T| * T ≤ ε := by
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp ((tendsto_iff_norm_sub_tendsto_zero.mp
    tendsto_mertensLagPrimitive_zero).eventually (ge_mem_nhds (show 0 < ε / 8 by positivity)))
  filter_upwards [eventually_ge_atTop (max T₀ 1)] with T hT
  have hT1 : 1 ≤ T := le_trans (le_max_right _ _) hT
  have hT0 : 0 < T := by linarith
  have hv : ∀ s, T ≤ s → |mertensLagPrimitive s| ≤ ε / 8 := fun s hs => by
    have := hT₀ s (le_trans (le_trans (le_max_left _ _) hT) hs)
    simpa only [sub_zero, Real.norm_eq_abs] using this
  have hδ : 0 < ε / 8 / T := by positivity
  obtain ⟨U₁, hU₁, hTU₁⟩ := ((frequently_mertensErrorRemainder_le hδ).and_eventually
    (eventually_ge_atTop T)).exists
  obtain ⟨U₂, hU₂, hTU₂⟩ := ((frequently_mertensErrorRemainder_ge hδ).and_eventually
    (eventually_ge_atTop T)).exists
  have h1 := abs_mertensErrorRemainder_sub_le_of_lag (by positivity) hT1 hTU₁ hv
  have h2 := abs_mertensErrorRemainder_sub_le_of_lag (by positivity) hT1 hTU₂ hv
  have hb : |mertensErrorRemainder T| ≤ ε / T := by
    have e : ε / T = 7 * (ε / 8) / T + ε / 8 / T := by ring
    rw [abs_le, e]
    constructor
    · linarith [(abs_le.mp h2).1]
    · linarith [(abs_le.mp h1).2]
  calc |mertensErrorRemainder T| * T ≤ ε / T * T := mul_le_mul_of_nonneg_right hb hT0.le
    _ = ε := by field_simp


/-! ## The scaled remainder -/

/-- The scaled Mertens remainder `s(T) = G(T) e^{T/2} T`. -/
def scaledMertensRemainder (T : ℝ) : ℝ := mertensErrorRemainder T * (Real.exp (T / 2) * T)

theorem continuousOn_scaledMertensRemainder (U : ℝ) :
    ContinuousOn scaledMertensRemainder (Icc 1 U) :=
  (continuousOn_mertensErrorRemainder U).mul
    ((Real.continuous_exp.comp (continuous_id.div_const 2)).continuousOn.mul continuousOn_id)

/-- **`s(T) ≥ -K` for arbitrarily large `T`** once `K > a₁ + 1`. -/
theorem frequently_neg_le_scaledMertensRemainder {K : ℝ} (hK : poleSharpConstant + 1 < K) :
    ∃ᶠ T : ℝ in atTop, -K ≤ scaledMertensRemainder T := by
  by_contra h
  rw [not_frequently] at h
  have hlt : ∀ᶠ T : ℝ in atTop, scaledMertensRemainder T < -K :=
    h.mono fun T hT => not_le.mp hT
  have ha := poleSharpConstant_pos
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp (hlt.and (eventually_ge_atTop (1 : ℝ)))
  have hRH : RiemannHypothesis := by
    refine riemannHypothesis_of_remainder_le (B := 0) (T₀ := max T₀ 1) le_rfl (le_max_right _ _)
      fun s hs => ?_
    obtain ⟨h1, h2⟩ := hT₀ s (le_trans (le_max_left _ _) hs)
    have hs0 : 0 < s := by linarith
    have hσ : 0 < Real.exp (s / 2) * s := by positivity
    rw [zero_mul, zero_div]
    unfold scaledMertensRemainder at h1
    by_contra hG
    push Not at hG
    have := mul_pos hG hσ
    linarith
  have hT := (tendsto_mertensErrorRemainder_scaled_sub_lag hRH).comp Real.tendsto_exp_atTop
  have hev : ∀ᶠ T : ℝ in atTop, -(1 / 2) < scaledMertensRemainder T - weilLagFunctionReal T := by
    refine (hT.eventually (lt_mem_nhds (by norm_num : (-(1 / 2) : ℝ) < 0))).mono fun T hT' => ?_
    simp only [Function.comp, Real.log_exp] at hT'
    unfold scaledMertensRemainder
    rwa [Real.exp_half]
  obtain ⟨T, h1, h2⟩ := (hlt.and hev).exists
  have hΦ : |weilLagFunctionReal T| ≤ poleSharpConstant := by
    have := norm_weilLagFunction_le_of_riemannHypothesis hRH T
    rwa [weilLagFunction_eq_ofReal, Complex.norm_real, Real.norm_eq_abs] at this
  linarith [neg_abs_le (weilLagFunctionReal T)]

/-! ## At a minimum of the scaled remainder -/

/-- `ψ(y) - ψ(x) ≤ log y` for `1 ≤ x ≤ y ≤ x + 1`. -/
theorem psi_sub_psi_le_log {x y : ℝ} (hx : 1 ≤ x) (hxy : x ≤ y) (hy : y ≤ x + 1) :
    Chebyshev.psi y - Chebyshev.psi x ≤ Real.log y := by
  rw [Chebyshev.psi_eq_sum_Icc, Chebyshev.psi_eq_sum_Icc]
  have h1 : ⌊y⌋₊ ≤ ⌊x⌋₊ + 1 := by
    have := Nat.floor_le_floor (R := ℝ) hy
    rwa [Nat.floor_add_one (by linarith)] at this
  have h2 : ⌊x⌋₊ ≤ ⌊y⌋₊ := Nat.floor_le_floor hxy
  have hly : 0 ≤ Real.log y := Real.log_nonneg (by linarith)
  obtain h | h : ⌊y⌋₊ = ⌊x⌋₊ ∨ ⌊y⌋₊ = ⌊x⌋₊ + 1 := by omega
  · rw [h, sub_self]; exact hly
  · rw [h, Finset.sum_Icc_succ_top (by omega), add_sub_cancel_left]
    refine ArithmeticFunction.vonMangoldt_le_log.trans (Real.log_le_log ?_ ?_)
    · exact_mod_cast Nat.succ_pos _
    · have := Nat.floor_le (show 0 ≤ y by linarith)
      rw [h] at this
      exact_mod_cast this

/-- `σ(T) ≤ (1 + 2h) σ(T - h)` for `σ(T) = e^{T/2} T`, `T ≥ 4`, `0 < h ≤ 1`. -/
theorem exp_half_mul_le_of_sub {T h : ℝ} (hT : 4 ≤ T) (h0 : 0 < h) (h1 : h ≤ 1) :
    Real.exp (T / 2) * T ≤ (1 + 2 * h) * (Real.exp ((T - h) / 2) * (T - h)) := by
  have he : Real.exp (T / 2) = Real.exp ((T - h) / 2) * Real.exp (h / 2) := by
    rw [← Real.exp_add]; ring_nf
  have hb := Real.exp_bound_div_one_sub_of_interval' (show 0 < h / 2 by positivity)
    (show h / 2 < 1 by linarith)
  have hb' : Real.exp (h / 2) ≤ 1 + h := by
    refine hb.le.trans ?_
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have hTh : T ≤ (1 + h / 3) * (T - h) := by nlinarith
  have hE := Real.exp_pos ((T - h) / 2)
  rw [he]
  calc Real.exp ((T - h) / 2) * Real.exp (h / 2) * T
      ≤ Real.exp ((T - h) / 2) * (1 + h) * ((1 + h / 3) * (T - h)) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_left hb' hE.le) hTh (by linarith) (by positivity)
    _ = (1 + h) * (1 + h / 3) * (Real.exp ((T - h) / 2) * (T - h)) := by ring
    _ ≤ (1 + 2 * h) * (Real.exp ((T - h) / 2) * (T - h)) := by
        refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg (Real.exp_pos _).le (by linarith))
        nlinarith

/-- The weight `w(s) = (1 + s)e^{-s}/s²` is antitone on `(0, ∞)`. -/
theorem mertensAbelWeight_anti {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) :
    mertensAbelWeight t ≤ mertensAbelWeight s := by
  unfold mertensAbelWeight
  have ht : 0 < t := by linarith
  have h1 : (1 + t) / t ^ 2 ≤ (1 + s) / s ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith [mul_pos hs ht]
  have h2 : Real.exp (-t) ≤ Real.exp (-s) := Real.exp_le_exp.mpr (by linarith)
  have e1 : (1 + t) * Real.exp (-t) / t ^ 2 = (1 + t) / t ^ 2 * Real.exp (-t) := by ring
  have e2 : (1 + s) * Real.exp (-s) / s ^ 2 = (1 + s) / s ^ 2 * Real.exp (-s) := by ring
  rw [e1, e2]
  exact mul_le_mul h1 h2 (Real.exp_pos _).le (by positivity)

theorem mertensAbelWeight_pos {s : ℝ} (hs : 0 < s) : 0 < mertensAbelWeight s := by
  unfold mertensAbelWeight; positivity

/-- **The Chebyshev error under one-sided remainder comparisons.**  If `T ≥ 4`, `0 < h ≤ 1`,
`e^T(e^h - 1) ≤ 1`, `G(T) < 0`, `G(T) ≤ G(T + h)` and `(1 + 2h)G(T) ≤ G(T - h)`, then
`|ψ(x) - x| ≤ 2T|G(T)|x + log(x + 1)` at `x = e^T`. -/
theorem abs_psi_sub_le_of_remainder_comparison {T h : ℝ} (hT : 4 ≤ T) (h0 : 0 < h)
    (h1 : h ≤ 1) (hx1 : Real.exp T * (Real.exp h - 1) ≤ 1) (hG : mertensErrorRemainder T < 0)
    (hGr : mertensErrorRemainder T ≤ mertensErrorRemainder (T + h))
    (hGl : (1 + 2 * h) * mertensErrorRemainder T ≤ mertensErrorRemainder (T - h)) :
    |Chebyshev.psi (Real.exp T) - Real.exp T|
      ≤ 2 * T * |mertensErrorRemainder T| * Real.exp T + Real.log (Real.exp T + 1) := by
  set x := Real.exp T with hxdef
  have hx0 : 0 < x := Real.exp_pos T
  have hx1' : 1 ≤ x := Real.one_le_exp (by linarith)
  have hT0 : 0 < T := by linarith
  have hl2 : Real.log 2 ≤ T - h := by have := Real.log_two_lt_d9; linarith
  have hl2' : Real.log 2 ≤ T := by linarith
  set G := mertensErrorRemainder T with hGdef
  -- the right side: `ψ(x) - x ≥ -log(x + 1)`
  have hright : -Real.log (x + 1) ≤ Chebyshev.psi x - x := by
    by_contra hc
    push Not at hc
    set c := x - Chebyshev.psi x - Real.log (x + 1) with hc'
    have hcpos : 0 < c := by rw [hc']; linarith
    have hsub := mertensErrorRemainder_sub_eq hl2' (show T ≤ T + h by linarith)
    have hwc := continuousOn_mertensAbelWeight (by linarith : (0 : ℝ) < T) (show T ≤ T + h by
      linarith)
    have hint : IntervalIntegrable (fun s => (Real.exp s - Chebyshev.psi (Real.exp s))
        * mertensAbelWeight s) volume T (T + h) :=
      (intervalIntegrable_chebyshevDeficit T (T + h)).mul_continuousOn hwc
    have hmono : ∫ s in T..(T + h), c * mertensAbelWeight (T + h)
        ≤ ∫ s in T..(T + h), (Real.exp s - Chebyshev.psi (Real.exp s)) * mertensAbelWeight s := by
      refine intervalIntegral.integral_mono_on (by linarith) intervalIntegrable_const hint
        fun s hs => ?_
      have hs0 : 0 < s := by linarith [hs.1]
      have hes : x ≤ Real.exp s := Real.exp_le_exp.mpr hs.1
      have hes' : Real.exp s ≤ x + 1 := by
        have : Real.exp s ≤ Real.exp (T + h) := Real.exp_le_exp.mpr hs.2
        rw [Real.exp_add] at this
        linarith
      have hψ := psi_sub_psi_le_log hx1' hes hes'
      have hlog : Real.log (Real.exp s) ≤ Real.log (x + 1) := Real.log_le_log (Real.exp_pos _) hes'
      have hw := mertensAbelWeight_anti hs0 hs.2
      have hw0 := mertensAbelWeight_pos (show 0 < T + h by linarith)
      have hcs : c ≤ Real.exp s - Chebyshev.psi (Real.exp s) := by rw [hc']; linarith
      exact mul_le_mul hcs hw hw0.le (by linarith)
    rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
    have hw0 := mertensAbelWeight_pos (show 0 < T + h by linarith)
    have : 0 < (T + h - T) * (c * mertensAbelWeight (T + h)) := by
      have : T + h - T = h := by ring
      rw [this]; positivity
    linarith
  -- the left side: `ψ(x) - x ≤ log x + 2T|G|x`
  have hleft : Chebyshev.psi x - x ≤ Real.log (x + 1) + 2 * T * |G| * x := by
    have hdiff : G - mertensErrorRemainder (T - h) ≤ 2 * h * |G| := by
      rw [abs_of_neg hG]; linarith
    by_contra hc
    push Not at hc
    have hlx : Real.log x ≤ Real.log (x + 1) := Real.log_le_log hx0 (by linarith)
    set c := Chebyshev.psi x - x - Real.log x with hc'
    have hcpos : 2 * T * |G| * x < c := by rw [hc']; linarith
    have hsub := mertensErrorRemainder_sub_eq hl2 (show T - h ≤ T by linarith)
    have hwc := continuousOn_mertensAbelWeight (by linarith : (0 : ℝ) < T - h)
      (show T - h ≤ T by linarith)
    have hint : IntervalIntegrable (fun s => (Real.exp s - Chebyshev.psi (Real.exp s))
        * mertensAbelWeight s) volume (T - h) T :=
      (intervalIntegrable_chebyshevDeficit (T - h) T).mul_continuousOn hwc
    have hmono : ∫ s in (T - h)..T, (Real.exp s - Chebyshev.psi (Real.exp s)) * mertensAbelWeight s
        ≤ ∫ s in (T - h)..T, -(c * mertensAbelWeight T) := by
      refine intervalIntegral.integral_mono_on (by linarith) hint intervalIntegrable_const
        fun s hs => ?_
      have hs0 : 0 < s := by linarith [hs.1]
      have hes : Real.exp s ≤ x := Real.exp_le_exp.mpr hs.2
      have hes1 : 1 ≤ Real.exp s := Real.one_le_exp (by linarith [hs.1])
      have hes' : x ≤ Real.exp s + 1 := by
        have h5 : Real.exp (T - h) ≤ Real.exp s := Real.exp_le_exp.mpr hs.1
        have h6 : x - Real.exp (T - h) ≤ x * (Real.exp h - 1) := by
          have h7 : Real.exp (T - h) * Real.exp h = x := by
            rw [← Real.exp_add, hxdef]; ring_nf
          have h8 : x * (Real.exp h - 1) - (x - Real.exp (T - h))
              = Real.exp (T - h) * (Real.exp h - 1) ^ 2 := by rw [← h7]; ring
          have : 0 ≤ Real.exp (T - h) * (Real.exp h - 1) ^ 2 := by positivity
          linarith
        linarith
      have hψ := psi_sub_psi_le_log hes1 hes hes'
      have hlog : Real.log x ≤ Real.log x := le_rfl
      have hw := mertensAbelWeight_anti hs0 hs.2
      have hw0 := mertensAbelWeight_pos (show 0 < T by linarith)
      have hc0 : 0 < c := lt_of_le_of_lt (by positivity) hcpos
      have hcs : Real.exp s - Chebyshev.psi (Real.exp s) ≤ -c := by rw [hc']; linarith
      calc (Real.exp s - Chebyshev.psi (Real.exp s)) * mertensAbelWeight s
          ≤ -c * mertensAbelWeight s := mul_le_mul_of_nonneg_right hcs (by linarith)
        _ ≤ -c * mertensAbelWeight T := by nlinarith
        _ = -(c * mertensAbelWeight T) := by ring
    rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
    have hTh : T - (T - h) = h := by ring
    rw [hTh] at hmono
    have hwT : mertensAbelWeight T * (T * x) ≥ 1 := by
      unfold mertensAbelWeight
      rw [hxdef]
      have hE : Real.exp (-T) * Real.exp T = 1 := by rw [← Real.exp_add]; simp
      have : (1 + T) * Real.exp (-T) / T ^ 2 * (T * Real.exp T) = (1 + T) / T := by
        field_simp
        linear_combination hE
      rw [this, ge_iff_le, le_div_iff₀ hT0]; linarith
    have hw0 := mertensAbelWeight_pos (show 0 < T by linarith)
    have hkey : c * mertensAbelWeight T * h ≤ 2 * h * |G| := by
      have : G - mertensErrorRemainder (T - h) = -(mertensErrorRemainder (T - h) - G) := by ring
      linarith
    have hkey2 : c * mertensAbelWeight T ≤ 2 * |G| := by
      have := le_of_mul_le_mul_right (show c * mertensAbelWeight T * h ≤ 2 * |G| * h by linarith) h0
      exact this
    have : 2 * T * |G| * x * mertensAbelWeight T < c * mertensAbelWeight T :=
      mul_lt_mul_of_pos_right hcpos hw0
    have h9 : 2 * |G| ≤ 2 * T * |G| * x * mertensAbelWeight T := by
      have : 2 * T * |G| * x * mertensAbelWeight T = 2 * |G| * (mertensAbelWeight T * (T * x)) := by
        ring
      rw [this]
      have := abs_nonneg G
      nlinarith
    linarith
  rw [abs_le]
  constructor
  · have : 0 ≤ 2 * T * |G| * x := by positivity
    linarith
  · linarith


/-- **The Chebyshev error at a minimum of `s`.**  If `T ≥ 4`, `0 < h ≤ 1`, `e^T(e^h - 1) ≤ 1`,
`G(T) < 0` and `s(T) ≤ s(T ± h)`, then `|ψ(x) - x| ≤ 2T|G(T)|x + log(x + 1)` at `x = e^T`. -/
theorem abs_psi_sub_le_of_scaled_local_min {T h : ℝ} (hT : 4 ≤ T) (h0 : 0 < h) (h1 : h ≤ 1)
    (hx1 : Real.exp T * (Real.exp h - 1) ≤ 1) (hG : mertensErrorRemainder T < 0)
    (hl : scaledMertensRemainder T ≤ scaledMertensRemainder (T - h))
    (hr : scaledMertensRemainder T ≤ scaledMertensRemainder (T + h)) :
    |Chebyshev.psi (Real.exp T) - Real.exp T|
      ≤ 2 * T * |mertensErrorRemainder T| * Real.exp T + Real.log (Real.exp T + 1) := by
  have hT0 : 0 < T := by linarith
  unfold scaledMertensRemainder at hl hr
  set G := mertensErrorRemainder T with hGdef
  have hGr : G ≤ mertensErrorRemainder (T + h) := by
    have hσ : Real.exp (T / 2) * T ≤ Real.exp ((T + h) / 2) * (T + h) :=
      mul_le_mul (Real.exp_le_exp.mpr (by linarith)) (by linarith) hT0.le (Real.exp_pos _).le
    by_contra hc
    push Not at hc
    have := mul_lt_mul_of_pos_right hc (show 0 < Real.exp ((T + h) / 2) * (T + h) by positivity)
    nlinarith
  have hGl : (1 + 2 * h) * G ≤ mertensErrorRemainder (T - h) := by
    have hσ := exp_half_mul_le_of_sub hT h0 h1
    have hThpos : 0 < Real.exp ((T - h) / 2) * (T - h) := by
      have : 0 < T - h := by linarith
      positivity
    by_contra hc
    push Not at hc
    have h3 := mul_lt_mul_of_pos_right hc hThpos
    have h4 : G * ((1 + 2 * h) * (Real.exp ((T - h) / 2) * (T - h)))
        ≤ G * (Real.exp (T / 2) * T) := mul_le_mul_of_nonpos_left hσ hG.le
    nlinarith
  exact abs_psi_sub_le_of_remainder_comparison hT h0 h1 hx1 hG hGr hGl

/-! ## The Nicolas defect at a minimum -/

/-- `log(x + 1) ≤ 2√x` for `x ≥ 0`. -/
theorem log_add_one_le_two_sqrt {x : ℝ} (hx : 0 ≤ x) : Real.log (x + 1) ≤ 2 * Real.sqrt x := by
  have h1 : Real.log (x + 1) = 2 * Real.log (Real.sqrt (x + 1)) := by
    rw [Real.log_sqrt (by linarith)]; ring
  have h2 : Real.log (Real.sqrt (x + 1)) ≤ Real.sqrt (x + 1) - 1 :=
    Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr (by linarith))
  have h3 : Real.sqrt (x + 1) ≤ Real.sqrt x + 1 := by
    have h4 : x + 1 ≤ (Real.sqrt x + 1) ^ 2 := by
      have := Real.sq_sqrt hx
      nlinarith [Real.sqrt_nonneg x]
    calc Real.sqrt (x + 1) ≤ Real.sqrt ((Real.sqrt x + 1) ^ 2) := Real.sqrt_le_sqrt h4
      _ = Real.sqrt x + 1 := Real.sqrt_sq (by positivity)
  linarith

/-- **The Nicolas defect at a near-zero of `ψ(x) - x`.**  If
`|ψ(x) - x| ≤ 2T|G(T)|x + log(x + 1)` at `x = e^T`, `G(T) < 0`, `T|G(T)| ≤ 1/280` and `x` is large,
then `Nic(x) ≤ G(T)/2 + (8 log 4 + C + 1)/(√x T)`. -/
theorem nicolasDefect_le_half_remainder {T C : ℝ} (hT : 8 ≤ T)
    (hθ25 : 2 / 5 * Real.exp T ≤ Chebyshev.theta (Real.exp T))
    (hC : Chebyshev.psi (Real.exp T) - Chebyshev.theta (Real.exp T) ≤ C * Real.sqrt (Real.exp T))
    (hG : mertensErrorRemainder T < 0)
    (hTG : |mertensErrorRemainder T| * T ≤ 1 / 280)
    (hψ : |Chebyshev.psi (Real.exp T) - Real.exp T|
      ≤ 2 * T * |mertensErrorRemainder T| * Real.exp T + Real.log (Real.exp T + 1))
    (hbig : (140 + 18 * C ^ 2) ^ 2 ≤ Real.exp T) :
    nicolasDefect (Real.exp T)
      ≤ mertensErrorRemainder T / 2
        + (8 * Real.log 4 + C + 1) / (Real.sqrt (Real.exp T) * T) := by
  set x := Real.exp T with hxdef
  set a := |mertensErrorRemainder T| with ha
  have hx9 : 9 ≤ x := by have := Real.add_one_le_exp T; linarith
  have hx0 : 0 < x := by linarith
  have hT0 : 0 < T := by linarith
  have hlogx : Real.log x = T := Real.log_exp T
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hxx : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0.le
  have hlθ1 : 1 ≤ Real.log (Chebyshev.theta x) := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9; linarith
  have hnd := nicolasDefect_le (by linarith) hθ25 hlθ1 hC
  rw [hlogx] at hnd
  have hψθ0 : 0 ≤ Chebyshev.psi x - Chebyshev.theta x := by
    linarith [Chebyshev.theta_le_psi x]
  -- the second-order term
  have hL1 : Real.log (x + 1) ^ 2 ≤ 4 * x := by
    have h1 := log_add_one_le_two_sqrt hx0.le
    have h0 : 0 ≤ Real.log (x + 1) := Real.log_nonneg (by linarith)
    have : Real.log (x + 1) ^ 2 ≤ (2 * Real.sqrt x) ^ 2 := pow_le_pow_left₀ h0 h1 2
    rw [mul_pow, Real.sq_sqrt hx0.le] at this
    linarith
  have hψx2 : (Chebyshev.psi x - x) ^ 2 ≤ 8 * T ^ 2 * a ^ 2 * x ^ 2 + 8 * x := by
    have h0 : 0 ≤ 2 * T * a * x + Real.log (x + 1) := by
      have := Real.log_nonneg (show (1 : ℝ) ≤ x + 1 by linarith)
      positivity
    have h1 : (Chebyshev.psi x - x) ^ 2 ≤ (2 * T * a * x + Real.log (x + 1)) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hψ 2
    nlinarith [sq_nonneg (2 * T * a * x - Real.log (x + 1))]
  have hψθ2 : (Chebyshev.psi x - Chebyshev.theta x) ^ 2 ≤ C ^ 2 * x := by
    have : (Chebyshev.psi x - Chebyshev.theta x) ^ 2 ≤ (C * Real.sqrt x) ^ 2 :=
      pow_le_pow_left₀ hψθ0 hC 2
    rwa [mul_pow, Real.sq_sqrt hx0.le] at this
  have hθx2 : (Chebyshev.theta x - x) ^ 2 ≤ 16 * T ^ 2 * a ^ 2 * x ^ 2 + (16 + 2 * C ^ 2) * x := by
    have e : Chebyshev.theta x - x
        = (Chebyshev.psi x - x) - (Chebyshev.psi x - Chebyshev.theta x) := by ring
    rw [e]
    nlinarith [sq_nonneg ((Chebyshev.psi x - x) + (Chebyshev.psi x - Chebyshev.theta x))]
  have hQ : 35 / 4 * ((Chebyshev.theta x - x) ^ 2 / (x ^ 2 * T))
      ≤ 140 * T * a ^ 2 + (140 + 35 / 2 * C ^ 2) / (x * T) := by
    have h1 : (Chebyshev.theta x - x) ^ 2 / (x ^ 2 * T)
        ≤ (16 * T ^ 2 * a ^ 2 * x ^ 2 + (16 + 2 * C ^ 2) * x) / (x ^ 2 * T) :=
      div_le_div_of_nonneg_right hθx2 (by positivity)
    have h2 : (16 * T ^ 2 * a ^ 2 * x ^ 2 + (16 + 2 * C ^ 2) * x) / (x ^ 2 * T)
        = 16 * T * a ^ 2 + (16 + 2 * C ^ 2) / (x * T) := by
      field_simp
    have h3 : 35 / 4 * (16 * T * a ^ 2 + (16 + 2 * C ^ 2) / (x * T))
        = 140 * T * a ^ 2 + (140 + 35 / 2 * C ^ 2) / (x * T) := by
      field_simp; ring
    calc 35 / 4 * ((Chebyshev.theta x - x) ^ 2 / (x ^ 2 * T))
        ≤ 35 / 4 * (16 * T * a ^ 2 + (16 + 2 * C ^ 2) / (x * T)) := by
          rw [← h2]; exact mul_le_mul_of_nonneg_left h1 (by norm_num)
      _ = _ := h3
  have ha2 : 140 * T * a ^ 2 ≤ a / 2 := by
    have h0 : 0 ≤ a := abs_nonneg _
    have : 140 * T * a ^ 2 = 140 * ((a * T) * a) := by ring
    rw [this]
    have := mul_le_mul_of_nonneg_right hTG h0
    linarith
  have hsmall : (140 + 35 / 2 * C ^ 2) / (x * T) ≤ 1 / (Real.sqrt x * T) := by
    have hbig' : 140 + 18 * C ^ 2 ≤ Real.sqrt x := by
      rw [Real.le_sqrt (by positivity) hx0.le]; exact hbig
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : (140 + 35 / 2 * C ^ 2) * Real.sqrt x ≤ x := by
      calc (140 + 35 / 2 * C ^ 2) * Real.sqrt x ≤ Real.sqrt x * Real.sqrt x :=
            mul_le_mul_of_nonneg_right (by nlinarith [sq_nonneg C]) hsx.le
        _ = x := hxx
    calc (140 + 35 / 2 * C ^ 2) * (Real.sqrt x * T)
          = ((140 + 35 / 2 * C ^ 2) * Real.sqrt x) * T := by ring
      _ ≤ x * T := mul_le_mul_of_nonneg_right this hT0.le
      _ = 1 * (x * T) := by ring
  -- conclusion
  have hGa : mertensErrorRemainder T = -a := by rw [ha, abs_of_neg hG]; ring
  have hD : 0 < Real.sqrt x * T := by positivity
  have e : (8 * Real.log 4 + C + 1) / (Real.sqrt x * T)
      = (8 * Real.log 4 + C) / (Real.sqrt x * T) + 1 / (Real.sqrt x * T) := by ring
  rw [e, hGa]
  linarith only [hnd, hQ, ha2, hsmall, hGa]

/-- **The Nicolas defect bounds the scaled remainder at a near-zero of `ψ(x) - x`.**  If
`Nic(x) ≥ 0` at `x = e^T` and `|ψ(x) - x| ≤ 2T|G(T)|x + log(x + 1)`, with `T|G(T)| ≤ 1/280` and
`x` large, then `s(T) ≥ -(2(8 log 4 + C) + 2)`. -/
theorem scaledMertensRemainder_ge_of_nicolas {T C : ℝ} (hT : 8 ≤ T)
    (hθ25 : 2 / 5 * Real.exp T ≤ Chebyshev.theta (Real.exp T))
    (hC : Chebyshev.psi (Real.exp T) - Chebyshev.theta (Real.exp T) ≤ C * Real.sqrt (Real.exp T))
    (hNic : 0 ≤ nicolasDefect (Real.exp T)) (hG : mertensErrorRemainder T < 0)
    (hTG : |mertensErrorRemainder T| * T ≤ 1 / 280)
    (hψ : |Chebyshev.psi (Real.exp T) - Real.exp T|
      ≤ 2 * T * |mertensErrorRemainder T| * Real.exp T + Real.log (Real.exp T + 1))
    (hbig : (140 + 18 * C ^ 2) ^ 2 ≤ Real.exp T) :
    -(2 * (8 * Real.log 4 + C) + 2) ≤ scaledMertensRemainder T := by
  have h := nicolasDefect_le_half_remainder hT hθ25 hC hG hTG hψ hbig
  have hT0 : 0 < T := by linarith
  have hD : 0 < Real.sqrt (Real.exp T) * T := by positivity
  have h1 : -(mertensErrorRemainder T / 2)
      ≤ (8 * Real.log 4 + C + 1) / (Real.sqrt (Real.exp T) * T) := by linarith
  have h2 := (le_div_iff₀ hD).mp h1
  unfold scaledMertensRemainder
  rw [Real.exp_half]
  linarith

/-- **The Nicolas inequality for all large real `x` keeps the scaled remainder bounded below.** -/
theorem exists_neg_le_scaledMertensRemainder_of_nicolasDefect
    (hNic : ∀ᶠ x : ℝ in atTop, 0 ≤ nicolasDefect x) :
    ∃ K T₀ : ℝ, 0 ≤ K ∧ 1 ≤ T₀ ∧ ∀ T, T₀ ≤ T → -K ≤ scaledMertensRemainder T := by
  obtain ⟨C₀, hC₀⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  set C := max C₀ 0 with hCdef
  have hC0 : 0 ≤ C := le_max_right _ _
  have hC : ∀ x, Chebyshev.psi x - Chebyshev.theta x ≤ C * Real.sqrt x := fun x =>
    (hC₀ x).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg x))
  have hl4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  set K' := 2 * (8 * Real.log 4 + C) + 2 with hK'
  set K := K' + 1 with hK
  have ha3 := poleSharpConstant_lt_three_tenths
  have hKa : poleSharpConstant + 1 < K := by rw [hK, hK']; nlinarith
  have hev : ∀ᶠ T : ℝ in atTop, 8 ≤ T ∧ 2 / 5 * Real.exp T ≤ Chebyshev.theta (Real.exp T)
      ∧ 0 ≤ nicolasDefect (Real.exp T) ∧ |mertensErrorRemainder T| * T ≤ 1 / 280
      ∧ (140 + 18 * C ^ 2) ^ 2 ≤ Real.exp T := by
    filter_upwards [eventually_ge_atTop (8 : ℝ),
      Real.tendsto_exp_atTop.eventually eventually_two_fifths_le_theta,
      Real.tendsto_exp_atTop.eventually hNic,
      eventually_abs_mertensErrorRemainder_mul_le (show (0 : ℝ) < 1 / 280 by norm_num),
      Real.tendsto_exp_atTop.eventually (eventually_ge_atTop ((140 + 18 * C ^ 2) ^ 2))]
      with T h1 h2 h3 h4 h5
    exact ⟨h1, h2, h3, h4, h5⟩
  obtain ⟨Ta, hTa⟩ := eventually_atTop.mp hev
  obtain ⟨T₁, hs₁, hT₁⟩ := ((frequently_neg_le_scaledMertensRemainder hKa).and_eventually
    (eventually_ge_atTop Ta)).exists
  have hT₁8 : 8 ≤ T₁ := (hTa T₁ hT₁).1
  refine ⟨K, T₁, by rw [hK, hK']; positivity, by linarith, fun T hT => ?_⟩
  by_contra hlt
  push Not at hlt
  obtain ⟨T₂, hs₂, hT₂⟩ := ((frequently_neg_le_scaledMertensRemainder hKa).and_eventually
    (eventually_ge_atTop T)).exists
  have hcont : ContinuousOn scaledMertensRemainder (Icc T₁ T₂) :=
    (continuousOn_scaledMertensRemainder T₂).mono (Icc_subset_Icc_left (by linarith))
  obtain ⟨Tm, hTm, hmin⟩ := isCompact_Icc.exists_isMinOn ⟨T₁, ⟨le_rfl, le_trans hT hT₂⟩⟩ hcont
  have hsm : scaledMertensRemainder Tm < -K :=
    lt_of_le_of_lt (hmin ⟨hT, hT₂⟩) hlt
  have hTm1 : T₁ < Tm := by
    rcases eq_or_lt_of_le hTm.1 with h | h
    · rw [← h] at hsm; linarith
    · exact h
  have hTm2 : Tm < T₂ := by
    rcases eq_or_lt_of_le hTm.2 with h | h
    · rw [h] at hsm; linarith
    · exact h
  obtain ⟨hTm8, hθ25, hNicm, hTG, hbig⟩ := hTa Tm (by linarith)
  have hTm0 : 0 < Tm := by linarith
  have hG : mertensErrorRemainder Tm < 0 := by
    unfold scaledMertensRemainder at hsm
    by_contra hc
    push Not at hc
    have : 0 ≤ mertensErrorRemainder Tm * (Real.exp (Tm / 2) * Tm) := by positivity
    have : 0 < K := by rw [hK, hK']; positivity
    linarith
  set h := min (min 1 (Tm - T₁)) (min (T₂ - Tm) (Real.exp (-Tm) / 2)) with hhdef
  have hEm : Real.exp (-Tm) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have h0 : 0 < h := by
    have := Real.exp_pos (-Tm)
    simp only [hhdef, lt_min_iff]
    exact ⟨⟨by norm_num, by linarith⟩, by linarith, by positivity⟩
  have h1 : h ≤ 1 := le_trans (min_le_left _ _) (min_le_left _ _)
  have hhl : h ≤ Tm - T₁ := le_trans (min_le_left _ _) (min_le_right _ _)
  have hhr : h ≤ T₂ - Tm := le_trans (min_le_right _ _) (min_le_left _ _)
  have hhe : h ≤ Real.exp (-Tm) / 2 := le_trans (min_le_right _ _) (min_le_right _ _)
  have hx1 : Real.exp Tm * (Real.exp h - 1) ≤ 1 := by
    have hh2 : h < 1 := by linarith
    have hb := Real.exp_bound_div_one_sub_of_interval' h0 hh2
    have hb' : Real.exp h - 1 ≤ 2 * h := by
      have : 1 / (1 - h) ≤ 1 + 2 * h := by
        rw [div_le_iff₀ (by linarith)]; nlinarith
      linarith
    have hE : Real.exp Tm * Real.exp (-Tm) = 1 := by rw [← Real.exp_add]; simp
    calc Real.exp Tm * (Real.exp h - 1) ≤ Real.exp Tm * (2 * h) :=
          mul_le_mul_of_nonneg_left hb' (Real.exp_pos _).le
      _ ≤ Real.exp Tm * Real.exp (-Tm) :=
          mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le
      _ = 1 := hE
  have hl := hmin ⟨by linarith, by linarith⟩ (a := Tm - h)
  have hr := hmin ⟨by linarith, by linarith⟩ (a := Tm + h)
  have hψ := abs_psi_sub_le_of_scaled_local_min (by linarith) h0 h1 hx1 hG hl hr
  have := scaledMertensRemainder_ge_of_nicolas hTm8 hθ25 (hC _) hNicm hG hTG hψ hbig
  linarith

/-- **Nicolas's inequality for all large real `x` implies the Riemann hypothesis.** -/
theorem riemannHypothesis_of_eventually_nicolasDefect_nonneg
    (hNic : ∀ᶠ x : ℝ in atTop, 0 ≤ nicolasDefect x) : RiemannHypothesis := by
  obtain ⟨K, T₀, hK, hT₀, hs⟩ := exists_neg_le_scaledMertensRemainder_of_nicolasDefect hNic
  refine riemannHypothesis_of_remainder_ge hK hT₀ fun s hs' => ?_
  have h := hs s hs'
  unfold scaledMertensRemainder at h
  have hs0 : 0 < s := by linarith
  have hσ : 0 < Real.exp (s / 2) * s := by positivity
  have e : K * Real.exp (-s / 2) / s = K / (Real.exp (s / 2) * s) := by
    rw [show -s / 2 = -(s / 2) by ring, Real.exp_neg]
    field_simp
  rw [e, neg_le, le_div_iff₀ hσ]
  linarith

/-- **Nicolas's criterion, converse.**  If `N_k/φ(N_k) > e^γ log log N_k` for all large
primorials `N_k`, the Riemann hypothesis holds. -/
theorem riemannHypothesis_of_eventually_nicolas
    (hNic : ∀ᶠ n : ℕ in atTop, Real.exp Real.eulerMascheroniConstant
        * Real.log (Real.log ((primorial n : ℕ) : ℝ))
      < ((primorial n : ℕ) : ℝ) / ((primorial n).totient : ℝ)) : RiemannHypothesis :=
  riemannHypothesis_of_eventually_nicolasDefect_nonneg
    (eventually_nicolasDefect_nonneg_of_nicolas hNic)

/-- **Nicolas's criterion.**  The Riemann hypothesis holds if and only if
`N_k/φ(N_k) > e^γ log log N_k` for all large primorials `N_k`. -/
theorem riemannHypothesis_iff_eventually_nicolas :
    RiemannHypothesis ↔ ∀ᶠ n : ℕ in atTop, Real.exp Real.eulerMascheroniConstant
        * Real.log (Real.log ((primorial n : ℕ) : ℝ))
      < ((primorial n : ℕ) : ℝ) / ((primorial n).totient : ℝ) :=
  ⟨eventually_nicolas_inequality_of_riemannHypothesis, riemannHypothesis_of_eventually_nicolas⟩

end

end RHTower
