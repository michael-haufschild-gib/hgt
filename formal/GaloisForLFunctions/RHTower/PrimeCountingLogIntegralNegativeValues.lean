import GaloisForLFunctions.RHTower.PrimeCountingLiLandauLower
import GaloisForLFunctions.RHTower.PrimeCountingLogIntegralSignChange

/-!
# `π(x) < li(x)` infinitely often, and the sign changes of `π - li`

The negative half of Littlewood's theorem for `π - li`.  Under the Riemann hypothesis the error
integral `∫_{log 2}^{log x} (θ(e^s) - e^s)/s² ds` is at most `O(√x/log²x) + O(1)` (the prime-power
part `ψ - θ ≥ 0` only helps), and `θ ≤ ψ`, so at the negative Littlewood points
`ψ(x) - x < -c√x logloglog x` one has `π(x) - li(x) < -(c/2)√x logloglog x/log x`.  If the Riemann
hypothesis fails, the mirrored Landau theorem
(`riemannHypothesis_of_logIntegral_sub_sqrt_le_primeCounting`) gives `π(x) < li(x) - √x`
infinitely often.
-/

open Filter Topology MeasureTheory Set
open GaloisForLFunctions.RHTower

namespace RHTower

noncomputable section

/-- With `|D(t)| ≤ B e^{t/2}`, the error integral is at most
`2B e^{T/2}/T² + (4B/a) ∫_a^T e^{s/2}/s² ds`. -/
theorem integral_theta_sub_div_sq_le {B a T : ℝ} (ha : 0 < a) (haT : a ≤ T)
    (hB : ∀ t : ℝ, 0 ≤ t → |ccmLogChebyshevDeficitPrimitive t| ≤ B * Real.exp (t / 2)) :
    ∫ s in a..T, (Chebyshev.theta (Real.exp s) - Real.exp s) / s ^ 2
      ≤ 2 * B * (Real.exp (T / 2) / T ^ 2)
        + 4 * B / a * ∫ s in a..T, Real.exp (s / 2) / s ^ 2 := by
  have hB0 : 0 ≤ B := by
    have := (abs_nonneg _).trans (hB 0 le_rfl)
    exact nonneg_of_mul_nonneg_left this (Real.exp_pos _)
  set f : ℝ → ℝ := fun r => Real.exp r - Chebyshev.psi (Real.exp r) with hf
  set P : ℝ → ℝ := fun s => ∫ r in a..s, f r with hP
  set p : ℝ → ℝ := fun s => Chebyshev.psi (Real.exp s) - Chebyshev.theta (Real.exp s) with hp
  have hPc : Continuous P :=
    intervalIntegral.continuous_primitive (fun u v => intervalIntegrable_chebyshevDeficit u v) a
  have hPb : ∀ s ∈ Icc a T, -(2 * B * Real.exp (s / 2)) ≤ P s := fun s hs =>
    (neg_le_neg (abs_integral_chebyshevDeficit_le ha.le hs.1 hB)).trans (neg_abs_le _)
  have hinv2 := continuousOn_inv_pow_uIcc ha haT 2
  have hinv3 := continuousOn_inv_pow_uIcc ha haT 3
  have hW := continuousOn_exp_half_div_sq ha haT
  have hfi : IntervalIntegrable (fun s => (s ^ 2)⁻¹ * f s) volume a T :=
    (intervalIntegrable_chebyshevDeficit a T).continuousOn_mul hinv2
  have hpi : IntervalIntegrable (fun s => p s * (s ^ 2)⁻¹) volume a T :=
    (((Chebyshev.psi_mono.comp Real.exp_monotone).intervalIntegrable).sub
      ((Chebyshev.theta_mono.comp Real.exp_monotone).intervalIntegrable)).mul_continuousOn hinv2
  have hPi : IntervalIntegrable (fun s => -(2 * (s ^ 3)⁻¹ * P s)) volume a T :=
    ((continuousOn_const.mul hinv3).mul hPc.continuousOn).neg.intervalIntegrable
  have hsplit : ∫ s in a..T, (Chebyshev.theta (Real.exp s) - Real.exp s) / s ^ 2
      = -(∫ s in a..T, (s ^ 2)⁻¹ * f s) - ∫ s in a..T, p s * (s ^ 2)⁻¹ := by
    have hfin : IntervalIntegrable (fun s => -((s ^ 2)⁻¹ * f s)) volume a T := hfi.neg
    rw [← intervalIntegral.integral_neg, ← intervalIntegral.integral_sub hfin hpi]
    refine intervalIntegral.integral_congr fun s _ => ?_
    simp only [hf, hp]
    rw [div_eq_mul_inv]
    ring
  have hparts := integral_chebyshevDeficit_div_sq_eq ha haT
  have hbd : -((T ^ 2)⁻¹ * P T) ≤ 2 * B * (Real.exp (T / 2) / T ^ 2) := by
    have := mul_le_mul_of_nonneg_left (hPb T ⟨haT, le_rfl⟩) (inv_nonneg.mpr (sq_nonneg T))
    rw [div_eq_mul_inv]
    linarith
  have hint : ∫ s in a..T, -(2 * (s ^ 3)⁻¹ * P s)
      ≤ ∫ s in a..T, 4 * B / a * (Real.exp (s / 2) / s ^ 2) := by
    refine intervalIntegral.integral_mono_on haT hPi
      ((hW.intervalIntegrable).const_mul _) fun s hs => ?_
    have hs0 : 0 < s := lt_of_lt_of_le ha hs.1
    have h1 : -(2 * (s ^ 3)⁻¹ * P s) ≤ 2 * (s ^ 3)⁻¹ * (2 * B * Real.exp (s / 2)) := by
      have := mul_le_mul_of_nonneg_left (hPb s hs) (by positivity : (0 : ℝ) ≤ 2 * (s ^ 3)⁻¹)
      linarith
    have h2 : 2 * (s ^ 3)⁻¹ * (2 * B * Real.exp (s / 2))
        = 4 * B * Real.exp (s / 2) / s ^ 2 * (1 / s) := by
      field_simp
      ring
    have h3 : 1 / s ≤ 1 / a := one_div_le_one_div_of_le ha hs.1
    have h4 : 0 ≤ 4 * B * Real.exp (s / 2) / s ^ 2 := by positivity
    have h5 : 4 * B * Real.exp (s / 2) / s ^ 2 * (1 / s)
        ≤ 4 * B * Real.exp (s / 2) / s ^ 2 * (1 / a) :=
      mul_le_mul_of_nonneg_left h3 h4
    have h6 : 4 * B * Real.exp (s / 2) / s ^ 2 * (1 / a)
        = 4 * B / a * (Real.exp (s / 2) / s ^ 2) := by
      field_simp
    linarith
  have hpp : 0 ≤ ∫ s in a..T, p s * (s ^ 2)⁻¹ := by
    refine intervalIntegral.integral_nonneg haT fun s hs => ?_
    have hs0 : 0 < s := lt_of_lt_of_le ha hs.1
    exact mul_nonneg (sub_nonneg.mpr (Chebyshev.theta_le_psi _)) (by positivity)
  rw [intervalIntegral.integral_neg, intervalIntegral.integral_const_mul] at hint
  rw [hsplit, hparts]
  linarith

/-- **Under the Riemann hypothesis, `π - li` is bounded above by the Chebyshev error.**  There are
constants `K₁, K₂` with `π(x) - li(x) ≤ (ψ(x) - x)/log x + K₁√x/log²x + K₂` for `x ≥ e⁸`. -/
theorem exists_primeCounting_sub_logIntegral_le_of_riemannHypothesis (hRH : RiemannHypothesis) :
    ∃ K₁ K₂ : ℝ, 0 ≤ K₁ ∧ ∀ x : ℝ, Real.exp 8 ≤ x →
      (Nat.primeCounting ⌊x⌋₊ : ℝ) - ∫ t in (2 : ℝ)..x, 1 / Real.log t
        ≤ (Chebyshev.psi x - x) / Real.log x + K₁ * Real.sqrt x / Real.log x ^ 2 + K₂ := by
  obtain ⟨B, hB0, hB⟩ := riemannHypothesis_iff_logChebyshevDeficitPrimitive_bound.mp hRH
  set a : ℝ := Real.log 2 with ha
  have ha0 : 0 < a := Real.log_pos (by norm_num)
  have ha8 : a ≤ 8 := by have := Real.log_two_lt_d9; linarith
  set W₈ : ℝ := ∫ s in a..8, Real.exp (s / 2) / s ^ 2 with hW₈
  refine ⟨2 * B + 4 * (4 * B / a), 2 / a + 4 * B / a * W₈, by positivity, fun x hx => ?_⟩
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos 8) hx
  have hx2 : 2 ≤ x := by
    have := Real.add_one_le_exp 8; linarith
  set T : ℝ := Real.log x with hT
  have hT8 : 8 ≤ T := by rw [hT, Real.le_log_iff_exp_le hx0]; exact hx
  have hT0 : 0 < T := by linarith
  have haT : a ≤ T := le_trans ha8 hT8
  have hsq : Real.exp (T / 2) = Real.sqrt x := by
    rw [← Real.exp_log hx0, sqrt_exp_eq_exp_half_mul, ← hT]; ring_nf
  rw [primeCounting_sub_logIntegral_eq hx2, integral_theta_sub_eq_log_variable hx2]
  have hJ := integral_theta_sub_div_sq_le ha0 haT hB
  have hsplitW : ∫ s in a..T, Real.exp (s / 2) / s ^ 2
      = W₈ + ∫ s in (8 : ℝ)..T, Real.exp (s / 2) / s ^ 2 := by
    rw [hW₈, intervalIntegral.integral_add_adjacent_intervals
      ((continuousOn_exp_half_div_sq ha0 ha8).intervalIntegrable)
      ((continuousOn_exp_half_div_sq (by norm_num) hT8).intervalIntegrable)]
  have hW8T := integral_exp_half_div_sq_le hT8
  have hcoef : 0 ≤ 4 * B / a := by positivity
  have hJ' : ∫ s in a..T, (Chebyshev.theta (Real.exp s) - Real.exp s) / s ^ 2
      ≤ 2 * B * (Real.exp (T / 2) / T ^ 2) + 4 * B / a * (W₈
        + 4 * (Real.exp (T / 2) / T ^ 2)) := by
    rw [hsplitW] at hJ
    have := mul_le_mul_of_nonneg_left (add_le_add_left hW8T W₈) hcoef
    linarith
  have hθ : (Chebyshev.theta x - x) / T ≤ (Chebyshev.psi x - x) / T :=
    div_le_div_of_nonneg_right (by linarith [Chebyshev.theta_le_psi x]) hT0.le
  rw [hsq] at hJ'
  have hK : (2 * B + 4 * (4 * B / a)) * Real.sqrt x / T ^ 2
      = 2 * B * (Real.sqrt x / T ^ 2) + 4 * B / a * (4 * (Real.sqrt x / T ^ 2)) := by
    ring
  rw [hK]
  have h2a : 2 / Real.log 2 = 2 / a := rfl
  nlinarith

/-- **Littlewood's theorem for `π - li`, negative values, Riemann-hypothesis branch.** -/
theorem frequently_primeCounting_lt_logIntegral_sub_of_riemannHypothesis
    (hRH : RiemannHypothesis) :
    ∃ᶠ x : ℝ in atTop, (Nat.primeCounting ⌊x⌋₊ : ℝ)
      < (∫ t in (2 : ℝ)..x, 1 / Real.log t)
        - littlewoodConst / 28 * Real.sqrt x * Real.log (Real.log (Real.log x)) / Real.log x := by
  obtain ⟨K₁, K₂, hK₁, hbound⟩ := exists_primeCounting_sub_logIntegral_le_of_riemannHypothesis hRH
  set c : ℝ := littlewoodConst / 14 with hc
  have hc0 : 0 < c := by rw [hc]; have := littlewoodConst_pos; positivity
  have hev := ((eventually_ge_atTop (Real.exp 8)).and
    (eventually_log_le_mul_sqrt (by positivity : (0 : ℝ) < 1 / (|K₂| + 1)))).and
    (tendsto_logLogLog_atTop.eventually_ge_atTop ((K₁ + 1) / (c / 2)))
  refine ((frequently_chebyshevError_lt_littlewood_of_riemannHypothesis hRH).and_eventually
    hev).mono ?_
  rintro x ⟨hlw, ⟨hx8, hlog⟩, hL3⟩
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos 8) hx8
  have hlx : 8 ≤ Real.log x := by rw [Real.le_log_iff_exp_le hx0]; exact hx8
  have hlx0 : 0 < Real.log x := by linarith
  have hb := hbound x hx8
  set L := Real.log x with hL
  set u : ℝ := Real.sqrt x / L with hu
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hu0 : 0 < u := div_pos hsx hlx0
  set L3 := Real.log (Real.log (Real.log x)) with hL3def
  have hψ : (Chebyshev.psi x - x) / L < -(c * L3 * u) := by
    have : Chebyshev.psi x - x < -(c * Real.sqrt x * L3) := by
      simpa [chebyshevError, hc] using hlw
    rw [hu, div_lt_iff₀ hlx0]
    have : -(c * L3 * (Real.sqrt x / L)) * L = -(c * Real.sqrt x * L3) := by field_simp
    linarith
  have hK₁u : K₁ * Real.sqrt x / L ^ 2 ≤ K₁ * u := by
    rw [hu, div_le_iff₀ (by positivity)]
    have : K₁ * (Real.sqrt x / L) * L ^ 2 = K₁ * Real.sqrt x * L := by field_simp
    rw [this]
    have : 0 ≤ K₁ * Real.sqrt x := mul_nonneg hK₁ hsx.le
    nlinarith
  have hK₂u : K₂ ≤ u := by
    have h1 : (|K₂| + 1) * L ≤ Real.sqrt x := by
      have := mul_le_mul_of_nonneg_left hlog (by positivity : (0 : ℝ) ≤ |K₂| + 1)
      rw [← mul_assoc, mul_one_div_cancel (by positivity), one_mul] at this
      exact this
    rw [hu, le_div_iff₀ hlx0]
    nlinarith [le_abs_self K₂]
  have hL3' : K₁ + 1 ≤ c / 2 * L3 := by
    rw [div_le_iff₀ (by positivity)] at hL3
    linarith
  have hmain : -(c * L3 * u) + K₁ * u + u ≤ -(c / 2 * L3 * u) := by
    have : (K₁ + 1) * u ≤ c / 2 * L3 * u := mul_le_mul_of_nonneg_right hL3' hu0.le
    linarith
  have hgoal : littlewoodConst / 28 * Real.sqrt x * L3 / L = c / 2 * L3 * u := by
    rw [hu, hc]; field_simp; ring
  rw [hgoal]
  linarith

/-- **Littlewood's theorem: `π(x) - li(x) < -(c/2)√x logloglog x / log x` infinitely often**, with
`c = 1/(70π³)` and `li(x) = ∫_2^x dt/log t`. -/
theorem frequently_primeCounting_lt_logIntegral_sub_littlewood :
    ∃ᶠ x : ℝ in atTop, (Nat.primeCounting ⌊x⌋₊ : ℝ)
      < (∫ t in (2 : ℝ)..x, 1 / Real.log t)
        - littlewoodConst / 28 * Real.sqrt x * Real.log (Real.log (Real.log x)) / Real.log x := by
  by_cases hRH : RiemannHypothesis
  · exact frequently_primeCounting_lt_logIntegral_sub_of_riemannHypothesis hRH
  · have hfr : ∃ᶠ x : ℝ in atTop,
        (Nat.primeCounting ⌊x⌋₊ : ℝ) < (∫ t in (2 : ℝ)..x, 1 / Real.log t) - 1 * Real.sqrt x := by
      by_contra hno
      rw [Filter.not_frequently] at hno
      exact hRH (riemannHypothesis_of_logIntegral_sub_sqrt_le_primeCounting
        (hno.mono fun x hx => not_lt.mp hx))
    have hev : ∀ᶠ x : ℝ in atTop, Real.exp 1 ≤ Real.log x :=
      Real.tendsto_log_atTop.eventually_ge_atTop _
    refine (hfr.and_eventually (hev.and (eventually_gt_atTop (1 : ℝ)))).mono ?_
    rintro x ⟨hx, hlx, hx1⟩
    have hlx0 : 0 < Real.log x := Real.log_pos hx1
    have hL3 := logLogLog_le_log hlx
    have hsx : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
    have hc := littlewoodConst_le_one
    have hc0 := littlewoodConst_pos
    have hle : littlewoodConst / 28 * Real.sqrt x * Real.log (Real.log (Real.log x)) / Real.log x
        ≤ 1 * Real.sqrt x := by
      rw [div_le_iff₀ hlx0]
      have h1 : littlewoodConst / 28 * Real.sqrt x * Real.log (Real.log (Real.log x))
          ≤ littlewoodConst / 28 * Real.sqrt x * Real.log x :=
        mul_le_mul_of_nonneg_left hL3 (by positivity)
      have h2 : littlewoodConst / 28 * Real.sqrt x * Real.log x
          ≤ 1 * Real.sqrt x * Real.log x := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hsx) hlx0.le
        linarith
      linarith
    linarith

/-- **`π - li` changes sign infinitely often (Littlewood 1914)**, with amplitude
`(c/2)√x logloglog x / log x` on both sides, `c = 1/(70π³)`. -/
theorem primeCounting_sub_logIntegral_omega_pm_littlewood :
    (∃ᶠ x : ℝ in atTop, (Nat.primeCounting ⌊x⌋₊ : ℝ)
      < (∫ t in (2 : ℝ)..x, 1 / Real.log t)
        - littlewoodConst / 28 * Real.sqrt x * Real.log (Real.log (Real.log x)) / Real.log x)
    ∧ ∃ᶠ x : ℝ in atTop, (∫ t in (2 : ℝ)..x, 1 / Real.log t)
        + littlewoodConst / 28 * Real.sqrt x * Real.log (Real.log (Real.log x)) / Real.log x
      < (Nat.primeCounting ⌊x⌋₊ : ℝ) :=
  ⟨frequently_primeCounting_lt_logIntegral_sub_littlewood,
    frequently_logIntegral_add_littlewood_lt_primeCounting⟩

end

end RHTower
