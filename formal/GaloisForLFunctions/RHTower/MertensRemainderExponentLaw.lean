import GaloisForLFunctions.RHTower.NicolasInequalityRiemannConverse
import GaloisForLFunctions.RHTower.RobinExtremalThresholds

/-!
# The exponent law for the Mertens remainder and the Nicolas defect

Let `Θ = sup_ρ Re ρ`, `G(T) = R(e^T) - (ψ(e^T) - e^T)/(e^T T)` the Mertens remainder and
`Nic(x) = -log ∏_{p ≤ x}(1 - 1/p) - γ - log log θ(x)` the Nicolas defect.

* A one-sided bound `G(T) ≤ B e^{(b-1)T}` (or `≥ -B e^{(b-1)T}`) for all large `T`, `½ ≤ b < 1`,
  forces every zero to have real part `≤ b`: the inversion of `G` into the lag primitive has an
  unconditional tail, and the lag receiver applies at every exponent `a > b - ½`.
* `|G(T)| ≤ C e^{(Θ-1)T}` for all large `T`.
* Hence for `½ ≤ b < Θ`, `G(T) = Ω±(e^{(b-1)T})`, and `Nic(x) = Ω±(x^{b-1})`; the lower side uses
  the minimum of `G(T)e^{(1-b)T}`, where the unsmoothed Chebyshev error is controlled by `G`.
-/

open MeasureTheory Set Filter Topology
open GaloisForLFunctions.RHTower

namespace RHTower

noncomputable section

/-! ## One-sided receivers at exponent `b` -/

/-- **Upper inversion at exponent `b`.**  If `G(s) ≤ B e^{(b-1)s}` for `s ≥ T₀ ≥ 1`, `b < 1`, then
`v(T) ≤ B (T + 1/(1 - b)) e^{(b-1)T}` for `T ≥ T₀`. -/
theorem mertensLagPrimitive_le_of_remainder_le_rpow {B T₀ b : ℝ} (hB : 0 ≤ B) (hT₀ : 1 ≤ T₀)
    (hb : b < 1) (hG : ∀ s, T₀ ≤ s → mertensErrorRemainder s ≤ B * Real.exp ((b - 1) * s))
    {T : ℝ} (hT : T₀ ≤ T) :
    mertensLagPrimitive T ≤ B * (T + 1 / (1 - b)) * Real.exp ((b - 1) * T) := by
  have hT1 : 1 ≤ T := le_trans hT₀ hT
  have hT0 : 0 < T := by linarith
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  obtain ⟨W, hW, hTW⟩ := ((frequently_lag_bracket_lt hε).and_eventually
    (eventually_ge_atTop T)).exists
  have hinv := mertensLagPrimitive_eq_inversion hT1 hTW
  have hE0 : 0 ≤ B * Real.exp ((b - 1) * T) := by positivity
  have hGT : mertensErrorRemainder T * (T ^ 2 / (1 + T)) ≤ B * Real.exp ((b - 1) * T) * T := by
    have hr0 : 0 ≤ T ^ 2 / (1 + T) := by positivity
    have hrT : T ^ 2 / (1 + T) ≤ T := by rw [div_le_iff₀ (by linarith)]; nlinarith
    calc mertensErrorRemainder T * (T ^ 2 / (1 + T))
        ≤ B * Real.exp ((b - 1) * T) * (T ^ 2 / (1 + T)) :=
          mul_le_mul_of_nonneg_right (hG T hT) hr0
      _ ≤ B * Real.exp ((b - 1) * T) * T := mul_le_mul_of_nonneg_left hrT hE0
  have hint : ∫ s in T..W, mertensErrorRemainder s * (s * (s + 2) / (1 + s) ^ 2)
      ≤ B * Real.exp ((b - 1) * T) / (1 - b) := by
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
        ≤ ∫ s in T..W, (0 * Real.exp (-s / 2)
          + B * Real.exp ((2 * ((b + 1) / 2) - 2) * s)) := by
      refine intervalIntegral.integral_mono_on hTW hGqi
        (Continuous.intervalIntegrable (by fun_prop) _ _) fun s hs => ?_
      have hs0 : 0 < s := by linarith [hs.1]
      have hq0 : 0 ≤ s * (s + 2) / (1 + s) ^ 2 := by positivity
      have hq1 : s * (s + 2) / (1 + s) ^ 2 ≤ 1 := by
        rw [div_le_one (by positivity)]; nlinarith
      have hEs : 0 ≤ B * Real.exp ((b - 1) * s) := by positivity
      have e : (2 * ((b + 1) / 2) - 2) * s = (b - 1) * s := by ring
      rw [e, zero_mul, zero_add]
      calc mertensErrorRemainder s * (s * (s + 2) / (1 + s) ^ 2)
          ≤ B * Real.exp ((b - 1) * s) * (s * (s + 2) / (1 + s) ^ 2) :=
            mul_le_mul_of_nonneg_right (hG s (le_trans hT hs.1)) hq0
        _ ≤ B * Real.exp ((b - 1) * s) := mul_le_of_le_one_right hEs hq1
    have h2 := integral_exp_weight_le (c₁ := 0) (c₂ := B) (b := (b + 1) / 2) T W le_rfl hB
      (by linarith)
    have e1 : (2 * ((b + 1) / 2) - 2) * T = (b - 1) * T := by ring
    have e2 : 2 - 2 * ((b + 1) / 2) = 1 - b := by ring
    rw [e1, e2] at h2
    simp only [mul_zero, zero_mul, zero_add] at h2 hmono
    linarith
  have e : B * (T + 1 / (1 - b)) * Real.exp ((b - 1) * T)
      = B * Real.exp ((b - 1) * T) * T + B * Real.exp ((b - 1) * T) / (1 - b) := by
    have : 1 - b ≠ 0 := by linarith
    field_simp
  rw [e]
  linarith

/-- **Lower inversion at exponent `b`.**  If `G(s) ≥ -B e^{(b-1)s}` for `s ≥ T₀ ≥ 1`, `b < 1`, then
`v(T) ≥ -B (T + 1/(1 - b)) e^{(b-1)T}` for `T ≥ T₀`. -/
theorem mertensLagPrimitive_ge_of_remainder_ge_rpow {B T₀ b : ℝ} (hB : 0 ≤ B) (hT₀ : 1 ≤ T₀)
    (hb : b < 1) (hG : ∀ s, T₀ ≤ s → -(B * Real.exp ((b - 1) * s)) ≤ mertensErrorRemainder s)
    {T : ℝ} (hT : T₀ ≤ T) :
    -(B * (T + 1 / (1 - b)) * Real.exp ((b - 1) * T)) ≤ mertensLagPrimitive T := by
  have hT1 : 1 ≤ T := le_trans hT₀ hT
  have hT0 : 0 < T := by linarith
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  obtain ⟨W, hW, hTW⟩ := ((frequently_lag_bracket_gt hε).and_eventually
    (eventually_ge_atTop T)).exists
  have hinv := mertensLagPrimitive_eq_inversion hT1 hTW
  have hE0 : 0 ≤ B * Real.exp ((b - 1) * T) := by positivity
  have hGT : -(B * Real.exp ((b - 1) * T) * T) ≤ mertensErrorRemainder T * (T ^ 2 / (1 + T)) := by
    have hr0 : 0 ≤ T ^ 2 / (1 + T) := by positivity
    have hrT : T ^ 2 / (1 + T) ≤ T := by rw [div_le_iff₀ (by linarith)]; nlinarith
    calc -(B * Real.exp ((b - 1) * T) * T) ≤ -(B * Real.exp ((b - 1) * T)) * (T ^ 2 / (1 + T)) := by
          have := mul_le_mul_of_nonneg_left hrT hE0
          linarith
      _ ≤ mertensErrorRemainder T * (T ^ 2 / (1 + T)) :=
          mul_le_mul_of_nonneg_right (hG T hT) hr0
  have hint : -(B * Real.exp ((b - 1) * T) / (1 - b))
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
    have hmono : ∫ s in T..W, -(0 * Real.exp (-s / 2)
          + B * Real.exp ((2 * ((b + 1) / 2) - 2) * s))
        ≤ ∫ s in T..W, mertensErrorRemainder s * (s * (s + 2) / (1 + s) ^ 2) := by
      refine intervalIntegral.integral_mono_on hTW
        (Continuous.intervalIntegrable (by fun_prop) _ _) hGqi fun s hs => ?_
      have hs0 : 0 < s := by linarith [hs.1]
      have hq0 : 0 ≤ s * (s + 2) / (1 + s) ^ 2 := by positivity
      have hq1 : s * (s + 2) / (1 + s) ^ 2 ≤ 1 := by
        rw [div_le_one (by positivity)]; nlinarith
      have hEs : 0 ≤ B * Real.exp ((b - 1) * s) := by positivity
      have e : (2 * ((b + 1) / 2) - 2) * s = (b - 1) * s := by ring
      rw [e, zero_mul, zero_add]
      calc -(B * Real.exp ((b - 1) * s))
          ≤ -(B * Real.exp ((b - 1) * s)) * (s * (s + 2) / (1 + s) ^ 2) := by nlinarith
        _ ≤ mertensErrorRemainder s * (s * (s + 2) / (1 + s) ^ 2) :=
            mul_le_mul_of_nonneg_right (hG s (le_trans hT hs.1)) hq0
    have h2 := integral_exp_weight_le (c₁ := 0) (c₂ := B) (b := (b + 1) / 2) T W le_rfl hB
      (by linarith)
    rw [intervalIntegral.integral_neg] at hmono
    have e1 : (2 * ((b + 1) / 2) - 2) * T = (b - 1) * T := by ring
    have e2 : 2 - 2 * ((b + 1) / 2) = 1 - b := by ring
    rw [e1, e2] at h2
    simp only [mul_zero, zero_mul, zero_add] at h2 hmono
    linarith
  have e : B * (T + 1 / (1 - b)) * Real.exp ((b - 1) * T)
      = B * Real.exp ((b - 1) * T) * T + B * Real.exp ((b - 1) * T) / (1 - b) := by
    have : 1 - b ≠ 0 := by linarith
    field_simp
  rw [e]
  linarith

/-- `L e^{cL} ≤ e^{aL}/(a - c)` for `c < a`. -/
theorem mul_exp_le_exp_div_sub {a c L : ℝ} (hca : c < a) :
    L * Real.exp (c * L) ≤ Real.exp (a * L) / (a - c) := by
  have hk : 0 < a - c := by linarith
  have h1 : (a - c) * L ≤ Real.exp ((a - c) * L) := by
    have := Real.add_one_le_exp ((a - c) * L); linarith
  rw [le_div_iff₀ hk]
  calc L * Real.exp (c * L) * (a - c) = ((a - c) * L) * Real.exp (c * L) := by ring
    _ ≤ Real.exp ((a - c) * L) * Real.exp (c * L) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = Real.exp (a * L) := by rw [← Real.exp_add]; ring_nf

/-- From `Re ρ ≤ ½ + a` for all `a ∈ (b - ½, ½)` to `Re ρ ≤ b`. -/
theorem re_le_of_forall_re_le_half_add {b : ℝ} (q : XiZeroCopy)
    (h : ∀ a : ℝ, b - 1 / 2 < a → a < 1 / 2 → (q.1 : ℂ).re ≤ 1 / 2 + a) :
    (q.1 : ℂ).re ≤ b := by
  by_contra hc
  push Not at hc
  have hq1 := xiZeroCopy_re_lt_one q
  have := h ((b - 1 / 2 + ((q.1 : ℂ).re - 1 / 2)) / 2) (by linarith) (by linarith)
  linarith

/-- **The upper remainder receiver at exponent `b`.**  If `G(s) ≤ B e^{(b-1)s}` for all large `s`,
`½ ≤ b < 1`, then every zero has real part `≤ b`. -/
theorem re_le_of_remainder_le_rpow {B T₀ b : ℝ} (hB : 0 ≤ B) (hT₀ : 1 ≤ T₀) (hb : 1 / 2 ≤ b)
    (hb1 : b < 1) (hG : ∀ s, T₀ ≤ s → mertensErrorRemainder s ≤ B * Real.exp ((b - 1) * s))
    (q : XiZeroCopy) : (q.1 : ℂ).re ≤ b := by
  refine re_le_of_forall_re_le_half_add q fun a ha ha2 => ?_
  have ha0 : 0 ≤ a := by linarith
  have hκ : 0 < a - (b - 1 / 2) := by linarith
  have hb0 : 0 < 1 - b := by linarith
  set M₁ := B * (1 / (a - (b - 1 / 2)) + 1 / (1 - b)) + 6 with hM₁
  have hM₁0 : 0 ≤ M₁ := by rw [hM₁]; positivity
  set M := max M₁ (Real.exp (T₀ / 2) * lagWeightTotal) with hM
  refine re_le_half_add_of_weilLagFunctionReal_le_exp ha0 ha2 (M := M) (fun L hL => ?_) q
  have heaL : 1 ≤ Real.exp (a * L) := Real.one_le_exp (by positivity)
  have heaL0 := Real.exp_pos (a * L)
  by_cases hLT : T₀ ≤ L
  · have hL0 : 0 < L := by linarith
    have hv := mertensLagPrimitive_le_of_remainder_le_rpow hB hT₀ hb1 hG hLT
    rw [weilLagFunctionReal_eq_lagPrimitive hL0]
    have hEm : Real.exp (-L / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have hEm0 := Real.exp_pos (-L / 2)
    have hprod : Real.exp (L / 2) * Real.exp ((b - 1) * L) = Real.exp ((b - 1 / 2) * L) := by
      rw [← Real.exp_add]; ring_nf
    have h1 : Real.exp (L / 2) * mertensLagPrimitive L
        ≤ B * (L * Real.exp ((b - 1 / 2) * L)) + B / (1 - b) * Real.exp ((b - 1 / 2) * L) := by
      calc Real.exp (L / 2) * mertensLagPrimitive L
          ≤ Real.exp (L / 2) * (B * (L + 1 / (1 - b)) * Real.exp ((b - 1) * L)) :=
            mul_le_mul_of_nonneg_left hv (Real.exp_pos _).le
        _ = B * (L + 1 / (1 - b)) * (Real.exp (L / 2) * Real.exp ((b - 1) * L)) := by ring
        _ = _ := by rw [hprod]; ring
    have h2 := mul_exp_le_exp_div_sub (show b - 1 / 2 < a by linarith) (L := L)
    have h3 : Real.exp ((b - 1 / 2) * L) ≤ Real.exp (a * L) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have h4 : -(Real.log (2 * Real.pi) - trivialZeroSeriesReal (Real.exp L))
        * Real.exp (-L / 2) ≤ 6 := by
      have hS0 := trivialZeroSeriesReal_nonneg (Real.one_le_exp hL0.le)
      have hS1 := trivialZeroSeriesReal_le_one (Real.one_le_exp hL0.le)
      have hl20 : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by linarith [Real.pi_gt_three])
      nlinarith
    have hB1 : 0 ≤ B / (1 - b) := div_nonneg hB hb0.le
    have h5 : B * (L * Real.exp ((b - 1 / 2) * L)) ≤ B * (Real.exp (a * L) / (a - (b - 1 / 2))) :=
      mul_le_mul_of_nonneg_left h2 hB
    have h6 : B / (1 - b) * Real.exp ((b - 1 / 2) * L) ≤ B / (1 - b) * Real.exp (a * L) :=
      mul_le_mul_of_nonneg_left h3 hB1
    have e : M₁ * Real.exp (a * L)
        = B * (Real.exp (a * L) / (a - (b - 1 / 2))) + B / (1 - b) * Real.exp (a * L)
          + 6 * Real.exp (a * L) := by
      rw [hM₁]; field_simp
    have h7 : M₁ * Real.exp (a * L) ≤ M * Real.exp (a * L) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) heaL0.le
    linarith
  · push Not at hLT
    have h1 := abs_weilLagFunctionReal_le L
    rw [abs_of_nonneg hL] at h1
    have h2 : Real.exp (L / 2) ≤ Real.exp (T₀ / 2) := Real.exp_le_exp.mpr (by linarith)
    have h3 := lagWeightTotal_nonneg
    have h4 : Real.exp (L / 2) * lagWeightTotal ≤ Real.exp (T₀ / 2) * lagWeightTotal :=
      mul_le_mul_of_nonneg_right h2 h3
    have hM0 : 0 ≤ M := le_trans hM₁0 (le_max_left _ _)
    have h5 : M ≤ M * Real.exp (a * L) := le_mul_of_one_le_right hM0 heaL
    have h6 := le_max_right M₁ (Real.exp (T₀ / 2) * lagWeightTotal)
    linarith [le_abs_self (weilLagFunctionReal L)]

/-- **The lower remainder receiver at exponent `b`.**  If `G(s) ≥ -B e^{(b-1)s}` for all large
`s`, `½ ≤ b < 1`, then every zero has real part `≤ b`. -/
theorem re_le_of_remainder_ge_rpow {B T₀ b : ℝ} (hB : 0 ≤ B) (hT₀ : 1 ≤ T₀) (hb : 1 / 2 ≤ b)
    (hb1 : b < 1)
    (hG : ∀ s, T₀ ≤ s → -(B * Real.exp ((b - 1) * s)) ≤ mertensErrorRemainder s)
    (q : XiZeroCopy) : (q.1 : ℂ).re ≤ b := by
  refine re_le_of_forall_re_le_half_add q fun a ha ha2 => ?_
  have ha0 : 0 ≤ a := by linarith
  have hκ : 0 < a - (b - 1 / 2) := by linarith
  have hb0 : 0 < 1 - b := by linarith
  set M₁ := B * (1 / (a - (b - 1 / 2)) + 1 / (1 - b)) + 6 with hM₁
  have hM₁0 : 0 ≤ M₁ := by rw [hM₁]; positivity
  set M := max M₁ (Real.exp (T₀ / 2) * lagWeightTotal) with hM
  refine re_le_half_add_of_neg_exp_le_weilLagFunctionReal ha0 ha2 (M := M) (fun L hL => ?_) q
  have heaL : 1 ≤ Real.exp (a * L) := Real.one_le_exp (by positivity)
  have heaL0 := Real.exp_pos (a * L)
  by_cases hLT : T₀ ≤ L
  · have hL0 : 0 < L := by linarith
    have hv := mertensLagPrimitive_ge_of_remainder_ge_rpow hB hT₀ hb1 hG hLT
    rw [weilLagFunctionReal_eq_lagPrimitive hL0]
    have hEm : Real.exp (-L / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have hEm0 := Real.exp_pos (-L / 2)
    have hprod : Real.exp (L / 2) * Real.exp ((b - 1) * L) = Real.exp ((b - 1 / 2) * L) := by
      rw [← Real.exp_add]; ring_nf
    have h1 : -(B * (L * Real.exp ((b - 1 / 2) * L)) + B / (1 - b) * Real.exp ((b - 1 / 2) * L))
        ≤ Real.exp (L / 2) * mertensLagPrimitive L := by
      calc -(B * (L * Real.exp ((b - 1 / 2) * L)) + B / (1 - b) * Real.exp ((b - 1 / 2) * L))
          = Real.exp (L / 2) * (-(B * (L + 1 / (1 - b)) * Real.exp ((b - 1) * L))) := by
            rw [show Real.exp (L / 2) * (-(B * (L + 1 / (1 - b)) * Real.exp ((b - 1) * L)))
              = -(B * (L + 1 / (1 - b)) * (Real.exp (L / 2) * Real.exp ((b - 1) * L))) by ring,
              hprod]
            ring
        _ ≤ Real.exp (L / 2) * mertensLagPrimitive L :=
            mul_le_mul_of_nonneg_left hv (Real.exp_pos _).le
    have h2 := mul_exp_le_exp_div_sub (show b - 1 / 2 < a by linarith) (L := L)
    have h3 : Real.exp ((b - 1 / 2) * L) ≤ Real.exp (a * L) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have h4 : (Real.log (2 * Real.pi) - trivialZeroSeriesReal (Real.exp L))
        * Real.exp (-L / 2) ≤ 6 := by
      have hS0 := trivialZeroSeriesReal_nonneg (Real.one_le_exp hL0.le)
      have hl2 : Real.log (2 * Real.pi) ≤ 6 := by
        have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 * Real.pi by positivity)
        linarith [Real.pi_lt_d2]
      rcases le_or_gt 0 (Real.log (2 * Real.pi) - trivialZeroSeriesReal (Real.exp L)) with h | h
      · nlinarith
      · nlinarith
    have hB1 : 0 ≤ B / (1 - b) := div_nonneg hB hb0.le
    have h5 : B * (L * Real.exp ((b - 1 / 2) * L)) ≤ B * (Real.exp (a * L) / (a - (b - 1 / 2))) :=
      mul_le_mul_of_nonneg_left h2 hB
    have h6 : B / (1 - b) * Real.exp ((b - 1 / 2) * L) ≤ B / (1 - b) * Real.exp (a * L) :=
      mul_le_mul_of_nonneg_left h3 hB1
    have e : M₁ * Real.exp (a * L)
        = B * (Real.exp (a * L) / (a - (b - 1 / 2))) + B / (1 - b) * Real.exp (a * L)
          + 6 * Real.exp (a * L) := by
      rw [hM₁]; field_simp
    have h7 : M₁ * Real.exp (a * L) ≤ M * Real.exp (a * L) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) heaL0.le
    linarith
  · push Not at hLT
    have h1 := abs_weilLagFunctionReal_le L
    rw [abs_of_nonneg hL] at h1
    have h2 : Real.exp (L / 2) ≤ Real.exp (T₀ / 2) := Real.exp_le_exp.mpr (by linarith)
    have h3 := lagWeightTotal_nonneg
    have h4 : Real.exp (L / 2) * lagWeightTotal ≤ Real.exp (T₀ / 2) * lagWeightTotal :=
      mul_le_mul_of_nonneg_right h2 h3
    have hM0 : 0 ≤ M := le_trans hM₁0 (le_max_left _ _)
    have h5 : M ≤ M * Real.exp (a * L) := le_mul_of_one_le_right hM0 heaL
    have h6 := le_max_right M₁ (Real.exp (T₀ / 2) * lagWeightTotal)
    linarith [neg_abs_le (weilLagFunctionReal L)]


/-! ## The exponent law for `G` -/

/-- **`G = O(e^{(Θ-1)T})`.** -/
theorem exists_abs_mertensErrorRemainder_le_exp :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 1 ≤ T →
      |mertensErrorRemainder T| ≤ C * Real.exp ((zeroReSup - 1) * T) := by
  have hΘh := half_le_zeroReSup
  have hΘ1 := zeroReSup_le_one
  have hW := lagWeightTotal_nonneg
  refine ⟨8 * (lagWeightTotal + 2), by positivity, fun T hT => ?_⟩
  have hT0 : 0 < T := by linarith
  set η := (lagWeightTotal + 2) * Real.exp ((zeroReSup - 1) * T) with hη
  have hη0 : 0 < η := by positivity
  have hv : ∀ s, T ≤ s → |mertensLagPrimitive s| ≤ η := by
    intro s hs
    have hs0 : 0 < s := by linarith
    have h1 := abs_mertensLagPrimitive_le_exp_zeroReSup hs0
    have h2 : Real.exp (-s) ≤ Real.exp ((zeroReSup - 1) * s) := Real.exp_le_exp.mpr (by nlinarith)
    have h3 : Real.exp ((zeroReSup - 1) * s) ≤ Real.exp ((zeroReSup - 1) * T) :=
      Real.exp_le_exp.mpr (by nlinarith)
    calc |mertensLagPrimitive s|
        ≤ lagWeightTotal * Real.exp ((zeroReSup - 1) * s) + 2 * Real.exp (-s) := h1
      _ ≤ lagWeightTotal * Real.exp ((zeroReSup - 1) * T)
          + 2 * Real.exp ((zeroReSup - 1) * T) := by
          have := mul_le_mul_of_nonneg_left h3 hW
          nlinarith
      _ = η := by rw [hη]; ring
  have hδ : 0 < η / T := by positivity
  obtain ⟨U₁, hU₁, hTU₁⟩ := ((frequently_mertensErrorRemainder_le hδ).and_eventually
    (eventually_ge_atTop T)).exists
  obtain ⟨U₂, hU₂, hTU₂⟩ := ((frequently_mertensErrorRemainder_ge hδ).and_eventually
    (eventually_ge_atTop T)).exists
  have h1 := abs_mertensErrorRemainder_sub_le_of_lag hη0.le hT hTU₁ hv
  have h2 := abs_mertensErrorRemainder_sub_le_of_lag hη0.le hT hTU₂ hv
  have hb : |mertensErrorRemainder T| ≤ 8 * η / T := by
    have e : 8 * η / T = 7 * η / T + η / T := by ring
    rw [abs_le, e]
    constructor
    · linarith [(abs_le.mp h2).1]
    · linarith [(abs_le.mp h1).2]
  have hTη : 8 * η / T ≤ 8 * η := div_le_self (by positivity) hT
  calc |mertensErrorRemainder T| ≤ 8 * η := hb.trans hTη
    _ = 8 * (lagWeightTotal + 2) * Real.exp ((zeroReSup - 1) * T) := by rw [hη]; ring

/-- **Landau for `G`, upper side.**  For `½ ≤ b < Θ`, `G(T) > e^{(b-1)T}` infinitely often. -/
theorem frequently_exp_lt_mertensErrorRemainder {b : ℝ} (hb : 1 / 2 ≤ b) (hbΘ : b < zeroReSup) :
    ∃ᶠ T : ℝ in atTop, Real.exp ((b - 1) * T) < mertensErrorRemainder T := by
  have hb1 : b < 1 := lt_of_lt_of_le hbΘ zeroReSup_le_one
  by_contra h
  rw [not_frequently] at h
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp h
  have hre : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ b := fun q =>
    re_le_of_remainder_le_rpow (B := 1) (T₀ := max T₀ 1) zero_le_one (le_max_right _ _) hb hb1
      (fun s hs => by
        have := not_lt.mp (hT₀ s (le_trans (le_max_left _ _) hs)); linarith) q
  have := zeroReSup_le_of_forall_re_le hre
  linarith

/-- **Landau for `G`, lower side.**  For `½ ≤ b < Θ`, `G(T) < -e^{(b-1)T}` infinitely often. -/
theorem frequently_mertensErrorRemainder_lt_neg_exp {b : ℝ} (hb : 1 / 2 ≤ b)
    (hbΘ : b < zeroReSup) :
    ∃ᶠ T : ℝ in atTop, mertensErrorRemainder T < -Real.exp ((b - 1) * T) := by
  have hb1 : b < 1 := lt_of_lt_of_le hbΘ zeroReSup_le_one
  by_contra h
  rw [not_frequently] at h
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp h
  have hre : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ b := fun q =>
    re_le_of_remainder_ge_rpow (B := 1) (T₀ := max T₀ 1) zero_le_one (le_max_right _ _) hb hb1
      (fun s hs => by
        have := not_lt.mp (hT₀ s (le_trans (le_max_left _ _) hs)); linarith) q
  have := zeroReSup_le_of_forall_re_le hre
  linarith

/-! ## The exponent law for the Nicolas defect -/

/-- `x^{b-1} = e^{(b-1) log x}`. -/
theorem rpow_sub_one_eq_exp_log {x b : ℝ} (hx : 0 < x) :
    x ^ (b - 1) = Real.exp ((b - 1) * Real.log x) := by
  rw [Real.rpow_def_of_pos hx, mul_comm]

/-- **Nicolas, upper side.**  For `½ ≤ b < Θ`, `Nic(x) > x^{b-1}` for arbitrarily large `x`. -/
theorem frequently_rpow_lt_nicolasDefect {b : ℝ} (hb : 1 / 2 ≤ b) (hbΘ : b < zeroReSup) :
    ∃ᶠ x : ℝ in atTop, x ^ (b - 1) < nicolasDefect x := by
  refine Real.tendsto_exp_atTop.frequently ?_
  have hθ := Real.tendsto_exp_atTop.eventually eventually_two_fifths_le_theta
  refine ((frequently_exp_lt_mertensErrorRemainder hb hbΘ).and_eventually
    (hθ.and (eventually_ge_atTop 4))).mono fun T ⟨hG, hθT, hT⟩ => ?_
  have hx : 4 ≤ Real.exp T := by have := Real.add_one_le_exp T; linarith
  have hθ1 : 1 < Chebyshev.theta (Real.exp T) := by linarith
  have h := nicolasDefect_ge hx hθ1
  rw [Real.log_exp] at h
  have hθs : 0 ≤ Chebyshev.theta (Real.sqrt (Real.exp T)) / (Real.exp T * T) := by
    have := Chebyshev.theta_nonneg (Real.sqrt (Real.exp T))
    have : 0 < Real.exp T * T := mul_pos (Real.exp_pos T) (by linarith)
    positivity
  rw [rpow_sub_one_eq_exp_log (Real.exp_pos T), Real.log_exp]
  linarith

/-- One-sided remainder comparisons at a minimum of `G(T) e^{(1-b)T}`. -/
theorem remainder_comparisons_of_scaled_min_rpow {b T h : ℝ} (hb0 : 0 ≤ b) (hb1 : b < 1)
    (h0 : 0 < h)
    (h12 : h ≤ 1 / 2) (hG : mertensErrorRemainder T < 0)
    (hl : mertensErrorRemainder T * Real.exp ((1 - b) * T)
      ≤ mertensErrorRemainder (T - h) * Real.exp ((1 - b) * (T - h)))
    (hr : mertensErrorRemainder T * Real.exp ((1 - b) * T)
      ≤ mertensErrorRemainder (T + h) * Real.exp ((1 - b) * (T + h))) :
    mertensErrorRemainder T ≤ mertensErrorRemainder (T + h)
      ∧ (1 + 2 * h) * mertensErrorRemainder T ≤ mertensErrorRemainder (T - h) := by
  set G := mertensErrorRemainder T with hGdef
  constructor
  · have hσ : Real.exp ((1 - b) * T) ≤ Real.exp ((1 - b) * (T + h)) :=
      Real.exp_le_exp.mpr (by nlinarith)
    by_contra hc
    push Not at hc
    have h3 := mul_lt_mul_of_pos_right hc (Real.exp_pos ((1 - b) * (T + h)))
    have h4 : G * Real.exp ((1 - b) * (T + h)) ≤ G * Real.exp ((1 - b) * T) :=
      mul_le_mul_of_nonpos_left hσ hG.le
    linarith
  · have hratio : Real.exp ((1 - b) * T)
        = Real.exp ((1 - b) * (T - h)) * Real.exp ((1 - b) * h) := by
      rw [← Real.exp_add]; ring_nf
    have hexph : Real.exp h ≤ 1 + 2 * h := by
      have := exp_sub_one_le_add_two_sq h0 h12
      nlinarith
    have hq : Real.exp ((1 - b) * h) ≤ 1 + 2 * h := by
      have : Real.exp ((1 - b) * h) ≤ Real.exp h := Real.exp_le_exp.mpr (by nlinarith)
      linarith
    have hpos := Real.exp_pos ((1 - b) * (T - h))
    rw [hratio] at hl
    have h5 : G * Real.exp ((1 - b) * h) ≤ mertensErrorRemainder (T - h) := by
      by_contra hc
      push Not at hc
      have h6 := mul_lt_mul_of_pos_right hc hpos
      have e : G * Real.exp ((1 - b) * h) * Real.exp ((1 - b) * (T - h))
          = G * (Real.exp ((1 - b) * (T - h)) * Real.exp ((1 - b) * h)) := by ring
      linarith
    have h6 : (1 + 2 * h) * G ≤ G * Real.exp ((1 - b) * h) := by
      have := mul_le_mul_of_nonpos_left hq hG.le
      linarith
    linarith

/-- The final comparison: a deep remainder at a near-zero of `ψ(x) - x` violates
`Nic(x) ≥ -x^{b-1}`. -/
theorem false_of_nicolas_lower_of_deep_remainder {b T c : ℝ} (hb : 1 / 2 ≤ b) (hT : 8 ≤ T)
    (hcT : c ≤ T)
    (hNb : nicolasDefect (Real.exp T)
      ≤ mertensErrorRemainder T / 2 + c / (Real.sqrt (Real.exp T) * T))
    (hNic : -Real.exp ((b - 1) * T) ≤ nicolasDefect (Real.exp T))
    (hGbig : mertensErrorRemainder T < -4 * Real.exp ((b - 1) * T)) : False := by
  have hT0 : 0 < T := by linarith
  have hsx : 0 < Real.sqrt (Real.exp T) := Real.sqrt_pos.mpr (Real.exp_pos _)
  have hhalf : Real.exp (T / 2) = Real.sqrt (Real.exp T) := Real.exp_half T
  have hEb : Real.exp (-(T / 2)) ≤ Real.exp ((b - 1) * T) := Real.exp_le_exp.mpr (by nlinarith)
  have hsmall : c / (Real.sqrt (Real.exp T) * T) ≤ Real.exp ((b - 1) * T) := by
    rw [div_le_iff₀ (by positivity), ← hhalf]
    have hE1 : Real.exp (-(T / 2)) * Real.exp (T / 2) = 1 := by
      rw [← Real.exp_add]; simp
    calc c ≤ T := hcT
      _ = Real.exp (-(T / 2)) * Real.exp (T / 2) * T := by rw [hE1, one_mul]
      _ ≤ Real.exp ((b - 1) * T) * (Real.exp (T / 2) * T) := by
          have := mul_le_mul_of_nonneg_right hEb (show 0 ≤ Real.exp (T / 2) * T by positivity)
          linarith
  linarith

/-- **Nicolas, lower side.**  For `½ ≤ b < Θ`, `Nic(x) < -x^{b-1}` for arbitrarily large `x`. -/
theorem frequently_nicolasDefect_lt_neg_rpow {b : ℝ} (hb : 1 / 2 ≤ b) (hbΘ : b < zeroReSup) :
    ∃ᶠ x : ℝ in atTop, nicolasDefect x < -x ^ (b - 1) := by
  have hb1 : b < 1 := lt_of_lt_of_le hbΘ zeroReSup_le_one
  by_contra hno
  rw [not_frequently] at hno
  have hNic : ∀ᶠ T : ℝ in atTop, -Real.exp ((b - 1) * T) ≤ nicolasDefect (Real.exp T) := by
    refine (Real.tendsto_exp_atTop.eventually hno).mono fun T hT => ?_
    have := not_lt.mp hT
    rwa [rpow_sub_one_eq_exp_log (Real.exp_pos T), Real.log_exp] at this
  set sb : ℝ → ℝ := fun T => mertensErrorRemainder T * Real.exp ((1 - b) * T) with hsb
  have hsbc : ∀ U, ContinuousOn sb (Icc 1 U) := fun U =>
    (continuousOn_mertensErrorRemainder U).mul (Real.continuous_exp.comp
      (continuous_const.mul continuous_id)).continuousOn
  have hup : ∃ᶠ T : ℝ in atTop, 1 < sb T := by
    refine (frequently_exp_lt_mertensErrorRemainder hb hbΘ).mono fun T hT => ?_
    have he : Real.exp ((b - 1) * T) * Real.exp ((1 - b) * T) = 1 := by
      rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
    have := mul_lt_mul_of_pos_right hT (Real.exp_pos ((1 - b) * T))
    simp only [hsb]; linarith
  set b' := (b + zeroReSup) / 2 with hb'
  have hbb' : b < b' := by rw [hb']; linarith
  have hb'Θ : b' < zeroReSup := by rw [hb']; linarith
  have hdown : ∃ᶠ T : ℝ in atTop, sb T < -4 := by
    have hgrow : ∀ᶠ T : ℝ in atTop, 4 < Real.exp ((b' - b) * T) := by
      have : Tendsto (fun T : ℝ => Real.exp ((b' - b) * T)) atTop atTop :=
        Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (by linarith))
      exact this.eventually (eventually_gt_atTop 4)
    refine ((frequently_mertensErrorRemainder_lt_neg_exp (by linarith) hb'Θ).and_eventually
      hgrow).mono fun T ⟨hT, hg⟩ => ?_
    have he : Real.exp ((b' - 1) * T) * Real.exp ((1 - b) * T) = Real.exp ((b' - b) * T) := by
      rw [← Real.exp_add]; ring_nf
    have := mul_lt_mul_of_pos_right hT (Real.exp_pos ((1 - b) * T))
    simp only [hsb]
    nlinarith
  obtain ⟨C₀, hC₀⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  set C := max C₀ 0 with hCdef
  have hC : ∀ x, Chebyshev.psi x - Chebyshev.theta x ≤ C * Real.sqrt x := fun x =>
    (hC₀ x).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg x))
  have hev : ∀ᶠ T : ℝ in atTop, 8 ≤ T ∧ 2 / 5 * Real.exp T ≤ Chebyshev.theta (Real.exp T)
      ∧ -Real.exp ((b - 1) * T) ≤ nicolasDefect (Real.exp T)
      ∧ |mertensErrorRemainder T| * T ≤ 1 / 280
      ∧ (140 + 18 * C ^ 2) ^ 2 ≤ Real.exp T ∧ 8 * Real.log 4 + C + 1 ≤ T := by
    filter_upwards [eventually_ge_atTop (8 : ℝ),
      Real.tendsto_exp_atTop.eventually eventually_two_fifths_le_theta, hNic,
      eventually_abs_mertensErrorRemainder_mul_le (show (0 : ℝ) < 1 / 280 by norm_num),
      Real.tendsto_exp_atTop.eventually (eventually_ge_atTop ((140 + 18 * C ^ 2) ^ 2)),
      eventually_ge_atTop (8 * Real.log 4 + C + 1)]
      with T h1 h2 h3 h4 h5 h6
    exact ⟨h1, h2, h3, h4, h5, h6⟩
  obtain ⟨Ta, hTa⟩ := eventually_atTop.mp hev
  obtain ⟨T₁, hs₁, hT₁⟩ := (hup.and_eventually (eventually_ge_atTop Ta)).exists
  obtain ⟨Tst, hsst, hTst⟩ := (hdown.and_eventually (eventually_ge_atTop T₁)).exists
  obtain ⟨T₂, hs₂, hT₂⟩ := (hup.and_eventually (eventually_ge_atTop Tst)).exists
  have hT₁8 : 8 ≤ T₁ := (hTa T₁ hT₁).1
  have hcont : ContinuousOn sb (Icc T₁ T₂) := (hsbc T₂).mono (Icc_subset_Icc_left (by linarith))
  obtain ⟨Tm, hTm, hmin⟩ := isCompact_Icc.exists_isMinOn ⟨T₁, ⟨le_rfl, le_trans hTst hT₂⟩⟩ hcont
  have hsm : sb Tm < -4 := lt_of_le_of_lt (hmin ⟨hTst, hT₂⟩) hsst
  have hTm1 : T₁ < Tm := by
    rcases eq_or_lt_of_le hTm.1 with h | h
    · rw [← h] at hsm; linarith
    · exact h
  have hTm2 : Tm < T₂ := by
    rcases eq_or_lt_of_le hTm.2 with h | h
    · rw [h] at hsm; linarith
    · exact h
  obtain ⟨hTm8, hθ25, hNicm, hTG, hbig, hTlarge⟩ := hTa Tm (by linarith)
  have hG : mertensErrorRemainder Tm < 0 := by
    simp only [hsb] at hsm
    by_contra hc
    push Not at hc
    have : 0 ≤ mertensErrorRemainder Tm * Real.exp ((1 - b) * Tm) := by positivity
    linarith
  set h := min (min (1 / 2) (Tm - T₁)) (min (T₂ - Tm) (Real.exp (-Tm) / 2)) with hhdef
  have hEm : Real.exp (-Tm) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have h0 : 0 < h := by
    have := Real.exp_pos (-Tm)
    simp only [hhdef, lt_min_iff]
    exact ⟨⟨by norm_num, by linarith⟩, by linarith, by positivity⟩
  have h12 : h ≤ 1 / 2 := le_trans (min_le_left _ _) (min_le_left _ _)
  have hhl : h ≤ Tm - T₁ := le_trans (min_le_left _ _) (min_le_right _ _)
  have hhr : h ≤ T₂ - Tm := le_trans (min_le_right _ _) (min_le_left _ _)
  have hhe : h ≤ Real.exp (-Tm) / 2 := le_trans (min_le_right _ _) (min_le_right _ _)
  have hx1 : Real.exp Tm * (Real.exp h - 1) ≤ 1 := by
    have hexph : Real.exp h - 1 ≤ 2 * h := by
      have := exp_sub_one_le_add_two_sq h0 h12
      nlinarith
    have hE : Real.exp Tm * Real.exp (-Tm) = 1 := by rw [← Real.exp_add]; simp
    calc Real.exp Tm * (Real.exp h - 1) ≤ Real.exp Tm * (2 * h) :=
          mul_le_mul_of_nonneg_left hexph (Real.exp_pos _).le
      _ ≤ Real.exp Tm * Real.exp (-Tm) :=
          mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le
      _ = 1 := hE
  have hl := hmin ⟨by linarith, by linarith⟩ (a := Tm - h)
  have hr := hmin ⟨by linarith, by linarith⟩ (a := Tm + h)
  simp only [hsb] at hl hr
  obtain ⟨hGr, hGl⟩ := remainder_comparisons_of_scaled_min_rpow (by linarith) hb1 h0 h12 hG hl hr
  have hψ := abs_psi_sub_le_of_remainder_comparison (by linarith) h0 (by linarith) hx1 hG hGr hGl
  have hNb := nicolasDefect_le_half_remainder hTm8 hθ25 (hC _) hG hTG hψ hbig
  have hGbig : mertensErrorRemainder Tm < -4 * Real.exp ((b - 1) * Tm) := by
    simp only [hsb] at hsm
    have he : Real.exp ((1 - b) * Tm) * Real.exp ((b - 1) * Tm) = 1 := by
      rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
    have := mul_lt_mul_of_pos_right hsm (Real.exp_pos ((b - 1) * Tm))
    nlinarith
  exact false_of_nicolas_lower_of_deep_remainder hb hTm8 hTlarge hNb hNicm hGbig


/-- The second-order term above `Θ`: if `|ψ(x) - x| ≤ C₁ x^{b'}`, `ψ(x) - θ(x) ≤ C √x`,
`2b' - 2 ≤ b - 1`, `0 ≤ b`, `log x ≥ 1`, then
`(θ(x) - x)²/(x² log x) ≤ (2C₁² + 2C²) x^{b-1}`. -/
theorem theta_sub_sq_div_le_rpow {x b b' C₁ C : ℝ} (hx : 1 ≤ x) (hlx : 1 ≤ Real.log x)
    (hb0 : 0 ≤ b) (hbb : 2 * b' - 2 ≤ b - 1)
    (hψ : |Chebyshev.psi x - x| ≤ C₁ * x ^ b')
    (hC : Chebyshev.psi x - Chebyshev.theta x ≤ C * Real.sqrt x) :
    (Chebyshev.theta x - x) ^ 2 / (x ^ 2 * Real.log x)
      ≤ (2 * C₁ ^ 2 + 2 * C ^ 2) * x ^ (b - 1) := by
  have hx0 : 0 < x := by linarith
  have hψθ0 : 0 ≤ Chebyshev.psi x - Chebyshev.theta x := by
    linarith [Chebyshev.theta_le_psi x]
  have hCs : 0 ≤ C * Real.sqrt x := le_trans hψθ0 hC
  have hψθ2 : (Chebyshev.psi x - Chebyshev.theta x) ^ 2 ≤ C ^ 2 * x := by
    have h1 := pow_le_pow_left₀ hψθ0 hC 2
    rwa [mul_pow, Real.sq_sqrt hx0.le] at h1
  have hpow : (x ^ b') ^ 2 = x ^ (2 * b') := by
    rw [← Real.rpow_two, ← Real.rpow_mul hx0.le, mul_comm]
  have hψx2 : (Chebyshev.psi x - x) ^ 2 ≤ C₁ ^ 2 * x ^ (2 * b') := by
    have h1 := pow_le_pow_left₀ (abs_nonneg _) hψ 2
    rw [sq_abs, mul_pow, hpow] at h1
    exact h1
  have hθx2 : (Chebyshev.theta x - x) ^ 2 ≤ 2 * C₁ ^ 2 * x ^ (2 * b') + 2 * C ^ 2 * x := by
    have e : Chebyshev.theta x - x
        = (Chebyshev.psi x - x) - (Chebyshev.psi x - Chebyshev.theta x) := by ring
    rw [e]
    have := sq_nonneg ((Chebyshev.psi x - x) + (Chebyshev.psi x - Chebyshev.theta x))
    nlinarith
  have hp1 : x ^ (2 * b') / x ^ 2 ≤ x ^ (b - 1) := by
    rw [← Real.rpow_natCast x 2, ← Real.rpow_sub hx0]
    exact Real.rpow_le_rpow_of_exponent_le hx (by push_cast; linarith)
  have hp2 : x / x ^ 2 ≤ x ^ (b - 1) := by
    have e : x / x ^ 2 = x ^ (-(1 : ℝ)) := by
      rw [Real.rpow_neg_one]; field_simp
    rw [e]
    exact Real.rpow_le_rpow_of_exponent_le hx (by linarith)
  have hx2 : 0 < x ^ 2 * Real.log x := by positivity
  have h3 : 0 ≤ 2 * C₁ ^ 2 * x ^ (2 * b') + 2 * C ^ 2 * x := by positivity
  have h1 : (Chebyshev.theta x - x) ^ 2 / (x ^ 2 * Real.log x)
      ≤ (2 * C₁ ^ 2 * x ^ (2 * b') + 2 * C ^ 2 * x) / x ^ 2 := by
    rw [div_le_div_iff₀ hx2 (by positivity)]
    calc (Chebyshev.theta x - x) ^ 2 * x ^ 2
        ≤ (2 * C₁ ^ 2 * x ^ (2 * b') + 2 * C ^ 2 * x) * x ^ 2 :=
          mul_le_mul_of_nonneg_right hθx2 (by positivity)
      _ = (2 * C₁ ^ 2 * x ^ (2 * b') + 2 * C ^ 2 * x) * (x ^ 2 * 1) := by ring
      _ ≤ (2 * C₁ ^ 2 * x ^ (2 * b') + 2 * C ^ 2 * x) * (x ^ 2 * Real.log x) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlx (by positivity)) h3
  have e : (2 * C₁ ^ 2 * x ^ (2 * b') + 2 * C ^ 2 * x) / x ^ 2
      = 2 * C₁ ^ 2 * (x ^ (2 * b') / x ^ 2) + 2 * C ^ 2 * (x / x ^ 2) := by ring
  rw [e] at h1
  have h4 := mul_le_mul_of_nonneg_left hp1 (show 0 ≤ 2 * C₁ ^ 2 by positivity)
  have h5 := mul_le_mul_of_nonneg_left hp2 (show 0 ≤ 2 * C ^ 2 by positivity)
  linarith

/-- `1/(√x log x) ≤ x^{b-1}` for `b ≥ ½`, `x ≥ 1`, `log x ≥ 1`. -/
theorem one_div_sqrt_mul_log_le_rpow {x b : ℝ} (hx : 1 ≤ x) (hlx : 1 ≤ Real.log x)
    (hb : 1 / 2 ≤ b) : 1 / (Real.sqrt x * Real.log x) ≤ x ^ (b - 1) := by
  have hx0 : 0 < x := by linarith
  have h2 : x ^ (-(1 / 2 : ℝ)) ≤ x ^ (b - 1) := Real.rpow_le_rpow_of_exponent_le hx (by linarith)
  have h3 : 1 / (Real.sqrt x * Real.log x) ≤ x ^ (-(1 / 2 : ℝ)) := by
    rw [Real.rpow_neg hx0.le, ← Real.sqrt_eq_rpow, one_div]
    exact inv_anti₀ (Real.sqrt_pos.mpr hx0) (le_mul_of_one_le_right (Real.sqrt_nonneg _) hlx)
  linarith

/-- **Nicolas, size above `Θ`.**  For `b > Θ`, `|Nic(x)| ≤ C x^{b-1}` for all large `x`. -/
theorem exists_abs_nicolasDefect_le_rpow {b : ℝ} (hb : zeroReSup < b) :
    ∃ C : ℝ, ∀ᶠ x : ℝ in atTop, |nicolasDefect x| ≤ C * x ^ (b - 1) := by
  have hΘh := half_le_zeroReSup
  have hΘ1 := zeroReSup_le_one
  obtain ⟨C₂, hC₂0, hC₂⟩ := exists_abs_mertensErrorRemainder_le_exp
  set b' := (zeroReSup + b) / 2 with hb'
  obtain ⟨C₁, hC₁0, hC₁⟩ := exists_abs_chebyshevPsi_sub_le_rpow (b := b') (by rw [hb']; linarith)
  obtain ⟨C₀, hC₀⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  set C := max C₀ 0 with hCdef
  have hC0 : 0 ≤ C := le_max_right _ _
  have hC : ∀ x, Chebyshev.psi x - Chebyshev.theta x ≤ C * Real.sqrt x := fun x =>
    (hC₀ x).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg x))
  have hl4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  refine ⟨C₂ + (8 * Real.log 4 + C) + 35 / 4 * (2 * C₁ ^ 2 + 2 * C ^ 2), ?_⟩
  filter_upwards [eventually_ge_atTop (16 : ℝ), eventually_two_fifths_le_theta] with x hx hθ
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hlx : 1 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le hx0]; have := Real.exp_one_lt_d9; linarith
  have hθ1 : 1 < Chebyshev.theta x := by linarith
  have hlθ1 : 1 ≤ Real.log (Chebyshev.theta x) := by
    rw [Real.le_log_iff_exp_le (by linarith)]; have := Real.exp_one_lt_d9; linarith
  have hup := nicolasDefect_le (by linarith) hθ hlθ1 (hC x)
  have hlow := nicolasDefect_ge (by linarith) hθ1
  have hθs : 0 ≤ Chebyshev.theta (Real.sqrt x) / (x * Real.log x) := by
    have := Chebyshev.theta_nonneg (Real.sqrt x)
    have : 0 < x * Real.log x := by positivity
    positivity
  have hxb : 0 < x ^ (b - 1) := Real.rpow_pos_of_pos hx0 _
  have hG : |mertensErrorRemainder (Real.log x)| ≤ C₂ * x ^ (b - 1) := by
    have h1 := hC₂ (Real.log x) hlx
    have h2 : Real.exp ((zeroReSup - 1) * Real.log x) ≤ x ^ (b - 1) := by
      rw [rpow_sub_one_eq_exp_log hx0]
      exact Real.exp_le_exp.mpr (by nlinarith)
    exact h1.trans (mul_le_mul_of_nonneg_left h2 hC₂0)
  have hsq : (8 * Real.log 4 + C) / (Real.sqrt x * Real.log x)
      ≤ (8 * Real.log 4 + C) * x ^ (b - 1) := by
    have h1 := one_div_sqrt_mul_log_le_rpow hx1 hlx (by linarith : 1 / 2 ≤ b)
    calc (8 * Real.log 4 + C) / (Real.sqrt x * Real.log x)
        = (8 * Real.log 4 + C) * (1 / (Real.sqrt x * Real.log x)) := by ring
      _ ≤ (8 * Real.log 4 + C) * x ^ (b - 1) := mul_le_mul_of_nonneg_left h1 (by positivity)
  have hsec0 := theta_sub_sq_div_le_rpow (b := b) (b' := b') hx1 hlx (by linarith)
    (by rw [hb']; linarith) (hC₁ x hx1) (hC x)
  have hsec : 35 / 4 * ((Chebyshev.theta x - x) ^ 2 / (x ^ 2 * Real.log x))
      ≤ 35 / 4 * (2 * C₁ ^ 2 + 2 * C ^ 2) * x ^ (b - 1) := by
    have := mul_le_mul_of_nonneg_left hsec0 (show (0 : ℝ) ≤ 35 / 4 by norm_num)
    linarith
  have hG1 := (abs_le.mp hG).1
  have hG2 := (abs_le.mp hG).2
  have hp1 : 0 ≤ (8 * Real.log 4 + C) * x ^ (b - 1) := by positivity
  have hp2 : 0 ≤ 35 / 4 * (2 * C₁ ^ 2 + 2 * C ^ 2) * x ^ (b - 1) := by positivity
  have e : (C₂ + (8 * Real.log 4 + C) + 35 / 4 * (2 * C₁ ^ 2 + 2 * C ^ 2)) * x ^ (b - 1)
      = C₂ * x ^ (b - 1) + (8 * Real.log 4 + C) * x ^ (b - 1)
        + 35 / 4 * (2 * C₁ ^ 2 + 2 * C ^ 2) * x ^ (b - 1) := by ring
  rw [abs_le, e]
  constructor
  · linarith only [hlow, hθs, hG1, hp1, hp2]
  · linarith only [hup, hG2, hsq, hsec]

/-- **The exponent law for the Nicolas defect.**  For `b > Θ`, `Nic(x) = O(x^{b-1})`; for
`½ ≤ b < Θ`, `Nic(x) > x^{b-1}` and `Nic(x) < -x^{b-1}` for arbitrarily large `x`. -/
theorem nicolasDefect_exponent_law :
    (∀ b : ℝ, zeroReSup < b → ∃ C : ℝ, ∀ᶠ x : ℝ in atTop, |nicolasDefect x| ≤ C * x ^ (b - 1))
      ∧ ∀ b : ℝ, 1 / 2 ≤ b → b < zeroReSup →
        (∃ᶠ x : ℝ in atTop, x ^ (b - 1) < nicolasDefect x)
          ∧ ∃ᶠ x : ℝ in atTop, nicolasDefect x < -x ^ (b - 1) :=
  ⟨fun _ hb => exists_abs_nicolasDefect_le_rpow hb, fun _ hb hbΘ =>
    ⟨frequently_rpow_lt_nicolasDefect hb hbΘ, frequently_nicolasDefect_lt_neg_rpow hb hbΘ⟩⟩

end

end RHTower
