import GaloisForLFunctions.SquareRootThreshold.ZetaNearTopZerosAreVisibleAtAPolylogarithmicLag
import GaloisForLFunctions.SquareRootThreshold.OneParameterLagFamilyRecordsAreVisibleAtAnExplicitLag

/-!
# The order of the explicit visibility lags

The Fejér order `k = P + ⌈log₂ Y⌉ + 1`, `Y = 4(160π²/3)^P (2P)! M/q^P`, of the explicit lags obeys, for
`M ≥ 1` and coherence `0 < c ≤ 1`,

`2P² log(P + 1)/log 2 ≤ k ≤ P + 2 + L(M, c, P)/log 2`        (`le_explicitOrder`, `explicitOrder_le`),

`L = log 4 + P log(160π²/3) + 2P log 2P + log M + P log 2(P + 1) + P² log G − P log c`, `G = 20(P + 1)²/c`.
With `P = ⌈80 log(180Γ(a))⌉ ≍ log(1/a)` this gives the two-sided law of the record lag
(`recordLag_two_sided`)

`(104π/(σ log 2)) P² log(P + 1) + w + d(a) ≤ V(a, σ) ≤ (4/σ)(13π(P + 2 + L/log 2) + 4) + w + d(a)`,

with the coherence drift `d(a) = 8w e^{w/2} J_w/H₀(a) = 8w e^{w/2} J_w √(80 log(180Γ(a))/a)`. The drift
is polynomial in `1/a`: `√a · V(a, σ) → ∞` as `a → 0⁺` (`tendsto_sqrt_mul_recordLag`), so
`V(a, σ) ≍ log²(1/a) log log(1/a)/σ + √(log(1/a)/a)`, not the first term alone. The near-top lag is
the record lag at loudness `2η²/e` and depth `δ₀/2` plus an amplitude logarithm
(`oneParamLag_eq_recordLag`), and `η · V₀(w, η, δ₀) → ∞` as `η → 0⁺` (`tendsto_mul_oneParamLag`).
-/

open scoped Real
open Filter Topology

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

open Zeta23 _root_.RHTower

/-- The exponent of the Fejér order: `log Y` for `Y = 4(160π²/3)^P (2P)! M/q^P`, with `(2P)!`
replaced by `(2P)^{2P}`. -/
def explicitOrderLog (M c : ℝ) (P : ℕ) : ℝ :=
  Real.log 4 + P * Real.log (160 * π ^ 2 / 3) + 2 * P * Real.log (2 * P) + Real.log M +
    P * Real.log (2 * (P + 1)) + (P : ℝ) ^ 2 * Real.log (explicitGap c P) - P * Real.log c

private theorem log_explicitOrderArg {M c : ℝ} (hM : 0 < M) (hc : 0 < c) (P : ℕ) :
    Real.log (4 * (160 * π ^ 2 / 3) ^ P * ((2 * P).factorial : ℝ) * M / explicitRatio c P ^ P) =
      Real.log 4 + P * Real.log (160 * π ^ 2 / 3) + Real.log ((2 * P).factorial : ℝ) +
        Real.log M + P * Real.log (2 * (P + 1)) + (P : ℝ) ^ 2 * Real.log (explicitGap c P) -
          P * Real.log c := by
  have hG : 0 < explicitGap c P := by unfold explicitGap; positivity
  have hB : (0 : ℝ) < 2 * (P + 1) := by positivity
  have hA : (0 : ℝ) < 160 * π ^ 2 / 3 := by positivity
  have hF : (0 : ℝ) < ((2 * P).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hq : explicitRatio c P ^ P = c ^ P / ((2 * (P + 1)) ^ P * explicitGap c P ^ (P * P)) := by
    unfold explicitRatio
    rw [div_pow, mul_pow, ← pow_mul]
  rw [hq, div_div_eq_mul_div, Real.log_div (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow, Real.log_pow,
    Real.log_pow]
  push_cast
  ring

/-- **Upper bound for the Fejér order.** For `M ≥ 1` and `0 < c ≤ 1`,
`k ≤ P + 2 + explicitOrderLog M c P / log 2`. -/
theorem explicitOrder_le {M c : ℝ} (hM : 1 ≤ M) (hc0 : 0 < c) (hc1 : c ≤ 1) (P : ℕ) :
    (explicitOrder M c P : ℝ) ≤ P + 2 + explicitOrderLog M c P / Real.log 2 := by
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlog := log_explicitOrderArg (M := M) (by linarith) hc0 P
  have hfac : Real.log ((2 * P).factorial : ℝ) ≤ 2 * P * Real.log (2 * P) := by
    have h := Nat.factorial_le_pow (2 * P)
    have h' : ((2 * P).factorial : ℝ) ≤ ((2 * P : ℕ) : ℝ) ^ (2 * P) := by exact_mod_cast h
    calc Real.log ((2 * P).factorial : ℝ) ≤ Real.log (((2 * P : ℕ) : ℝ) ^ (2 * P)) :=
          Real.log_le_log (by exact_mod_cast Nat.factorial_pos _) h'
      _ = 2 * P * Real.log (2 * P) := by rw [Real.log_pow]; push_cast; ring
  have hle : Real.log (4 * (160 * π ^ 2 / 3) ^ P * ((2 * P).factorial : ℝ) * M /
      explicitRatio c P ^ P) ≤ explicitOrderLog M c P := by
    rw [hlog, explicitOrderLog]; linarith
  unfold explicitOrder
  push_cast
  set x := Real.logb 2 (4 * (160 * π ^ 2 / 3) ^ P * ((2 * P).factorial : ℝ) * M /
    explicitRatio c P ^ P)
  have hx : x ≤ explicitOrderLog M c P / Real.log 2 := by
    simp only [x, Real.logb]
    exact div_le_div_of_nonneg_right hle hl2.le
  have hceil : (⌈x⌉₊ : ℝ) ≤ max x 0 + 1 := by
    rcases le_total 0 x with h | h
    · rw [max_eq_left h]; exact (Nat.ceil_lt_add_one h).le
    · rw [Nat.ceil_eq_zero.mpr h, Nat.cast_zero]
      linarith [le_max_right x 0]
  have hE : 0 ≤ explicitOrderLog M c P / Real.log 2 := by
    refine div_nonneg ?_ hl2.le
    have h4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    have hA : 0 ≤ Real.log (160 * π ^ 2 / 3) :=
      Real.log_nonneg (by nlinarith [Real.pi_gt_three])
    have hP : 0 ≤ 2 * (P : ℝ) * Real.log (2 * P) := by
      rcases Nat.eq_zero_or_pos P with rfl | hP
      · simp
      · exact mul_nonneg (by positivity)
          (Real.log_nonneg (by
            have h1 : (1 : ℝ) ≤ P := by exact_mod_cast hP
            linarith))
    have hM0 : 0 ≤ Real.log M := Real.log_nonneg hM
    have hB : 0 ≤ Real.log (2 * ((P : ℝ) + 1)) := Real.log_nonneg (by
      have : (0 : ℝ) ≤ P := Nat.cast_nonneg _
      linarith)
    have hG : 0 ≤ Real.log (explicitGap c P) := by
      apply Real.log_nonneg; unfold explicitGap
      rw [le_div_iff₀ hc0]; nlinarith [sq_nonneg ((P : ℝ) + 1)]
    have hc : Real.log c ≤ 0 := Real.log_nonpos hc0.le hc1
    unfold explicitOrderLog
    have : 0 ≤ (P : ℝ) * Real.log (160 * π ^ 2 / 3) := mul_nonneg (by positivity) hA
    have : 0 ≤ (P : ℝ) * Real.log (2 * ((P : ℝ) + 1)) := mul_nonneg (by positivity) hB
    have : 0 ≤ (P : ℝ) ^ 2 * Real.log (explicitGap c P) := mul_nonneg (by positivity) hG
    have : (P : ℝ) * Real.log c ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) hc
    linarith
  have : max x 0 ≤ explicitOrderLog M c P / Real.log 2 := max_le hx hE
  linarith

/-- **Lower bound for the Fejér order.** For `M ≥ 1` and `0 < c ≤ 1`,
`k ≥ 2P² log(P + 1)/log 2`: the order is at least quadratic-logarithmic in the zero count. -/
theorem le_explicitOrder {M c : ℝ} (hM : 1 ≤ M) (hc0 : 0 < c) (hc1 : c ≤ 1) (P : ℕ) :
    2 * (P : ℝ) ^ 2 * Real.log (P + 1) / Real.log 2 ≤ explicitOrder M c P := by
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlog := log_explicitOrderArg (M := M) (by linarith) hc0 P
  have hge : 2 * (P : ℝ) ^ 2 * Real.log (P + 1) ≤
      Real.log (4 * (160 * π ^ 2 / 3) ^ P * ((2 * P).factorial : ℝ) * M /
        explicitRatio c P ^ P) := by
    rw [hlog]
    have h4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    have hA : 0 ≤ (P : ℝ) * Real.log (160 * π ^ 2 / 3) :=
      mul_nonneg (by positivity) (Real.log_nonneg (by nlinarith [Real.pi_gt_three]))
    have hF : 0 ≤ Real.log ((2 * P).factorial : ℝ) :=
      Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _))
    have hM0 : 0 ≤ Real.log M := Real.log_nonneg hM
    have hB : 0 ≤ (P : ℝ) * Real.log (2 * ((P : ℝ) + 1)) :=
      mul_nonneg (by positivity) (Real.log_nonneg (by
        have : (0 : ℝ) ≤ P := Nat.cast_nonneg _
        linarith))
    have hc : (P : ℝ) * Real.log c ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) (Real.log_nonpos hc0.le hc1)
    have hG : 2 * Real.log ((P : ℝ) + 1) ≤ Real.log (explicitGap c P) := by
      rw [show 2 * Real.log ((P : ℝ) + 1) = Real.log (((P : ℝ) + 1) ^ 2) by
        rw [Real.log_pow]; push_cast; ring]
      apply Real.log_le_log (by positivity)
      unfold explicitGap
      rw [le_div_iff₀ hc0]; nlinarith [sq_nonneg ((P : ℝ) + 1)]
    have := mul_le_mul_of_nonneg_left hG (sq_nonneg (P : ℝ))
    linarith
  unfold explicitOrder
  push_cast
  have h1 : 2 * (P : ℝ) ^ 2 * Real.log (P + 1) / Real.log 2 ≤ Real.logb 2
      (4 * (160 * π ^ 2 / 3) ^ P * ((2 * P).factorial : ℝ) * M / explicitRatio c P ^ P) :=
    div_le_div_of_nonneg_right hge hl2.le
  have h2 := Nat.le_ceil (Real.logb 2
      (4 * (160 * π ^ 2 / 3) ^ P * ((2 * P).factorial : ℝ) * M / explicitRatio c P ^ P))
  have : (0 : ℝ) ≤ P := Nat.cast_nonneg _
  linarith

/-! ## The record lag -/

theorem recordHeightOf_nonneg (w : ℝ) {a : ℝ} (ha : 0 < a) : 0 ≤ recordHeightOf w a :=
  Real.rpow_nonneg (by positivity) _

theorem one_le_recordNoise (w : ℝ) {a : ℝ} (ha : 0 < a) : 1 ≤ recordNoise w a := by
  have hΓ := recordHeightOf_nonneg w ha
  have hC := xiLineTwoLogDerivConstant_nonneg
  have hl4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have he : 0 < Real.exp 1 - 1 := by linarith [Real.add_one_lt_exp (one_ne_zero : (1 : ℝ) ≠ 0)]
  have h1 : 0 ≤ 4 * (32 * (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 *
      (xiLineTwoLogDerivConstant + Real.log 4)) / ((Real.exp 1 - 1) * a) := by positivity
  have h2 : 1 ≤ Real.log (180 * (recordHeightOf w a + 6)) := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    nlinarith [Real.exp_one_lt_d9]
  unfold recordNoise
  nlinarith

theorem recordCoherence_pos_le_one (w : ℝ) {a : ℝ} (ha : 0 < a) :
    0 < recordCoherence w a ∧ recordCoherence w a ≤ 1 := by
  have hD : 0 ≤ recordMass w a := by
    unfold recordMass
    exact mul_nonneg (by norm_num) (Real.log_nonneg (by nlinarith [recordHeightOf_nonneg w ha]))
  unfold recordCoherence explicitCoherence
  refine ⟨by positivity, (div_le_one (by positivity)).mpr ?_⟩
  have : 0 ≤ 10 * ((explicitCount (recordHeightOf w a) : ℝ) + 1) * recordMass w a := by positivity
  linarith

/-- **Two-sided law for the record lag.** With `P = ⌈80 log(180 Γ(a))⌉` and the drift
`d(a) = 8w e^{w/2} J_w/H₀(a)`,
`(104π/(σ log 2)) P² log(P + 1) + w + d(a) ≤ V(a, σ)
   ≤ (4/σ)(13π(P + 2 + L/log 2) + 4) + w + d(a)`,
`L = explicitOrderLog(M(a), c(a), P)`. -/
theorem recordLag_two_sided {w a σ : ℝ} (ha : 0 < a) (hσ : 0 < σ) :
    104 * π / (σ * Real.log 2) * ((explicitCount (recordHeightOf w a) : ℝ) ^ 2 *
        Real.log (explicitCount (recordHeightOf w a) + 1)) + w +
        8 * w * Real.exp (w / 2) * bumpMass w / recordScale w a ≤ recordLag w a σ ∧
      recordLag w a σ ≤ 4 / σ * (13 * π * (explicitCount (recordHeightOf w a) + 2 +
        explicitOrderLog (recordNoise w a) (recordCoherence w a)
          (explicitCount (recordHeightOf w a)) / Real.log 2) + 4) + w +
        8 * w * Real.exp (w / 2) * bumpMass w / recordScale w a := by
  obtain ⟨hc0, hc1⟩ := recordCoherence_pos_le_one w ha
  have hM := one_le_recordNoise w ha
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlo := le_explicitOrder hM hc0 hc1 (explicitCount (recordHeightOf w a))
  have hhi := explicitOrder_le hM hc0 hc1 (explicitCount (recordHeightOf w a))
  have h4σ : 0 < 4 / σ := by positivity
  unfold recordLag recordOrder
  constructor
  · have h := mul_le_mul_of_nonneg_left hlo (by positivity : (0 : ℝ) ≤ 4 / σ * (13 * π))
    have heq : 4 / σ * (13 * π) * (2 * (explicitCount (recordHeightOf w a) : ℝ) ^ 2 *
        Real.log (explicitCount (recordHeightOf w a) + 1) / Real.log 2) =
        104 * π / (σ * Real.log 2) * ((explicitCount (recordHeightOf w a) : ℝ) ^ 2 *
          Real.log (explicitCount (recordHeightOf w a) + 1)) := by
      field_simp; ring
    nlinarith
  · have h := mul_le_mul_of_nonneg_left hhi (by positivity : (0 : ℝ) ≤ 4 / σ * (13 * π))
    nlinarith

/-- The bump mass `J_w = ∫ |β(u/4w)| du` is positive. -/
theorem bumpMass_pos {w : ℝ} (hw : 0 < w) : 0 < bumpMass w := by
  unfold bumpMass
  have hcont : Continuous fun u : ℝ => |weilBump (u / (4 * w))| :=
    (weilBump.continuous.comp (continuous_id.div_const _)).abs
  have hcs : HasCompactSupport fun u : ℝ => |weilBump (u / (4 * w))| := by
    refine HasCompactSupport.of_support_subset_isCompact
      (isCompact_closedBall (0 : ℝ) (4 * w * weilBump.rOut)) fun u hu => ?_
    have hu' : weilBump (u / (4 * w)) ≠ 0 := fun h => hu (by simp [h])
    have hmem : u / (4 * w) ∈ Function.support weilBump := hu'
    rw [weilBump.support_eq, Metric.mem_ball, dist_zero_right, Real.norm_eq_abs,
      abs_div, abs_of_pos (by positivity : (0 : ℝ) < 4 * w), div_lt_iff₀ (by positivity)] at hmem
    rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs]
    linarith
  refine hcont.integral_pos_of_hasCompactSupport_nonneg_nonzero hcs (fun u => abs_nonneg _)
    (x := 0) ?_
  rw [zero_div, weilBump.one_of_mem_closedBall (Metric.mem_closedBall_self weilBump.rIn_pos.le)]
  norm_num

theorem scaledBumpDecay_pos {w : ℝ} (hw : 0 < w) : 0 < scaledBumpDecay w := by
  have h1 : (∫ u, ‖scaledBump w u‖) = bumpMass w := by
    unfold scaledBump weilBumpC bumpMass
    simp only [Complex.norm_real, Real.norm_eq_abs]
  have h2 : 0 ≤ ∫ u, ‖deriv (deriv (scaledBump w)) u‖ := MeasureTheory.integral_nonneg fun _ => norm_nonneg _
  have h3 := bumpMass_pos hw
  show 0 < 4 * ((∫ u, ‖scaledBump w u‖) + ∫ u, ‖deriv (deriv (scaledBump w)) u‖)
  rw [h1]
  positivity

/-- `log(180 Γ(a)) → ∞` as `a → 0⁺`. -/
theorem tendsto_log_recordHeightOf {w : ℝ} (hw : 0 < w) :
    Tendsto (fun a => Real.log (180 * recordHeightOf w a)) (𝓝[>] 0) atTop := by
  have hK : 0 < 2880 * (80 * (Real.exp (w / 2) * scaledBumpDecay w) ^ 2) := by
    have := scaledBumpDecay_pos hw
    positivity
  have heq : (fun a => recordHeightOf w a) = fun a =>
      ((2880 * (80 * (Real.exp (w / 2) * scaledBumpDecay w) ^ 2)) * a⁻¹) ^ ((1 : ℝ) / 3) := by
    funext a; unfold recordHeightOf; rw [mul_div_assoc', div_eq_mul_inv, mul_assoc]
  have hΓ : Tendsto (fun a => recordHeightOf w a) (𝓝[>] 0) atTop := by
    rw [heq]
    exact (tendsto_rpow_atTop (by norm_num)).comp (tendsto_inv_nhdsGT_zero.const_mul_atTop hK)
  exact Real.tendsto_log_atTop.comp (hΓ.const_mul_atTop (by norm_num))

/-- **The record lag has a polynomial drift.** For `w, σ > 0`, `√a · V(a, σ) → ∞` as `a → 0⁺`:
the coherence drift `8w e^{w/2} J_w/H₀(a) = 8w e^{w/2} J_w √(80 log(180Γ(a))/a)` outgrows every
power of `log(1/a)`, so `V(a, σ)` is not `O(log²(1/a) log log(1/a))` at fixed `σ`. -/
theorem tendsto_sqrt_mul_recordLag {w σ : ℝ} (hw : 0 < w) (hσ : 0 < σ) :
    Tendsto (fun a => Real.sqrt a * recordLag w a σ) (𝓝[>] 0) atTop := by
  set C : ℝ := 8 * w * Real.exp (w / 2) * bumpMass w
  have hCpos : 0 < C := by have := bumpMass_pos hw; positivity
  have hL := tendsto_log_recordHeightOf hw
  have hf : Tendsto (fun a => C * Real.sqrt (80 * Real.log (180 * recordHeightOf w a)))
      (𝓝[>] 0) atTop :=
    (Real.tendsto_sqrt_atTop.comp (hL.const_mul_atTop (by norm_num))).const_mul_atTop hCpos
  refine tendsto_atTop_mono' _ ?_ hf
  filter_upwards [self_mem_nhdsWithin, hL.eventually (eventually_gt_atTop 0)] with a ha hLa
  change 0 < a at ha
  have hlow := (recordLag_two_sided (w := w) ha hσ).1
  have hP : 0 ≤ 104 * π / (σ * Real.log 2) * ((explicitCount (recordHeightOf w a) : ℝ) ^ 2 *
      Real.log (explicitCount (recordHeightOf w a) + 1)) := by
    have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
    have : 0 ≤ Real.log ((explicitCount (recordHeightOf w a) : ℝ) + 1) :=
      Real.log_nonneg (by have : (0 : ℝ) ≤ explicitCount (recordHeightOf w a) := Nat.cast_nonneg _
                          linarith)
    positivity
  have hscale : Real.sqrt a / recordScale w a =
      Real.sqrt (80 * Real.log (180 * recordHeightOf w a)) := by
    unfold recordScale
    rw [← Real.sqrt_div ha.le]
    congr 1
    field_simp
  have hdrift : Real.sqrt a * (C / recordScale w a) =
      C * Real.sqrt (80 * Real.log (180 * recordHeightOf w a)) := by
    rw [← hscale]; ring
  have hsa : 0 ≤ Real.sqrt a := Real.sqrt_nonneg a
  have hrec : C / recordScale w a ≤ recordLag w a σ := by linarith
  calc C * Real.sqrt (80 * Real.log (180 * recordHeightOf w a)) =
        Real.sqrt a * (C / recordScale w a) := hdrift.symm
    _ ≤ Real.sqrt a * recordLag w a σ := mul_le_mul_of_nonneg_left hrec hsa

/-! ## The near-top lag -/

/-- The near-top lag is the record lag at loudness `2η²/e` and depth `δ₀/2`, plus the amplitude
logarithm: `V₀(w, η, δ₀) = V(2η²/e, δ₀/2) + (8/δ₀) |log(80 log(180Γ₀)(e^{w/2}B_w)²/(2η²))|`. -/
theorem oneParamLag_eq_recordLag (w η δ₀ : ℝ) :
    oneParamLag w η δ₀ = recordLag w (2 * η ^ 2 / Real.exp 1) (δ₀ / 2) +
      8 / δ₀ * |Real.log (80 * Real.log (180 * oneParamRecordHeight w η) *
        (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 / (2 * η ^ 2))| := by
  unfold oneParamLag recordLag
  change 8 / δ₀ * (13 * π * (recordOrder w (2 * η ^ 2 / Real.exp 1) : ℝ) + 4 + _) + w +
      8 * w * Real.exp (w / 2) * bumpMass w / recordScale w (2 * η ^ 2 / Real.exp 1) = _
  rw [show (4 : ℝ) / (δ₀ / 2) = 8 / δ₀ by ring]
  ring

/-- **The near-top lag has a polynomial drift.** For `w, δ₀ > 0`, `η · V₀(w, η, δ₀) → ∞` as
`η → 0⁺`: `V₀` is not `O((log Γ₀)² log log Γ₀)` at fixed depth, `Γ₀ ≍ η^{−2/3}`. -/
theorem tendsto_mul_oneParamLag {w δ₀ : ℝ} (hw : 0 < w) (hδ : 0 < δ₀) :
    Tendsto (fun η => η * oneParamLag w η δ₀) (𝓝[>] 0) atTop := by
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  have hmap : Tendsto (fun η : ℝ => 2 * η ^ 2 / Real.exp 1) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have h : Tendsto (fun η : ℝ => 2 * η ^ 2 / Real.exp 1) (𝓝 0) (𝓝 (2 * 0 ^ 2 / Real.exp 1)) :=
        ((continuous_const.mul (continuous_pow 2)).div_const _).tendsto 0
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_div] at h
      exact h.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with η hη
      change 0 < η at hη
      exact show (0 : ℝ) < 2 * η ^ 2 / Real.exp 1 by positivity
  have hrec := (tendsto_sqrt_mul_recordLag hw (by positivity : 0 < δ₀ / 2)).comp hmap
  have hk : 0 < Real.sqrt (Real.exp 1 / 2) := Real.sqrt_pos.mpr (by positivity)
  refine tendsto_atTop_mono' _ ?_ (hrec.const_mul_atTop hk)
  filter_upwards [self_mem_nhdsWithin] with η hη
  change 0 < η at hη
  have hsq : Real.sqrt (Real.exp 1 / 2) * Real.sqrt (2 * η ^ 2 / Real.exp 1) = η := by
    rw [← Real.sqrt_mul (by positivity), show Real.exp 1 / 2 * (2 * η ^ 2 / Real.exp 1) = η ^ 2 by
      field_simp, Real.sqrt_sq hη.le]
  have habs : 0 ≤ 8 / δ₀ * |Real.log (80 * Real.log (180 * oneParamRecordHeight w η) *
      (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 / (2 * η ^ 2))| := by positivity
  simp only [Function.comp_apply]
  rw [oneParamLag_eq_recordLag, ← mul_assoc, hsq]
  nlinarith

end GaloisForLFunctions.SquareRootThreshold
