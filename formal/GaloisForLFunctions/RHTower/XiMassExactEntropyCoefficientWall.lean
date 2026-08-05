import GaloisForLFunctions.RHTower.XiMassEntropyScaleZeroFreeMarginBudget

/-!
# Exact entropy-coefficient wall for the Xi mass budget

At residual fraction `q * log(3A+9)^10 / A`, zero-count entropy and zero-free phase decay
occupy the same logarithmic scale.  This module proves the exact phase transition of the absolute
widened-corona envelope: it vanishes above coefficient one and diverges at or below coefficient
one.  Above the wall, the complete literal Euler/Gamma source vanishes along an explicit genuinely
subcritical frequency tending to infinity.
-/

open Complex Metric Set Filter
open scoped BigOperators Topology

namespace RHTower

noncomputable section

/-- Entropy-critical residual fraction with explicit coefficient `q`. -/
def xiMassEntropyCriticalResidualFraction (q A : ℝ) : ℝ :=
  q * (Real.log (3 * A + 9) ^ (10 : ℕ) / A)

/-- Every fixed entropy-critical residual coefficient still gives a vanishing fraction. -/
theorem tendsto_xiMassEntropyCriticalResidualFraction_zero (q : ℝ) :
    Tendsto (xiMassEntropyCriticalResidualFraction q) atTop (𝓝 0) := by
  have hscale : Tendsto (fun A : ℝ => (3 / 2) * A) atTop atTop :=
    tendsto_id.const_mul_atTop (by norm_num)
  have hraw := (tendsto_pow_log_two_mul_add_nine_div_id 10).comp hscale
  have hbase : Tendsto (fun A : ℝ =>
      Real.log (3 * A + 9) ^ (10 : ℕ) / A) atTop (𝓝 0) := by
    have hmul : Tendsto (fun A : ℝ => (3 / 2 : ℝ) *
        (Real.log (2 * ((3 / 2) * A) + 9) ^ (10 : ℕ) / ((3 / 2) * A)))
        atTop (𝓝 0) := by
      simpa only [Function.comp_apply, mul_zero] using
        Filter.Tendsto.const_mul (3 / 2 : ℝ) hraw
    apply hmul.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with A hA
    rw [show 2 * ((3 / 2 : ℝ) * A) + 9 = 3 * A + 9 by ring]
    field_simp
  unfold xiMassEntropyCriticalResidualFraction
  simpa only [mul_zero] using Filter.Tendsto.const_mul q hbase

/-- Exact entropy-critical widened-corona envelope after `B=3A/2`. -/
def xiMassExactEntropyScaledEnvelope (σ q B : ℝ) : ℝ :=
  xiZeroCountEnvelopeConstant * (2 * B + 3) * Real.log (2 * B + 4) *
    Real.exp (-(3 * σ * q * xiWardZeroFreeMarginC / 13) *
      Real.log (2 * B + 9))

/-- Above coefficient one, exponential phase decay beats exact linear-log corona entropy. -/
theorem tendsto_xiMassExactEntropyScaledEnvelope_zero
    {σ q : ℝ} (hwall : 1 < 3 * σ * q * xiWardZeroFreeMarginC / 13) :
    Tendsto (xiMassExactEntropyScaledEnvelope σ q) atTop (𝓝 0) := by
  let C : ℝ := xiZeroCountEnvelopeConstant
  let D : ℝ := C + 1
  let α : ℝ := 3 * σ * q * xiWardZeroFreeMarginC / 13
  let β : ℝ := α - 1
  have hC : 0 < C := by dsimp only [C]; exact xiZeroCountEnvelopeConstant_pos
  have hD : 0 < D := by dsimp only [D]; linarith
  have hα : 1 < α := by simpa only [α] using hwall
  have hβ : 0 < β := by dsimp only [β]; linarith
  have hβ0 : β ≠ 0 := hβ.ne'
  have haff : Tendsto (fun B : ℝ => 2 * B + 9) atTop atTop :=
    tendsto_atTop_add_const_right atTop 9
      (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2))
  have hLtop : Tendsto (fun B : ℝ => Real.log (2 * B + 9)) atTop atTop :=
    Real.tendsto_log_atTop.comp haff
  have hβLtop : Tendsto (fun B : ℝ => β * Real.log (2 * B + 9)) atTop atTop :=
    hLtop.const_mul_atTop hβ
  have hraw := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hβLtop
  have hdecay : Tendsto (fun B : ℝ =>
      D * Real.log (2 * B + 9) *
        Real.exp (-β * Real.log (2 * B + 9))) atTop (𝓝 0) := by
    have hmul := Filter.Tendsto.const_mul (D / β) hraw
    have hmul' : Tendsto (fun B : ℝ =>
        (D / β) * ((β * Real.log (2 * B + 9)) *
          Real.exp (-(β * Real.log (2 * B + 9))))) atTop (𝓝 0) := by
      simpa only [Function.comp_apply, pow_one, mul_zero] using hmul
    convert hmul' using 1
    · funext B
      field_simp [hβ0]
  apply squeeze_zero'
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with B hB
    unfold xiMassExactEntropyScaledEnvelope
    have hlog : 0 ≤ Real.log (2 * B + 4) := Real.log_nonneg (by linarith)
    positivity
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with B hB
    let x : ℝ := 2 * B + 9
    let y : ℝ := 2 * B + 4
    let L : ℝ := Real.log x
    have hx : 0 < x := by dsimp only [x]; linarith
    have hy : 0 < y := by dsimp only [y]; linarith
    have hL0 : 0 ≤ L := by
      dsimp only [L]
      exact Real.log_nonneg (by dsimp only [x]; linarith)
    have hCD : C ≤ D := by dsimp only [D]; linarith
    have hfac0 : 0 ≤ 2 * B + 3 := by linarith
    have hfac : 2 * B + 3 ≤ x := by dsimp only [x]; linarith
    have hlogy0 : 0 ≤ Real.log y := Real.log_nonneg (by dsimp only [y]; linarith)
    have hlogyx : Real.log y ≤ L := by
      dsimp only [L]
      exact Real.log_le_log hy (by dsimp only [x, y]; linarith)
    have hP :
        C * (2 * B + 3) * Real.log y * Real.exp (-α * L) ≤
          D * x * L * Real.exp (-α * L) := by
      gcongr
    have hxexp : Real.exp L = x := by
      dsimp only [L]
      exact Real.exp_log hx
    have hcombine : D * x * L * Real.exp (-α * L) =
        D * L * Real.exp (-β * L) := by
      rw [← hxexp]
      rw [show D * Real.exp L * L * Real.exp (-α * L) =
          D * L * (Real.exp L * Real.exp (-α * L)) by ring]
      rw [← Real.exp_add]
      congr 2
      dsimp only [β]
      ring
    unfold xiMassExactEntropyScaledEnvelope
    change C * (2 * B + 3) * Real.log y * Real.exp (-α * L) ≤
      D * L * Real.exp (-β * L)
    exact hP.trans_eq hcombine
  · exact hdecay

/-- At and below coefficient one, the same absolute envelope diverges.  This classifies the
absolute-value method; it does not assert divergence of the oscillatory prime source. -/
theorem tendsto_xiMassExactEntropyScaledEnvelope_atTop
    {σ q : ℝ} (hwall : 3 * σ * q * xiWardZeroFreeMarginC / 13 ≤ 1) :
    Tendsto (xiMassExactEntropyScaledEnvelope σ q) atTop atTop := by
  let C : ℝ := xiZeroCountEnvelopeConstant
  let α : ℝ := 3 * σ * q * xiWardZeroFreeMarginC / 13
  have hC : 0 < C := by dsimp only [C]; exact xiZeroCountEnvelopeConstant_pos
  have hα : α ≤ 1 := by simpa only [α] using hwall
  have haff : Tendsto (fun B : ℝ => 2 * B + 4) atTop atTop :=
    tendsto_atTop_add_const_right atTop 4
      (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2))
  have hlogtop : Tendsto (fun B : ℝ => Real.log (2 * B + 4)) atTop atTop :=
    Real.tendsto_log_atTop.comp haff
  have hlowerTop : Tendsto (fun B : ℝ => (C / 2) * Real.log (2 * B + 4))
      atTop atTop := hlogtop.const_mul_atTop (by positivity)
  refine tendsto_atTop_mono' atTop ?_ hlowerTop
  filter_upwards [eventually_ge_atTop (3 / 2 : ℝ)] with B hB
  let x : ℝ := 2 * B + 9
  let y : ℝ := 2 * B + 4
  let L : ℝ := Real.log x
  have hx : 0 < x := by dsimp only [x]; linarith
  have hy1 : 1 ≤ y := by dsimp only [y]; linarith
  have hL0 : 0 ≤ L := by
    dsimp only [L]
    exact Real.log_nonneg (by dsimp only [x]; linarith)
  have hfac : x / 2 ≤ 2 * B + 3 := by dsimp only [x]; linarith
  have hlog0 : 0 ≤ Real.log y := Real.log_nonneg hy1
  have hexpOne : 1 ≤ Real.exp ((1 - α) * L) := by
    calc
      1 = Real.exp 0 := Real.exp_zero.symm
      _ ≤ Real.exp ((1 - α) * L) :=
        Real.exp_le_exp.mpr (mul_nonneg (sub_nonneg.mpr hα) hL0)
  have hxexp : Real.exp L = x := by
    dsimp only [L]
    exact Real.exp_log hx
  have hcombine : x * Real.exp (-α * L) = Real.exp ((1 - α) * L) := by
    rw [← hxexp, ← Real.exp_add]
    congr 1
    ring
  have hfirst :
      C * (x / 2) * Real.log y * Real.exp (-α * L) ≤
        C * (2 * B + 3) * Real.log y * Real.exp (-α * L) := by
    gcongr
  have hsecond : C / 2 * Real.log y ≤
      C * (x / 2) * Real.log y * Real.exp (-α * L) := by
    calc
      C / 2 * Real.log y = C / 2 * Real.log y * 1 := by ring
      _ ≤ C / 2 * Real.log y * Real.exp ((1 - α) * L) := by gcongr
      _ = C * (x / 2) * Real.log y * Real.exp (-α * L) := by
        rw [← hcombine]
        ring
  unfold xiMassExactEntropyScaledEnvelope
  change C / 2 * Real.log y ≤
    C * (2 * B + 3) * Real.log y * Real.exp (-α * L)
  exact hsecond.trans hfirst

/-- Spent fraction at exact entropy-critical residual scale. -/
def xiMassExactEntropyBudgetFraction (q A : ℝ) : ℝ :=
  1 - xiMassEntropyCriticalResidualFraction q A

theorem eventually_xiMassExactEntropyBudgetFraction_pos_lt_one
    {q : ℝ} (hq : 0 < q) :
    ∀ᶠ A : ℝ in atTop,
      0 < xiMassExactEntropyBudgetFraction q A ∧
        xiMassExactEntropyBudgetFraction q A < 1 := by
  have hsmall := (tendsto_xiMassEntropyCriticalResidualFraction_zero q).eventually_lt_const
    (by norm_num : (0 : ℝ) < 1)
  filter_upwards [hsmall, eventually_gt_atTop (0 : ℝ)] with A hsmallA hA
  have hx : 1 < 3 * A + 9 := by linarith
  have hL : 0 < Real.log (3 * A + 9) := Real.log_pos hx
  have hres : 0 < xiMassEntropyCriticalResidualFraction q A := by
    unfold xiMassEntropyCriticalResidualFraction
    exact mul_pos hq (div_pos (pow_pos hL 10) hA)
  unfold xiMassExactEntropyBudgetFraction
  constructor <;> linarith

theorem tendsto_xiMassExactEntropyBudgetFraction_one (q : ℝ) :
    Tendsto (xiMassExactEntropyBudgetFraction q) atTop (𝓝 1) := by
  unfold xiMassExactEntropyBudgetFraction
  simpa only [sub_zero] using
    tendsto_const_nhds.sub (tendsto_xiMassEntropyCriticalResidualFraction_zero q)

/-- Exact entropy-critical corona envelope before aperture rescaling. -/
def xiMassExactEntropyBudgetEnvelope (σ q A : ℝ) : ℝ :=
  xiMassMarginBudgetEnvelope σ (xiMassExactEntropyBudgetFraction q A) A

theorem xiMassExactEntropyBudgetEnvelope_eq_scaled
    (σ q : ℝ) {A : ℝ} (hA : 0 < A) :
    xiMassExactEntropyBudgetEnvelope σ q A =
      xiMassExactEntropyScaledEnvelope σ q ((3 / 2) * A) := by
  have hL : 0 < Real.log (3 * A + 9) := Real.log_pos (by linarith)
  unfold xiMassExactEntropyBudgetEnvelope xiMassExactEntropyBudgetFraction
    xiMassEntropyCriticalResidualFraction xiMassMarginBudgetEnvelope
    xiMassCriticalZeroFreeEnvelope xiMassExactEntropyScaledEnvelope
  rw [show 2 * ((3 / 2 : ℝ) * A) = 3 * A by ring]
  unfold xiWardZeroFreeMargin
  rw [abs_of_nonneg (by positivity : 0 ≤ 3 * A)]
  congr 2
  field_simp [hA.ne', hL.ne']
  ring

theorem tendsto_xiMassExactEntropyBudgetEnvelope_zero
    {σ q : ℝ} (hwall : 1 < 3 * σ * q * xiWardZeroFreeMarginC / 13) :
    Tendsto (xiMassExactEntropyBudgetEnvelope σ q) atTop (𝓝 0) := by
  have hscale : Tendsto (fun A : ℝ => (3 / 2) * A) atTop atTop :=
    tendsto_id.const_mul_atTop (by norm_num)
  have h := (tendsto_xiMassExactEntropyScaledEnvelope_zero hwall).comp hscale
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with A hA
  exact (xiMassExactEntropyBudgetEnvelope_eq_scaled σ q hA).symm

/-- Explicit entropy-critical frequency schedule. -/
def xiMassExactEntropyBudgetFrequency (σ q A : ℝ) : ℝ :=
  xiMassMarginBudgetFrequency σ (xiMassExactEntropyBudgetFraction q A) A

theorem xiMassExactEntropyBudgetFrequency_pos
    {σ q A : ℝ} (hσ : 0 < σ) (hA : 0 < A)
    (hθ1 : xiMassExactEntropyBudgetFraction q A < 1) :
    0 < xiMassExactEntropyBudgetFrequency σ q A := by
  unfold xiMassExactEntropyBudgetFrequency
  exact xiMassMarginBudgetFrequency_pos hσ hθ1.le hA

theorem xiMassExactEntropyBudgetFrequency_layer_eq
    {σ q A : ℝ} (hσ : 0 < σ) (hA : 0 < A)
    (hθ1 : xiMassExactEntropyBudgetFraction q A < 1) :
    |xiMassExactEntropyBudgetFrequency σ q A| *
        (1 / 2 - xiMassExactEntropyBudgetFraction q A *
          xiWardZeroFreeMargin (3 * A)) = 2 * σ * A := by
  unfold xiMassExactEntropyBudgetFrequency
  exact xiMassMarginBudgetFrequency_layer_eq hσ hθ1.le hA

theorem xiMassExactEntropyBudgetFrequency_lower
    {σ q A : ℝ} (hσ : 0 < σ) (hA : 0 < A)
    (hθ0 : 0 < xiMassExactEntropyBudgetFraction q A)
    (hθ1 : xiMassExactEntropyBudgetFraction q A < 1) :
    2 * σ * A ≤ |xiMassExactEntropyBudgetFrequency σ q A| := by
  unfold xiMassExactEntropyBudgetFrequency
  exact xiMassMarginBudgetFrequency_lower hσ hθ0 hθ1 hA

theorem xiMassExactEntropyBudgetFrequency_strictly_subcritical
    {σ q A : ℝ} (hσ : 0 < σ) (hA : 0 < A)
    (hθ0 : 0 < xiMassExactEntropyBudgetFraction q A)
    (hθ1 : xiMassExactEntropyBudgetFraction q A < 1) :
    4 * σ * A < |xiMassExactEntropyBudgetFrequency σ q A| := by
  unfold xiMassExactEntropyBudgetFrequency
  exact xiMassMarginBudgetFrequency_strictly_subcritical hσ hθ0 hθ1 hA

theorem tendsto_xiMassExactEntropyBudgetFrequency_atTop
    {σ q : ℝ} (hσ : 0 < σ) (hq : 0 < q) :
    Tendsto (xiMassExactEntropyBudgetFrequency σ q) atTop atTop := by
  have hlinear : Tendsto (fun A : ℝ => 4 * σ * A) atTop atTop :=
    tendsto_id.const_mul_atTop (by positivity)
  refine tendsto_atTop_mono' atTop ?_ hlinear
  filter_upwards [eventually_xiMassExactEntropyBudgetFraction_pos_lt_one hq,
    eventually_gt_atTop (0 : ℝ)] with A hθ hA
  have huPos := xiMassExactEntropyBudgetFrequency_pos hσ hA hθ.2
  simpa only [abs_of_pos huPos] using
    (xiMassExactEntropyBudgetFrequency_strictly_subcritical hσ hA hθ.1 hθ.2).le

/-- **Exact entropy-wall extinction.** Above coefficient one, complete literal source vanishes
on an explicit genuinely subcritical schedule tending to infinite frequency. -/
theorem tendsto_norm_xiMassBottomPrimeIntegral_exactEntropyBudget_zero
    {σ q : ℝ} (hσ : 0 < σ) (hq : 0 < q)
    (hwall : 1 < 3 * σ * q * xiWardZeroFreeMarginC / 13) :
    Tendsto (fun A : ℝ =>
      ‖xiMassBottomPrimeIntegral (A + 1 / 2) 1
        ((σ : ℂ) + xiMassExactEntropyBudgetFrequency σ q A * I)‖)
      atTop (𝓝 0) := by
  have henv := tendsto_xiMassExactEntropyBudgetEnvelope_zero hwall
  have henvMul : Tendsto (fun A : ℝ =>
      ‖(Real.pi : ℂ) * I‖ * xiMassExactEntropyBudgetEnvelope σ q A)
      atTop (𝓝 0) := by
    simpa only [mul_zero] using
      Filter.Tendsto.const_mul ‖(Real.pi : ℂ) * I‖ henv
  have hexpTrace : Tendsto (fun A : ℝ => Real.exp (-(σ / 12) * A))
      atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp
      (tendsto_id.const_mul_atTop_of_neg (by linarith : -(σ / 12) < 0))
  have hexpArch : Tendsto (fun A : ℝ => Real.exp (-(σ / 2) * A))
      atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp
      (tendsto_id.const_mul_atTop_of_neg (by linarith : -(σ / 2) < 0))
  have htraceTail : Tendsto (fun A : ℝ =>
      ‖(Real.pi : ℂ) * I‖ *
        (Real.exp (-(σ / 12) * A) * xiPoissonTraceReal (σ / 12)))
      atTop (𝓝 0) := by
    have h1 := Filter.Tendsto.mul_const (xiPoissonTraceReal (σ / 12)) hexpTrace
    have h2 := Filter.Tendsto.const_mul ‖(Real.pi : ℂ) * I‖ h1
    simpa only [zero_mul, mul_zero] using h2
  have harchTail : Tendsto (fun A : ℝ =>
      Real.exp (-(σ / 2) * A) * xiMassBottomArchUniformBound 2 (σ / 2))
      atTop (𝓝 0) := by
    simpa only [zero_mul] using
      Filter.Tendsto.mul_const (xiMassBottomArchUniformBound 2 (σ / 2)) hexpArch
  have hmajor : Tendsto (fun A : ℝ =>
      ‖(Real.pi : ℂ) * I‖ * xiMassExactEntropyBudgetEnvelope σ q A +
        ‖(Real.pi : ℂ) * I‖ *
          (Real.exp (-(σ / 12) * A) * xiPoissonTraceReal (σ / 12)) +
        Real.exp (-(σ / 2) * A) *
          xiMassBottomArchUniformBound 2 (σ / 2)) atTop (𝓝 0) := by
    simpa only [zero_add] using (henvMul.add htraceTail).add harchTail
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun _ => norm_nonneg _
  · filter_upwards [eventually_ge_atTop (3 / 2 : ℝ),
      eventually_xiMassExactEntropyBudgetFraction_pos_lt_one hq] with A hA hθ
    have hApos : 0 < A := by linarith
    let θ : ℝ := xiMassExactEntropyBudgetFraction q A
    have hlower := xiMassExactEntropyBudgetFrequency_lower hσ hApos hθ.1 hθ.2
    have hlayer := (xiMassExactEntropyBudgetFrequency_layer_eq hσ hApos hθ.2).le
    have hbound := norm_xiMassBottomPrimeIntegral_le_marginBudgetEnvelope
      (a := A + 1 / 2) (σ := σ) (θ := θ)
      (u := xiMassExactEntropyBudgetFrequency σ q A) (by linarith) hσ hθ.2
      (by simpa only [add_sub_cancel_right] using hlower)
      (by simpa only [add_sub_cancel_right, θ] using hlayer)
    simpa only [add_sub_cancel_right, xiMassExactEntropyBudgetEnvelope, θ] using hbound
  · exact hmajor

end

end RHTower
