import GaloisForLFunctions.RHTower.XiMassParameterizedZeroFreeMarginBudget

/-!
# Second-order moving Xi zero-free margin budget

The spent budget fraction now tends to one: only a second zero-free width remains as decay.
The residual scale `A / log(A)^18` still absorbs exact widened-corona entropy, so the complete
literal Euler/Gamma source vanishes on an explicit genuinely subcritical schedule.
-/

open Complex Metric Set Filter
open scoped BigOperators Topology

namespace RHTower

noncomputable section

/-- Any fixed log power leaves a divergent residual mass scale. -/
theorem tendsto_xiZeroFreeScale_pow (n : ℕ) :
    Tendsto (fun B : ℝ => B / Real.log (2 * B + 9) ^ n) atTop atTop := by
  have hratio := tendsto_pow_log_two_mul_add_nine_div_id n
  have hratioGT :
      Tendsto (fun B : ℝ => Real.log (2 * B + 9) ^ n / B)
        atTop (𝓝[>] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨hratio, ?_⟩
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with B hB
    have hlog : 0 < Real.log (2 * B + 9) := by
      apply Real.log_pos
      linarith
    exact div_pos (pow_pos hlog n) hB
  have hinv := hratioGT.inv_tendsto_nhdsGT_zero
  apply hinv.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with B hB
  have hlog : 0 < Real.log (2 * B + 9) := by
    apply Real.log_pos
    linarith
  change (Real.log (2 * B + 9) ^ n / B)⁻¹ =
    B / Real.log (2 * B + 9) ^ n
  rw [inv_div]

/-- Rescaled envelope when the unspent margin fraction equals one further zero-free width. -/
def xiMassSecondOrderScaledEnvelope (σ B : ℝ) : ℝ :=
  xiZeroCountEnvelopeConstant * (2 * B + 3) * Real.log (2 * B + 4) *
    Real.exp (-(2 * σ / 13) * B * xiWardZeroFreeMargin (2 * B) ^ 2)

/-- A second-order residual margin still absorbs the full widened-corona entropy. -/
theorem tendsto_xiMassSecondOrderScaledEnvelope_zero
    {σ : ℝ} (hσ : 0 < σ) :
    Tendsto (xiMassSecondOrderScaledEnvelope σ) atTop (𝓝 0) := by
  let C : ℝ := xiZeroCountEnvelopeConstant
  let D : ℝ := C + 1
  let c : ℝ := (2 * σ / 13) * xiWardZeroFreeMarginC ^ 2
  have hC : 0 < C := by dsimp only [C]; exact xiZeroCountEnvelopeConstant_pos
  have hD : 0 < D := by dsimp only [D]; linarith
  have hc : 0 < c := by
    dsimp only [c]
    exact mul_pos (by positivity) (pow_pos xiWardZeroFreeMarginC_pos 2)
  have h18 := tendsto_pow_log_two_mul_add_nine_div_id 18
  have h19 := tendsto_pow_log_two_mul_add_nine_div_id 19
  have hcombo :
      Tendsto (fun B : ℝ =>
        Real.log D * (Real.log (2 * B + 9) ^ (18 : ℕ) / B) +
          2 * (Real.log (2 * B + 9) ^ (19 : ℕ) / B))
        atTop (𝓝 0) := by
    simpa only [zero_add, mul_zero] using
      (tendsto_const_nhds.mul h18).add (tendsto_const_nhds.mul h19)
  have hsmall := hcombo.eventually_le_const (show 0 < c / 2 by positivity)
  have hscale := tendsto_xiZeroFreeScale_pow 18
  have hscaledBot :
      Tendsto (fun B : ℝ => -(c / 2) *
        (B / Real.log (2 * B + 9) ^ (18 : ℕ))) atTop atBot :=
    hscale.const_mul_atTop_of_neg
      (neg_lt_zero.mpr (div_pos hc (by norm_num)))
  have hdecay :
      Tendsto (fun B : ℝ =>
        Real.exp (-(c / 2) *
          (B / Real.log (2 * B + 9) ^ (18 : ℕ)))) atTop (𝓝 0) := by
    exact Real.tendsto_exp_atBot.comp hscaledBot
  apply squeeze_zero'
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with B hB
    unfold xiMassSecondOrderScaledEnvelope
    have hlog : 0 ≤ Real.log (2 * B + 4) :=
      Real.log_nonneg (by linarith)
    change 0 ≤ C * (2 * B + 3) * Real.log (2 * B + 4) *
      Real.exp (-(2 * σ / 13) * B * xiWardZeroFreeMargin (2 * B) ^ 2)
    positivity
  · filter_upwards [hsmall, eventually_gt_atTop (0 : ℝ)] with B hsmallB hB
    let x : ℝ := 2 * B + 9
    let y : ℝ := 2 * B + 4
    let L : ℝ := Real.log x
    let X : ℝ := B / L ^ (18 : ℕ)
    let P : ℝ := C * (2 * B + 3) * Real.log y
    have hx : 0 < x := by dsimp only [x]; linarith
    have hy : 0 < y := by dsimp only [y]; linarith
    have hL : 0 < L := by
      dsimp only [L]
      exact Real.log_pos (by dsimp only [x]; linarith)
    have hL18 : 0 < L ^ (18 : ℕ) := pow_pos hL 18
    have hCD : C ≤ D := by dsimp only [D]; linarith
    have hfac0 : 0 ≤ 2 * B + 3 := by linarith
    have hfac : 2 * B + 3 ≤ x := by dsimp only [x]; linarith
    have hlogy0 : 0 ≤ Real.log y := Real.log_nonneg (by dsimp only [y]; linarith)
    have hlogyx : Real.log y ≤ L := by
      dsimp only [L]
      exact Real.log_le_log hy (by dsimp only [x, y]; linarith)
    have hLx : L ≤ x := by
      have h := Real.log_le_sub_one_of_pos hx
      dsimp only [L]
      linarith
    have hlogyx' : Real.log y ≤ x := hlogyx.trans hLx
    have hP : P ≤ D * x ^ 2 := by
      dsimp only [P]
      calc
        C * (2 * B + 3) * Real.log y ≤ D * x * x := by gcongr
        _ = D * x ^ 2 := by ring
    have hsmallMul :
        Real.log D * L ^ (18 : ℕ) + 2 * L ^ (19 : ℕ) ≤ c / 2 * B := by
      have hmul := mul_le_mul_of_nonneg_left hsmallB hB.le
      have heqLeft :
          B * (Real.log D * (L ^ (18 : ℕ) / B) +
            2 * (L ^ (19 : ℕ) / B)) =
              Real.log D * L ^ (18 : ℕ) + 2 * L ^ (19 : ℕ) := by
        field_simp
      rw [show Real.log (2 * B + 9) = L by rfl, heqLeft] at hmul
      nlinarith
    have hbudget : Real.log D + 2 * L ≤ c / 2 * X := by
      dsimp only [X]
      rw [show c / 2 * (B / L ^ (18 : ℕ)) =
        (c / 2 * B) / L ^ (18 : ℕ) by ring, le_div_iff₀ hL18]
      calc
        (Real.log D + 2 * L) * L ^ (18 : ℕ) =
            Real.log D * L ^ (18 : ℕ) + 2 * L ^ (19 : ℕ) := by ring
        _ ≤ c / 2 * B := hsmallMul
    have hexpEq : Real.exp (Real.log D + 2 * L) = D * x ^ 2 := by
      rw [Real.exp_add, Real.exp_log hD]
      have htwo : 2 * L = L + L := by ring
      rw [htwo, Real.exp_add]
      dsimp only [L]
      rw [Real.exp_log hx]
      ring
    have hPexp : P ≤ Real.exp (c / 2 * X) := by
      calc
        P ≤ D * x ^ 2 := hP
        _ = Real.exp (Real.log D + 2 * L) := hexpEq.symm
        _ ≤ Real.exp (c / 2 * X) := Real.exp_le_exp.mpr hbudget
    have hcalc :
        P * Real.exp (-c * X) ≤ Real.exp (-(c / 2) * X) := by
      calc
        P * Real.exp (-c * X) ≤
            Real.exp (c / 2 * X) * Real.exp (-c * X) :=
          mul_le_mul_of_nonneg_right hPexp (Real.exp_pos _).le
        _ = Real.exp (-(c / 2) * X) := by
          rw [← Real.exp_add]
          congr 1
          ring
    have hmargin :
        xiWardZeroFreeMargin (2 * B) =
          xiWardZeroFreeMarginC / L ^ (9 : ℕ) := by
      unfold xiWardZeroFreeMargin
      rw [abs_of_nonneg (by positivity : 0 ≤ 2 * B)]
    have hexponent :
        -(2 * σ / 13) * B *
            (xiWardZeroFreeMarginC / L ^ (9 : ℕ)) ^ 2 = -c * X := by
      dsimp only [c, X]
      field_simp
    change P * Real.exp (-(2 * σ / 13) * B * xiWardZeroFreeMargin (2 * B) ^ 2) ≤
      Real.exp (-(c / 2) * X)
    rw [hmargin, hexponent]
    exact hcalc
  · exact hdecay

/-- Spend all but one further zero-free width of the available margin. -/
def xiMassSecondOrderBudgetFraction (A : ℝ) : ℝ :=
  1 - xiWardZeroFreeMargin (3 * A)

theorem xiMassSecondOrderBudgetFraction_pos (A : ℝ) :
    0 < xiMassSecondOrderBudgetFraction A := by
  unfold xiMassSecondOrderBudgetFraction
  have hd8 := xiWardZeroFreeMargin_le_one_eighth (3 * A)
  linarith

theorem xiMassSecondOrderBudgetFraction_lt_one (A : ℝ) :
    xiMassSecondOrderBudgetFraction A < 1 := by
  unfold xiMassSecondOrderBudgetFraction
  linarith [xiWardZeroFreeMargin_pos (3 * A)]

theorem tendsto_xiWardZeroFreeMargin_three_mul_zero :
    Tendsto (fun A : ℝ => xiWardZeroFreeMargin (3 * A)) atTop (𝓝 0) := by
  have haff : Tendsto (fun A : ℝ => 3 * A + 9) atTop atTop :=
    tendsto_atTop_add_const_right atTop 9
      (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 3))
  have hlog : Tendsto (fun A : ℝ => Real.log (3 * A + 9)) atTop atTop :=
    Real.tendsto_log_atTop.comp haff
  have hpow : Tendsto (fun A : ℝ => Real.log (3 * A + 9) ^ (9 : ℕ))
      atTop atTop :=
    (Filter.tendsto_pow_atTop (by norm_num : (9 : ℕ) ≠ 0)).comp hlog
  have hinv : Tendsto (fun A : ℝ =>
      (Real.log (3 * A + 9) ^ (9 : ℕ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hpow
  have hform : Tendsto (fun A : ℝ =>
      xiWardZeroFreeMarginC * (Real.log (3 * A + 9) ^ (9 : ℕ))⁻¹)
      atTop (𝓝 0) := by
    simpa only [mul_zero] using
      Filter.Tendsto.const_mul xiWardZeroFreeMarginC hinv
  apply hform.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with A hA
  unfold xiWardZeroFreeMargin
  rw [abs_of_nonneg (by positivity : 0 ≤ 3 * A)]
  simp only [div_eq_mul_inv]

theorem tendsto_xiMassSecondOrderBudgetFraction_one :
    Tendsto xiMassSecondOrderBudgetFraction atTop (𝓝 1) := by
  unfold xiMassSecondOrderBudgetFraction
  simpa only [sub_zero] using
    tendsto_const_nhds.sub tendsto_xiWardZeroFreeMargin_three_mul_zero

/-- Moving-budget corona envelope before rescaling. -/
def xiMassSecondOrderBudgetEnvelope (σ A : ℝ) : ℝ :=
  xiMassMarginBudgetEnvelope σ (xiMassSecondOrderBudgetFraction A) A

theorem xiMassSecondOrderBudgetEnvelope_eq_scaled (σ A : ℝ) :
    xiMassSecondOrderBudgetEnvelope σ A =
      xiMassSecondOrderScaledEnvelope σ ((3 / 2) * A) := by
  unfold xiMassSecondOrderBudgetEnvelope xiMassSecondOrderBudgetFraction
    xiMassMarginBudgetEnvelope xiMassCriticalZeroFreeEnvelope
    xiMassSecondOrderScaledEnvelope
  rw [show 2 * ((3 / 2 : ℝ) * A) = 3 * A by ring]
  congr 2
  ring_nf

theorem tendsto_xiMassSecondOrderBudgetEnvelope_zero
    {σ : ℝ} (hσ : 0 < σ) :
    Tendsto (xiMassSecondOrderBudgetEnvelope σ) atTop (𝓝 0) := by
  have hscale : Tendsto (fun A : ℝ => (3 / 2) * A) atTop atTop :=
    tendsto_id.const_mul_atTop (by norm_num)
  have h := (tendsto_xiMassSecondOrderScaledEnvelope_zero hσ).comp hscale
  exact h.congr' (Eventually.of_forall fun A =>
    (xiMassSecondOrderBudgetEnvelope_eq_scaled σ A).symm)

/-- Explicit schedule spending all but a second-order residual of zero-free width. -/
def xiMassSecondOrderBudgetFrequency (σ A : ℝ) : ℝ :=
  xiMassMarginBudgetFrequency σ (xiMassSecondOrderBudgetFraction A) A

theorem xiMassSecondOrderBudgetFrequency_pos
    {σ A : ℝ} (hσ : 0 < σ) (hA : 0 < A) :
    0 < xiMassSecondOrderBudgetFrequency σ A := by
  unfold xiMassSecondOrderBudgetFrequency
  exact xiMassMarginBudgetFrequency_pos hσ
    (xiMassSecondOrderBudgetFraction_lt_one A).le hA

theorem xiMassSecondOrderBudgetFrequency_layer_eq
    {σ A : ℝ} (hσ : 0 < σ) (hA : 0 < A) :
    |xiMassSecondOrderBudgetFrequency σ A| *
        (1 / 2 - xiMassSecondOrderBudgetFraction A *
          xiWardZeroFreeMargin (3 * A)) = 2 * σ * A := by
  unfold xiMassSecondOrderBudgetFrequency
  exact xiMassMarginBudgetFrequency_layer_eq hσ
    (xiMassSecondOrderBudgetFraction_lt_one A).le hA

theorem xiMassSecondOrderBudgetFrequency_lower
    {σ A : ℝ} (hσ : 0 < σ) (hA : 0 < A) :
    2 * σ * A ≤ |xiMassSecondOrderBudgetFrequency σ A| := by
  unfold xiMassSecondOrderBudgetFrequency
  exact xiMassMarginBudgetFrequency_lower hσ
    (xiMassSecondOrderBudgetFraction_pos A)
    (xiMassSecondOrderBudgetFraction_lt_one A) hA

/-- The second-order moving schedule remains genuinely below the geometric wall. -/
theorem xiMassSecondOrderBudgetFrequency_strictly_subcritical
    {σ A : ℝ} (hσ : 0 < σ) (hA : 0 < A) :
    4 * σ * A < |xiMassSecondOrderBudgetFrequency σ A| := by
  unfold xiMassSecondOrderBudgetFrequency
  exact xiMassMarginBudgetFrequency_strictly_subcritical hσ
    (xiMassSecondOrderBudgetFraction_pos A)
    (xiMassSecondOrderBudgetFraction_lt_one A) hA

theorem tendsto_xiMassSecondOrderBudgetFrequency_atTop
    {σ : ℝ} (hσ : 0 < σ) :
    Tendsto (xiMassSecondOrderBudgetFrequency σ) atTop atTop := by
  have hlinear : Tendsto (fun A : ℝ => 4 * σ * A) atTop atTop :=
    tendsto_id.const_mul_atTop (by positivity)
  refine tendsto_atTop_mono' atTop ?_ hlinear
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with A hA
  simpa only [abs_of_pos (xiMassSecondOrderBudgetFrequency_pos hσ hA)] using
    (xiMassSecondOrderBudgetFrequency_strictly_subcritical hσ hA).le

/-- **Second-order moving-budget extinction.**  The complete literal source vanishes even when
the spent fraction tends to one and only a second zero-free width remains as decay. -/
theorem tendsto_norm_xiMassBottomPrimeIntegral_secondOrderBudget_zero
    {σ : ℝ} (hσ : 0 < σ) :
    Tendsto (fun A : ℝ =>
      ‖xiMassBottomPrimeIntegral (A + 1 / 2) 1
        ((σ : ℂ) + xiMassSecondOrderBudgetFrequency σ A * I)‖)
      atTop (𝓝 0) := by
  have henv := tendsto_xiMassSecondOrderBudgetEnvelope_zero hσ
  have henvMul : Tendsto (fun A : ℝ =>
      ‖(Real.pi : ℂ) * I‖ * xiMassSecondOrderBudgetEnvelope σ A)
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
      ‖(Real.pi : ℂ) * I‖ * xiMassSecondOrderBudgetEnvelope σ A +
        ‖(Real.pi : ℂ) * I‖ *
          (Real.exp (-(σ / 12) * A) * xiPoissonTraceReal (σ / 12)) +
        Real.exp (-(σ / 2) * A) *
          xiMassBottomArchUniformBound 2 (σ / 2)) atTop (𝓝 0) := by
    simpa only [zero_add] using (henvMul.add htraceTail).add harchTail
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun _ => norm_nonneg _
  · filter_upwards [eventually_ge_atTop (3 / 2 : ℝ)] with A hA
    have hApos : 0 < A := by linarith
    let θ : ℝ := xiMassSecondOrderBudgetFraction A
    have hθ0 : 0 < θ := xiMassSecondOrderBudgetFraction_pos A
    have hθ1 : θ < 1 := xiMassSecondOrderBudgetFraction_lt_one A
    have hlower := xiMassSecondOrderBudgetFrequency_lower hσ hApos
    have hlayer := (xiMassSecondOrderBudgetFrequency_layer_eq hσ hApos).le
    have hbound := norm_xiMassBottomPrimeIntegral_le_marginBudgetEnvelope
      (a := A + 1 / 2) (σ := σ) (θ := θ)
      (u := xiMassSecondOrderBudgetFrequency σ A) (by linarith) hσ hθ1
      (by simpa only [add_sub_cancel_right] using hlower)
      (by simpa only [add_sub_cancel_right, θ] using hlayer)
    simpa only [add_sub_cancel_right, xiMassSecondOrderBudgetEnvelope, θ] using hbound
  · exact hmajor

end

end RHTower

