import GaloisForLFunctions.RHTower.XiCTaylorMovingPositiveCompletionGaugeNoGo

/-!
# Linear conditioning cost of a signed moving completion gauge

Positive moving completions have zero Xi divisor charge.  A real signed source can evade the
positive cone only through cancellation.  This module measures that cancellation before
logarithmic division.

For a signed density `h`, `signedTailCompletionVariation h z` is the real part of the completion
formed with `|h|`.  It is the source-visible absolute completion mass.  If this mass is at most
`κ` times the norm of the signed completion, then the corresponding logarithmic phase velocity is
at most `(κ + 1) / Im z`.

At an Xi zero of multiplicity `m`, exact screening on the `1/n` anisotropic mesh forces

`(m * (1/2 - Re σ) / 8) * (n+1) < κₙ + 1`

eventually.  Thus a successful signed scalar gauge must become at least linearly ill-conditioned;
bounded or sublinear cancellation cannot screen even one divisor unit.
-/

open Complex Real MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

/-- Absolute completion mass of a real signed source density. -/
def signedTailCompletionVariation (h : ℝ → ℝ) (z : ℂ) : ℝ :=
  (positiveTailCompletion (fun t : ℝ => |h t|) z).re

/-- Minimal source cancellation condition number: absolute completion mass divided by the norm of
the surviving signed completion. -/
def signedTailCompletionConditionNumber (h : ℝ → ℝ) (z : ℂ) : ℝ :=
  signedTailCompletionVariation h z / ‖positiveTailCompletion h z‖

/-- Raw signed source data before choosing any upper bound for its cancellation condition number. -/
structure SignedTailCompletionSourceAt
    (h : ℝ → ℝ) (F D z : ℂ) : Prop where
  completionIntegrable : IntegrableOn (fun t : ℝ =>
    (h t : ℂ) * (1 - spectralTranslationPhase t z)) (Ioi 0)
  variationIntegrable : IntegrableOn (fun t : ℝ =>
    ((|h t| : ℝ) : ℂ) * (1 - spectralTranslationPhase t z)) (Ioi 0)
  derivativeIntegrable : IntegrableOn (fun t : ℝ =>
    (h t : ℂ) * (-((t : ℂ) * I) * spectralTranslationPhase t z)) (Ioi 0)
  completion_eq : positiveTailCompletion h z = -I * z * F
  completionDerivative_eq :
    positiveTailCompletionDerivative h z = -I * (F + z * D)
  value_ne_zero : F ≠ 0

/-- The derivative of a signed completion is controlled by its absolute completion mass.  This
retains source cancellation in the denominator rather than taking an absolute value after
logarithmic division. -/
theorem norm_positiveTailCompletionDerivative_le_signedVariation_div
    {h : ℝ → ℝ} {z : ℂ} (hz : 0 < z.im)
    (hvariation : IntegrableOn (fun t : ℝ =>
      ((|h t| : ℝ) : ℂ) * (1 - spectralTranslationPhase t z)) (Ioi 0))
    (hderivative : IntegrableOn (fun t : ℝ =>
      (h t : ℂ) * (-((t : ℂ) * I) * spectralTranslationPhase t z)) (Ioi 0)) :
    ‖positiveTailCompletionDerivative h z‖ ≤
      signedTailCompletionVariation h z / z.im := by
  let f : ℝ → ℂ := fun t =>
    ((|h t| : ℝ) : ℂ) * (1 - spectralTranslationPhase t z)
  let f' : ℝ → ℂ := fun t =>
    (h t : ℂ) * (-((t : ℂ) * I) * spectralTranslationPhase t z)
  have hf : Integrable f (volume.restrict (Ioi 0)) := hvariation
  have hf' : Integrable f' (volume.restrict (Ioi 0)) := hderivative
  have hmajor : Integrable (fun t => (f t).re / z.im)
      (volume.restrict (Ioi 0)) := hf.re.div_const z.im
  calc
    ‖positiveTailCompletionDerivative h z‖ =
        ‖∫ t : ℝ in Ioi 0, f' t‖ := rfl
    _ ≤ ∫ t : ℝ in Ioi 0, ‖f' t‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t : ℝ in Ioi 0, (f t).re / z.im := by
      apply MeasureTheory.integral_mono_ae hf'.norm hmajor
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have hpoint :=
        norm_positiveTailCompletionDerivative_integrand_le_re_div
          (h := fun s : ℝ => |h s|) (t := t)
          ht.le (abs_nonneg (h t)) hz
      calc
        ‖f' t‖ =
            ‖(((|h t| : ℝ) : ℂ) *
              (-((t : ℂ) * I) * spectralTranslationPhase t z))‖ := by
          dsimp only [f']
          simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_abs]
        _ ≤ (f t).re / z.im := by
          simpa only [f] using hpoint
    _ = signedTailCompletionVariation h z / z.im := by
      rw [MeasureTheory.integral_div]
      have hre :
          (∫ t : ℝ in Ioi 0, (f t).re) =
            (∫ t : ℝ in Ioi 0, f t).re :=
        integral_re (μ := volume.restrict (Ioi 0)) hf
      rw [hre]
      rfl

/-- A completion contraction with loss `κ` gives derivative loss exactly `κ+1`; the extra one is
the undifferentiated source term in the covariant integration-by-parts connection. -/
theorem norm_derivative_le_conditionNumber_add_one_div_im
    {F D G G' z : ℂ} {kappa : ℝ}
    (hz : 0 < z.im) (hkappa : 0 ≤ kappa)
    (hG : G = -I * z * F)
    (hG' : G' = -I * (F + z * D))
    (hcontract : ‖G'‖ ≤ kappa * (‖G‖ / z.im)) :
    ‖D‖ ≤ ((kappa + 1) / z.im) * ‖F‖ := by
  have hzNorm : z.im ≤ ‖z‖ := by
    simpa only [abs_of_pos hz] using Complex.abs_im_le_norm z
  have hzNormPos : 0 < ‖z‖ := lt_of_lt_of_le hz hzNorm
  have hGnorm : ‖G‖ = ‖z‖ * ‖F‖ := by
    rw [hG, norm_mul, norm_mul]
    norm_num
  have hzd : z * D = I * G' - F := by
    rw [hG']
    ring_nf
    rw [I_sq]
    ring
  have htri : ‖z‖ * ‖D‖ ≤ ‖G'‖ + ‖F‖ := by
    rw [← norm_mul, hzd]
    calc
      ‖I * G' - F‖ ≤ ‖I * G'‖ + ‖F‖ := norm_sub_le _ _
      _ = ‖G'‖ + ‖F‖ := by simp
  have hc : ‖G'‖ ≤ kappa * ((‖z‖ * ‖F‖) / z.im) := by
    simpa only [hGnorm] using hcontract
  have hmul : ‖z‖ * ‖D‖ ≤
      ‖z‖ * (kappa * (‖F‖ / z.im) + ‖F‖ / ‖z‖) := by
    calc
      ‖z‖ * ‖D‖ ≤ ‖G'‖ + ‖F‖ := htri
      _ ≤ kappa * ((‖z‖ * ‖F‖) / z.im) + ‖F‖ := by gcongr
      _ = ‖z‖ * (kappa * (‖F‖ / z.im) + ‖F‖ / ‖z‖) := by
        field_simp [ne_of_gt hzNormPos, ne_of_gt hz]
  have hdiv :
      ‖D‖ ≤ kappa * (‖F‖ / z.im) + ‖F‖ / ‖z‖ :=
    (mul_le_mul_iff_of_pos_left hzNormPos).mp hmul
  calc
    ‖D‖ ≤ kappa * (‖F‖ / z.im) + ‖F‖ / ‖z‖ := hdiv
    _ ≤ kappa * (‖F‖ / z.im) + ‖F‖ / z.im := by
      gcongr
    _ = ((kappa + 1) / z.im) * ‖F‖ := by ring

/-- Pointwise signed-completion data with a source-visible cancellation condition number. -/
structure SignedTailCompletionGaugeAt
    (h : ℝ → ℝ) (F D z : ℂ) (kappa : ℝ) : Prop where
  kappa_nonneg : 0 ≤ kappa
  completionIntegrable : IntegrableOn (fun t : ℝ =>
    (h t : ℂ) * (1 - spectralTranslationPhase t z)) (Ioi 0)
  variationIntegrable : IntegrableOn (fun t : ℝ =>
    ((|h t| : ℝ) : ℂ) * (1 - spectralTranslationPhase t z)) (Ioi 0)
  derivativeIntegrable : IntegrableOn (fun t : ℝ =>
    (h t : ℂ) * (-((t : ℂ) * I) * spectralTranslationPhase t z)) (Ioi 0)
  variation_le :
    signedTailCompletionVariation h z ≤
      kappa * ‖positiveTailCompletion h z‖
  completion_eq : positiveTailCompletion h z = -I * z * F
  completionDerivative_eq :
    positiveTailCompletionDerivative h z = -I * (F + z * D)
  value_ne_zero : F ≠ 0

/-- The exact condition-number ratio is admissible whenever the source value is nonzero.  This
prevents the conditioning lower bound from being weakened by an artificially inflated witness. -/
theorem SignedTailCompletionSourceAt.toConditioned
    {h : ℝ → ℝ} {F D z : ℂ}
    (hs : SignedTailCompletionSourceAt h F D z)
    (hz : 0 < z.im) :
    SignedTailCompletionGaugeAt h F D z
      (signedTailCompletionConditionNumber h z) := by
  have hvar :=
    norm_positiveTailCompletionDerivative_le_signedVariation_div hz
      hs.variationIntegrable hs.derivativeIntegrable
  have hVdiv :
      0 ≤ signedTailCompletionVariation h z / z.im :=
    (norm_nonneg _).trans hvar
  have hV : 0 ≤ signedTailCompletionVariation h z := by
    calc
      0 ≤ (signedTailCompletionVariation h z / z.im) * z.im :=
        mul_nonneg hVdiv hz.le
      _ = signedTailCompletionVariation h z := by field_simp
  have hz0 : z ≠ 0 := by
    intro hzero
    rw [hzero] at hz
    simp at hz
  have hG0 : positiveTailCompletion h z ≠ 0 := by
    rw [hs.completion_eq]
    exact mul_ne_zero
      (mul_ne_zero (neg_ne_zero.mpr I_ne_zero) hz0) hs.value_ne_zero
  have hGnorm : 0 < ‖positiveTailCompletion h z‖ :=
    norm_pos_iff.mpr hG0
  constructor
  · exact div_nonneg hV hGnorm.le
  · exact hs.completionIntegrable
  · exact hs.variationIntegrable
  · exact hs.derivativeIntegrable
  · unfold signedTailCompletionConditionNumber
    rw [div_mul_cancel₀ _ (ne_of_gt hGnorm)]
  · exact hs.completion_eq
  · exact hs.completionDerivative_eq
  · exact hs.value_ne_zero

/-- Signed gauge phase velocity is bounded by its cancellation condition number. -/
theorem SignedTailCompletionGaugeAt.abs_im_derivative_div_value_le
    {h : ℝ → ℝ} {F D z : ℂ} {kappa : ℝ}
    (hg : SignedTailCompletionGaugeAt h F D z kappa)
    (hz : 0 < z.im) :
    |(D / F).im| ≤ (kappa + 1) / z.im := by
  have hvar :=
    norm_positiveTailCompletionDerivative_le_signedVariation_div hz
      hg.variationIntegrable hg.derivativeIntegrable
  have hcontract :
      ‖positiveTailCompletionDerivative h z‖ ≤
        kappa * (‖positiveTailCompletion h z‖ / z.im) := by
    calc
      ‖positiveTailCompletionDerivative h z‖ ≤
          signedTailCompletionVariation h z / z.im := hvar
      _ ≤ (kappa * ‖positiveTailCompletion h z‖) / z.im :=
        div_le_div_of_nonneg_right hg.variation_le hz.le
      _ = kappa * (‖positiveTailCompletion h z‖ / z.im) := by ring
  have hD := norm_derivative_le_conditionNumber_add_one_div_im
    hz hg.kappa_nonneg hg.completion_eq hg.completionDerivative_eq hcontract
  have hFnorm : 0 < ‖F‖ := norm_pos_iff.mpr hg.value_ne_zero
  calc
    |(D / F).im| ≤ ‖D / F‖ := Complex.abs_im_le_norm _
    _ = ‖D‖ / ‖F‖ := norm_div D F
    _ ≤ (((kappa + 1) / z.im) * ‖F‖) / ‖F‖ :=
      div_le_div_of_nonneg_right hD hFnorm.le
    _ = (kappa + 1) / z.im := by field_simp

/-- Exact screening transfers the complete finite-Taylor multiplicity to the moving gauge
logarithmic current. -/
theorem tendsto_movingGauge_horizontalCharge_of_screened
    {N : ℕ → ℕ} (hN : XiCTaylorSuperaccurateSchedule N)
    {F D : ℕ → ℂ} {sigma : ℂ}
    (hscreen :
      XiCTaylorMovingPositiveTailCompletionGaugeChargeScreenedAt N F D sigma) :
    Tendsto
      (fun n : ℕ =>
        xiTaylorAnisotropicHorizontalStep sigma n * (D n / F n).im)
      atTop (nhds ((analyticOrderAt xi sigma).toNat : ℝ)) := by
  have hTaylor :=
    xiCTaylor_logDeriv_anisotropicHorizontalCharge_tendsto hN sigma
  have hdiff := hTaylor.sub hscreen
  convert hdiff using 1
  · funext n
    ring
  · ring

/-- **Linear signed-conditioning no-go.**  At an Xi zero, a signed completion which exactly
screens the finite-Taylor divisor charge must have cancellation condition number at least linear
in the explicit anisotropic mesh denominator. -/
theorem eventually_linear_conditionNumber_of_screened_at_xi_zero
    {N : ℕ → ℕ} (hN : XiCTaylorSuperaccurateSchedule N)
    {h : ℕ → ℝ → ℝ} {F D : ℕ → ℂ} {kappa : ℕ → ℝ}
    {sigma : ℂ} (hsigma : sigma.re < 1 / 2)
    (hzero : xi sigma = 0)
    (hg : ∀ᶠ n : ℕ in atTop, SignedTailCompletionGaugeAt
      (h n) (F n) (D n) (xiCTaylorAnisotropicCenteredPoint sigma n)
        (kappa n))
    (hscreen :
      XiCTaylorMovingPositiveTailCompletionGaugeChargeScreenedAt N F D sigma) :
    ∀ᶠ n : ℕ in atTop,
      ((((analyticOrderAt xi sigma).toNat : ℝ) *
          (1 / 2 - sigma.re)) / 8) *
          (((n + 1 : ℕ) : ℝ)) <
        kappa n + 1 := by
  let m : ℕ := (analyticOrderAt xi sigma).toNat
  let eta : ℝ := 1 / 2 - sigma.re
  have hm : 0 < m := Nat.pos_of_ne_zero (xi_order_toNat_ne_zero hzero)
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have heta : 0 < eta := by dsimp only [eta]; linarith
  have hcharge :=
    tendsto_movingGauge_horizontalCharge_of_screened hN hscreen
  have hchargeLower : ∀ᶠ n : ℕ in atTop,
      (m : ℝ) / 2 <
        xiTaylorAnisotropicHorizontalStep sigma n * (D n / F n).im := by
    simpa only [m] using
      hcharge.eventually (eventually_gt_nhds (by linarith))
  have himTend : Tendsto
      (fun n : ℕ => (xiCTaylorAnisotropicCenteredPoint sigma n).im)
      atTop (nhds eta) := by
    have h :=
      Complex.continuous_im.continuousAt.tendsto.comp
        (tendsto_xiCTaylorAnisotropicCenteredPoint sigma)
    have hetaEq : eta = (xiCTaylorCenteredPoint sigma).im := by
      dsimp only [eta, xiCTaylorCenteredPoint]
      rw [mul_im]
      simp only [sub_re, neg_re, I_re, neg_im, I_im]
      norm_num
    rw [hetaEq]
    exact h
  have himLower : ∀ᶠ n : ℕ in atTop,
      eta / 2 < (xiCTaylorAnisotropicCenteredPoint sigma n).im :=
    himTend.eventually (eventually_gt_nhds (by linarith))
  filter_upwards [hg, hchargeLower, himLower] with n hgn hqLower him
  let NN : ℕ := n + 1
  let x : ℝ := xiTaylorAnisotropicHorizontalStep sigma n
  let y : ℝ := (xiCTaylorAnisotropicCenteredPoint sigma n).im
  let q : ℝ := x * (D n / F n).im
  have hNN : 0 < NN := by dsimp only [NN]; omega
  have hNNR : (0 : ℝ) < (NN : ℝ) := by exact_mod_cast hNN
  have hxgeom := xiTaylorAnisotropicRightApprox_re_sub_bounds sigma hNN
  have hx : 0 < x := by
    dsimp only [x, xiTaylorAnisotropicHorizontalStep, NN]
    exact lt_of_lt_of_le (by positivity) hxgeom.1
  have hxUpper : x < 2 / (NN : ℝ) := by
    simpa only [x, xiTaylorAnisotropicHorizontalStep, NN] using hxgeom.2
  have hy : 0 < y := (half_pos heta).trans (by simpa only [y] using him)
  have hkplus : 0 < kappa n + 1 := by linarith [hgn.kappa_nonneg]
  have hlog :
      |(D n / F n).im| ≤ (kappa n + 1) / y := by
    simpa only [y] using hgn.abs_im_derivative_div_value_le hy
  have hqUpper : q ≤ x * ((kappa n + 1) / y) := by
    calc
      q ≤ |q| := le_abs_self q
      _ = x * |(D n / F n).im| := by
        dsimp only [q]
        rw [abs_mul, abs_of_pos hx]
      _ ≤ x * ((kappa n + 1) / y) :=
        mul_le_mul_of_nonneg_left hlog hx.le
  have hsource :
      (m : ℝ) * eta / 4 < x * (kappa n + 1) := by
    have hqLower' : (m : ℝ) / 2 < q := by simpa only [m, q] using hqLower
    have hdiv : (m : ℝ) / 2 < x * ((kappa n + 1) / y) :=
      hqLower'.trans_le hqUpper
    have hmul :
        ((m : ℝ) / 2) * y < x * (kappa n + 1) := by
      have hdiv' :
          (m : ℝ) / 2 < (x * (kappa n + 1)) / y := by
        calc
          (m : ℝ) / 2 < x * ((kappa n + 1) / y) := hdiv
          _ = (x * (kappa n + 1)) / y := by ring
      exact (lt_div_iff₀ hy).mp hdiv'
    have him' : eta / 2 < y := by simpa only [y] using him
    nlinarith
  have hupperProduct :
      x * (kappa n + 1) <
        (2 / (NN : ℝ)) * (kappa n + 1) :=
    mul_lt_mul_of_pos_right hxUpper hkplus
  have hchain :
      (m : ℝ) * eta / 4 <
        (2 * (kappa n + 1)) / (NN : ℝ) := by
    calc
      (m : ℝ) * eta / 4 < x * (kappa n + 1) := hsource
      _ < (2 / (NN : ℝ)) * (kappa n + 1) := hupperProduct
      _ = (2 * (kappa n + 1)) / (NN : ℝ) := by ring
  have hmul :=
    (lt_div_iff₀ hNNR).mp hchain
  dsimp only [m, eta, NN] at hmul ⊢
  nlinarith

/-- Exact-ratio form of the linear no-go.  The conclusion concerns the intrinsic absolute-mass
ratio itself, not an arbitrarily chosen condition-number majorant. -/
theorem eventually_linear_exactSignedConditionNumber_of_screened_at_xi_zero
    {N : ℕ → ℕ} (hN : XiCTaylorSuperaccurateSchedule N)
    {h : ℕ → ℝ → ℝ} {F D : ℕ → ℂ}
    {sigma : ℂ} (hsigma : sigma.re < 1 / 2)
    (hzero : xi sigma = 0)
    (hsource : ∀ᶠ n : ℕ in atTop, SignedTailCompletionSourceAt
      (h n) (F n) (D n) (xiCTaylorAnisotropicCenteredPoint sigma n))
    (hscreen :
      XiCTaylorMovingPositiveTailCompletionGaugeChargeScreenedAt N F D sigma) :
    ∀ᶠ n : ℕ in atTop,
      ((((analyticOrderAt xi sigma).toNat : ℝ) *
          (1 / 2 - sigma.re)) / 8) *
          (((n + 1 : ℕ) : ℝ)) <
        signedTailCompletionConditionNumber (h n)
          (xiCTaylorAnisotropicCenteredPoint sigma n) + 1 := by
  have himTend : Tendsto
      (fun n : ℕ => (xiCTaylorAnisotropicCenteredPoint sigma n).im)
      atTop (nhds ((xiCTaylorCenteredPoint sigma).im)) :=
    Complex.continuous_im.continuousAt.tendsto.comp
      (tendsto_xiCTaylorAnisotropicCenteredPoint sigma)
  have hcenter : 0 < (xiCTaylorCenteredPoint sigma).im := by
    dsimp only [xiCTaylorCenteredPoint]
    rw [mul_im]
    simp only [sub_re, neg_re, I_re, neg_im, I_im]
    norm_num
    linarith
  have him : ∀ᶠ n : ℕ in atTop,
      0 < (xiCTaylorAnisotropicCenteredPoint sigma n).im :=
    himTend.eventually (eventually_gt_nhds hcenter)
  apply eventually_linear_conditionNumber_of_screened_at_xi_zero
    hN hsigma hzero
  · filter_upwards [hsource, him] with n hsn hzn
    exact hsn.toConditioned hzn
  · exact hscreen

end

end RHTower
