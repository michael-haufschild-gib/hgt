import GaloisForLFunctions.RHTower.ThetaTailCauchyFirstCorrection
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspSchwartz

/-!
# Endpoint commutators of the literal theta tail kernel

Both signs of the endpoint-commutator remainder have strictly negative
two-point packets for all sufficiently large common translations. The full
theta tail kernel is positive definite on those same nodes. The proof uses
a new first correction for the zeroth orbit moment of the complete source.

This excludes the two auxiliary CP-3 comparisons, not the full-kernel
positivity conjecture or RH.
-/

open Filter Topology MeasureTheory Set
noncomputable section
namespace RHTower.ThetaTailEndpoint
open ThetaTailCauchy ThetaTailFirstCorrection

/-- Zeroth paired tail moment, with a moving lower cut. -/
def tailMass (x y r : ℝ) : ℝ := ∫ t in Ioi r, pairProduct x y t

/-- First paired tail moment measured from its lower cut. -/
def tailMoment (x y r : ℝ) : ℝ :=
  ∫ t in Ioi r, (t-r)*pairProduct x y t

private theorem pair_continuous (x y : ℝ) : Continuous (pairProduct x y) :=
  (contDiff_thetaCuspFullSource.continuous.comp
    (continuous_const.add continuous_id)).mul
    (contDiff_thetaCuspFullSource.continuous.comp (continuous_const.add continuous_id))

private theorem pair_ne_zero (x y r : ℝ) : pairProduct x y r ≠ 0 :=
  mul_ne_zero (HedenmalmThetaSource.thetaCuspFullSource_pos _).ne'
    (HedenmalmThetaSource.thetaCuspFullSource_pos _).ne'

private theorem pair_integrable (x y : ℝ) : Integrable (pairProduct x y) := by
  have hx : Integrable (fun r : ℝ => thetaCuspFullSource (x+r)) := by
    simpa only [thetaCuspSchwartzReal_apply, add_comm] using
      thetaCuspSchwartzReal.integrable.comp_add_right x
  exact hx.mul_bdd
    (contDiff_thetaCuspFullSource.continuous.comp
      (continuous_const.add continuous_id)).aestronglyMeasurable
    (Eventually.of_forall fun r => thetaCuspSchwartzReal.norm_le_seminorm ℝ (y+r))

theorem tailMass_hasDerivAt (x y r : ℝ) :
    HasDerivAt (tailMass x y) (-pairProduct x y r) r := by
  have hf := pair_integrable x y
  have hc := pair_continuous x y
  have heq : tailMass x y = fun u => tailMass x y 0 - ∫ t in (0:ℝ)..u,
      pairProduct x y t := by
    funext u
    have h := intervalIntegral.integral_interval_add_Ioi
      (hf.integrableOn (s := Ioi 0)) (hf.integrableOn (s := Ioi u))
    dsimp [tailMass]
    linarith
  rw [heq]
  exact (intervalIntegral.integral_hasDerivAt_right hf.intervalIntegrable
    hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt).const_sub _

theorem tailMass_limit (x y : ℝ) : Tendsto (tailMass x y) atTop (𝓝 0) :=
  tendsto_integral_Ioi_zero tendsto_id

private theorem exp_limit : Tendsto (fun r : ℝ => Real.exp (-2*r)) atTop (𝓝 0) :=
  PositiveCoshEdge.exp_neg_rate (c := 2) (by norm_num)

/-- Exact first correction for the zeroth moment of the complete theta source. -/
theorem tailMass_first_correction_limit (x y : ℝ) :
    Tendsto (fun r : ℝ =>
      (tailMass x y r/baseNormalizer x y r-1/(2*pairScale x y))/Real.exp (-2*r))
      atTop (𝓝 (7/(4*pairScale x y^2))) := by
  let A := pairScale x y
  let E : ℝ → ℝ := fun r => Real.exp (-2*r)
  let N : ℝ → ℝ := fun r => tailMass x y r-baseNormalizer x y r/(2*A)
  let G : ℝ → ℝ := fun r => E r*baseNormalizer x y r
  have hA : A ≠ 0 := (pairScale_pos x y).ne'
  have hN (r : ℝ) : HasDerivAt N
      (-pairProduct x y r*(baseSlope x y r+2*A)/(2*A)) r := by
    convert (tailMass_hasDerivAt x y r).sub
      ((baseNormalizer_hasDerivAt x y r).div_const (2*A)) using 1 <;>
      first | rfl | (field_simp [hA]; ring)
  have hG (r : ℝ) : HasDerivAt G
      (E r*pairProduct x y r*(baseSlope x y r-2*E r)) r := by
    have he : HasDerivAt E (-2*E r) r := by
      convert ((hasDerivAt_id r).const_mul (-2)).exp using 1 <;> simp [E, mul_comm]
    convert he.mul (baseNormalizer_hasDerivAt x y r) using 1 <;>
      first | rfl | (simp only [E, baseNormalizer]; ring)
  have hs : Tendsto (fun r => baseSlope x y r-2*E r)
      atTop (𝓝 (-2*A)) := by
    simpa [E] using (baseSlope_limit x y).sub (exp_limit.const_mul 2)
  have hsne : ∀ᶠ r in atTop, baseSlope x y r-2*E r ≠ 0 :=
    hs.eventually_ne (by exact mul_ne_zero (by norm_num) hA)
  have hGne : ∀ᶠ r in atTop,
      E r*pairProduct x y r*(baseSlope x y r-2*E r) ≠ 0 := by
    filter_upwards [hsne] with r hr
    exact mul_ne_zero (mul_ne_zero (Real.exp_ne_zero _) (pair_ne_zero x y r)) hr
  have hN0 : Tendsto N atTop (𝓝 0) := by
    simpa [N] using (tailMass_limit x y).sub ((baseNormalizer_limit x y).div_const (2*A))
  have hG0 : Tendsto G atTop (𝓝 0) := by
    simpa [G, E] using exp_limit.mul (baseNormalizer_limit x y)
  have hratio : Tendsto (fun r =>
      (-pairProduct x y r*(baseSlope x y r+2*A)/(2*A)) /
      (E r*pairProduct x y r*(baseSlope x y r-2*E r)))
      atTop (𝓝 (7/(4*A^2))) := by
    have h := ((baseSlope_error_div_exp_limit x y).neg.div_const (2*A)).div hs
      (mul_ne_zero (by norm_num) hA)
    have hv : (-7/(2*A))/(-2*A) = 7/(4*A^2) := by field_simp; ring
    rw [hv] at h
    apply h.congr'
    filter_upwards [hsne] with r hr
    dsimp [E, A] at *
    field_simp [pair_ne_zero x y r, Real.exp_ne_zero, hr]
  have h := HasDerivAt.lhopital_zero_atTop
    (Eventually.of_forall hN) (Eventually.of_forall hG) hGne hN0 hG0 hratio
  apply h.congr'
  apply Eventually.of_forall
  intro r
  dsimp [N, G, E, A, baseNormalizer]
  field_simp [pair_ne_zero x y r, Real.exp_ne_zero]

theorem tailMass_normalized_limit (x y : ℝ) :
    Tendsto (fun r => tailMass x y r/baseNormalizer x y r)
      atTop (𝓝 (1/(2*pairScale x y))) := by
  have h := ((tailMass_first_correction_limit x y).mul exp_limit).add_const
    (1/(2*pairScale x y))
  convert h using 1
  · ext r
    field_simp [Real.exp_ne_zero]
    ring
  · simp

private theorem moment_integrable (x y r : ℝ) :
    Integrable (fun t => (t-r)*pairProduct x y t) := by
  have h := ((integrable_thetaTailCommonTranslationIntegrand x y).sub
    ((pair_integrable x y).const_mul (x+y+2*r))).const_mul (1/2 : ℝ)
  refine h.congr (Eventually.of_forall fun t => ?_)
  simp only [Pi.sub_apply, thetaTailCommonTranslationIntegrand, pairProduct]
  ring

/-- The full kernel keeps both orbit moments with their exact coefficients. -/
theorem kernel_eq_moments (x y r : ℝ) :
    thetaTailFirstMomentKernel (x+r) (y+r) =
      (x+y+2*r)*tailMass x y r+2*tailMoment x y r := by
  rw [thetaTailFirstMomentKernel_commonShift_eq_tail]
  have heq (t : ℝ) : thetaTailCommonTranslationIntegrand x y t =
      (x+y+2*r)*pairProduct x y t+2*((t-r)*pairProduct x y t) := by
    simp only [thetaTailCommonTranslationIntegrand, pairProduct]
    ring
  simp_rw [heq]
  rw [integral_add ((pair_integrable x y).const_mul _).integrableOn
    ((moment_integrable x y r).const_mul _).integrableOn]
  simp only [integral_const_mul, tailMass, tailMoment]

/-- First orbit moments are negligible at the endpoint-commutator scale. -/
theorem tailMoment_scaled_limit (x y : ℝ) :
    Tendsto (fun r => r*tailMoment x y r/baseNormalizer x y r)
      atTop (𝓝 0) := by
  have h1 := (PositiveCoshEdge.scaled_power_limit (c := 2) (by norm_num) 1).mul
    (tailMass_first_correction_limit x y)
  have h2 := (PositiveCoshEdge.scaled_power_limit (c := 2) (by norm_num) 2).mul
    (tailMass_first_correction_limit x y)
  have hH := (PositiveCoshEdge.scaled_power_limit (c := 2) (by norm_num) 2).mul
    (kernel_first_correction_limit x y)
  have h := ((hH.sub (h2.const_mul 2)).sub (h1.const_mul (x+y))).div_const 2
  apply (show Tendsto _ atTop (𝓝 (0:ℝ)) from by simpa using h).congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with r hr
  have hD : baseNormalizer x y r ≠ 0 :=
    mul_ne_zero (Real.exp_ne_zero _) (pair_ne_zero x y r)
  have he := kernel_eq_moments x y r
  rw [he]
  field_simp [Real.exp_ne_zero, hD, hr.ne']
  ring


private theorem sqrt_gap_lower {r : ℝ} (hr : 1 ≤ r) :
    (1/6 : ℝ) ≤ r*(Real.sqrt r-Real.sqrt (1+r))^2 := by
  have hu := Real.sq_sqrt (show 0 ≤ r by linarith)
  have hv := Real.sq_sqrt (show 0 ≤ 1+r by linarith)
  have hden : (Real.sqrt r+Real.sqrt (1+r))^2 ≤ 6*r := by
    nlinarith [sq_nonneg (Real.sqrt r-Real.sqrt (1+r))]
  have hprod : (Real.sqrt r-Real.sqrt (1+r))^2*
      (Real.sqrt r+Real.sqrt (1+r))^2 = 1 := by
    calc
      _ = ((Real.sqrt r)^2-(Real.sqrt (1+r))^2)^2 := by ring
      _ = 1 := by rw [hu, hv]; ring
  have h := mul_le_mul_of_nonneg_left hden
    (sq_nonneg (Real.sqrt r-Real.sqrt (1+r)))
  nlinarith

private def endpointCross (r : ℝ) : ℝ :=
  r*(Real.sqrt r-Real.sqrt (1+r))^2*tailMass 0 1 r/baseNormalizer 0 1 r

private theorem endpointCross_lower :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ r : ℝ in atTop, c ≤ endpointCross r := by
  have hA := pairScale_pos 0 1
  let d := 1/(4*pairScale 0 1)
  have hd : 0 < d := by dsimp [d]; positivity
  have hlt : d < 1/(2*pairScale 0 1) := by
    dsimp [d]
    apply (div_lt_div_iff₀ (by positivity) (by positivity)).2
    nlinarith [pairScale_pos 0 1]
  have hm := (tailMass_normalized_limit 0 1).eventually_const_lt hlt
  refine ⟨d/6, by positivity, ?_⟩
  filter_upwards [hm, eventually_ge_atTop (1:ℝ)] with r hr hrg
  have hs := sqrt_gap_lower hrg
  calc
    d/6 = (1/6)*d := by ring
    _ ≤ (r*(Real.sqrt r-Real.sqrt (1+r))^2)*
        (tailMass 0 1 r/baseNormalizer 0 1 r) :=
      mul_le_mul hs hr.le hd.le (by linarith)
    _ = endpointCross r := by unfold endpointCross; ring

/-- Endpoint double-commutator remainder; `ε = 1` is the corrected CP-3 comparison. -/
def endpointRemainder (ε x y r : ℝ) : ℝ :=
  2*tailMoment x y r+
    ε*(Real.sqrt (x+r)-Real.sqrt (y+r))^2*tailMass x y r

private theorem tailMass_comm (x y r : ℝ) : tailMass x y r = tailMass y x r := by
  unfold tailMass
  apply integral_congr_ae
  filter_upwards with t
  exact mul_comm _ _

private theorem tailMoment_comm (x y r : ℝ) : tailMoment x y r = tailMoment y x r := by
  unfold tailMoment
  apply integral_congr_ae
  filter_upwards with t
  simp only [pairProduct]
  ring

theorem tailMass_commonShift (x y r : ℝ) :
    tailMass (x+r) (y+r) 0 = tailMass x y r := by
  unfold tailMass
  rw [← setIntegral_Ioi_zero_comp_add_right (pairProduct x y) r]
  apply integral_congr_ae
  filter_upwards with t
  simp only [pairProduct]
  rw [show x+r+t = x+(t+r) by ring, show y+r+t = y+(t+r) by ring]

theorem tailMoment_commonShift (x y r : ℝ) :
    tailMoment (x+r) (y+r) 0 = tailMoment x y r := by
  unfold tailMoment
  rw [← setIntegral_Ioi_zero_comp_add_right (fun t => (t-r)*pairProduct x y t) r]
  apply integral_congr_ae
  filter_upwards with t
  simp only [sub_zero, add_sub_cancel_right, pairProduct]
  rw [show x+r+t = x+(t+r) by ring, show y+r+t = y+(t+r) by ring]

theorem endpointRemainder_commonShift (ε x y r : ℝ) :
    endpointRemainder ε (x+r) (y+r) 0 = endpointRemainder ε x y r := by
  simp only [endpointRemainder, add_zero, tailMass_commonShift, tailMoment_commonShift]

private def nodes : Fin 2 → ℝ := ![0, 1]

/-- Coefficients of the literal two-node test packet. -/
def packetCoefficients (σ r : ℝ) : Fin 2 → ℝ :=
  ![1/thetaCuspFullSource r, σ/thetaCuspFullSource (1+r)]

/-- The actual quadratic form, before any positive rescaling. -/
def packetForm (ε σ r : ℝ) : ℝ :=
  ∑ i : Fin 2, ∑ j : Fin 2,
    packetCoefficients σ r i*packetCoefficients σ r j*
      endpointRemainder ε (nodes i) (nodes j) r

private def momentCombo (σ r : ℝ) : ℝ :=
  2*(r*tailMoment 0 0 r/baseNormalizer 0 0 r)+
  (4*σ)*(r*tailMoment 0 1 r/baseNormalizer 0 1 r)+
  (2*σ^2)*(r*tailMoment 1 1 r/baseNormalizer 1 1 r)

private theorem momentCombo_limit (σ : ℝ) :
    Tendsto (momentCombo σ) atTop (𝓝 0) := by
  unfold momentCombo
  simpa only [mul_zero, add_zero] using
    (((tailMoment_scaled_limit 0 0).const_mul 2).add
      ((tailMoment_scaled_limit 0 1).const_mul (4*σ))).add
      ((tailMoment_scaled_limit 1 1).const_mul (2*σ^2))

private theorem packet_scale_identity (ε σ r : ℝ) :
    r/Real.exp (-2*r)*packetForm ε σ r =
      momentCombo σ r+(2*σ*ε)*endpointCross r := by
  simp only [packetForm, Fin.sum_univ_two, packetCoefficients, nodes,
    Matrix.cons_val_zero, Matrix.cons_val_one, endpointRemainder, zero_add]
  rw [tailMoment_comm 1 0 r, tailMass_comm 1 0 r]
  simp only [sub_self, zero_pow (by norm_num : (2:ℕ) ≠ 0), mul_zero, zero_mul, add_zero]
  dsimp only [momentCombo, endpointCross, baseNormalizer, pairProduct]
  simp only [zero_add]
  field_simp [Real.exp_ne_zero,
    (HedenmalmThetaSource.thetaCuspFullSource_pos r).ne',
    (HedenmalmThetaSource.thetaCuspFullSource_pos (1+r)).ne']
  ring

/-- Both signs of the proposed endpoint comparison fail on literal theta packets. -/
theorem endpoint_comparisons_eventually_negative :
    ∀ᶠ r : ℝ in atTop, packetForm (-1) 1 r < 0 ∧ packetForm 1 (-1) r < 0 := by
  obtain ⟨c, hc, hcross⟩ := endpointCross_lower
  filter_upwards [hcross, (momentCombo_limit 1).eventually_lt_const hc,
    (momentCombo_limit (-1)).eventually_lt_const hc,
    eventually_gt_atTop (0:ℝ)] with r hcross hp hn hr
  have hscale : 0 < r/Real.exp (-2*r) := div_pos hr (Real.exp_pos _)
  have hp' := packet_scale_identity (-1) 1 r
  have hn' := packet_scale_identity 1 (-1) r
  constructor
  · by_contra h
    have := mul_nonneg hscale.le (le_of_not_gt h)
    nlinarith
  · by_contra h
    have := mul_nonneg hscale.le (le_of_not_gt h)
    nlinarith

/-- The full kernel stays positive on the same packets that disprove both comparisons. -/
theorem full_kernel_positive_with_negative_endpoint_comparisons :
    ∀ᶠ r : ℝ in atTop, 0 < r ∧ (sourceMatrix ![0,1] r).PosDef ∧
      packetForm (-1) 1 r < 0 ∧ packetForm 1 (-1) r < 0 := by
  have hi : Function.Injective (![0,1] : Fin 2 → ℝ) := by
    intro i j h
    fin_cases i <;> fin_cases j <;> norm_num at *
  filter_upwards [sourceMatrix_eventually_posDef ![0,1] hi,
    endpoint_comparisons_eventually_negative, eventually_gt_atTop (0:ℝ)] with r hp hn hr
  exact ⟨hr, hp, hn⟩

end RHTower.ThetaTailEndpoint
