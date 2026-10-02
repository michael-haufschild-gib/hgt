import GaloisForLFunctions.RHTower.SoninTimeBandTraceCurrent
import GaloisForLFunctions.RHTower.SoninPrimePowerRegularization
import GaloisForLFunctions.HTGeometry.SchattenOneBanach

/-!
# Original linear-prime harmonic trace obstruction

The complete original correction response has a positive harmonic trace
coefficient. Its genuine Schatten-one family therefore cannot be summed
before joint prime–Gamma cancellation. The exact coefficient records the
scalar datum that such a source-derived cancellation must remove.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
open GaloisForLFunctions.HTGeometry ContinuousLinearMap
namespace RHTower

private def window (a c : ℝ) : ℝ :=
  (∫ x in Icc (-a) a, ∫ y in Icc (-a) a,
    Complex.exp (((2 * Real.pi * c * x * y : ℝ) : ℂ) * Complex.I)).re

private theorem window_eq (a c : ℝ) (ha : 0 < a) (hc : c ≠ 0) :
    window a c = (2 / (Real.pi * c)) *
      ∫ t in (0 : ℝ)..(2 * Real.pi * c * a ^ (2 : ℕ)), Real.sinc t := by
  rw [window, sonin_timeBand_window_eq_sine_current a c ha hc, Complex.ofReal_re]

private theorem sine_primitive_neg (T : ℝ) :
    (∫ t in (0 : ℝ)..(-T), Real.sinc t) = -(∫ t in (0 : ℝ)..T, Real.sinc t) := by
  have h := intervalIntegral.integral_comp_neg (fun t : ℝ => Real.sinc t)
    (a := (0 : ℝ)) (b := T)
  simp only [Real.sinc_neg, neg_zero] at h
  rw [intervalIntegral.integral_symm 0 (-T)] at h
  linarith

private theorem window_neg (a c : ℝ) (ha : 0 < a) (hc : c ≠ 0) :
    window a (-c) = window a c := by
  rw [window_eq a (-c) ha (neg_ne_zero.mpr hc), window_eq a c ha hc]
  rw [show 2 * Real.pi * -c * a ^ (2 : ℕ) = -(2 * Real.pi * c * a ^ (2 : ℕ)) by ring,
    sine_primitive_neg]
  ring

private theorem window_continuousAt_one (a : ℝ) (ha : 0 < a) :
    ContinuousAt (window a) 1 := by
  have hSi : Continuous (fun T : ℝ => ∫ t in (0 : ℝ)..T, Real.sinc t) :=
    intervalIntegral.continuous_primitive
      (fun a b => Real.continuous_sinc.intervalIntegrable a b) 0
  have h : ContinuousAt (fun c : ℝ => (2 / (Real.pi * c)) *
      ∫ t in (0 : ℝ)..(2 * Real.pi * c * a ^ (2 : ℕ)), Real.sinc t) 1 := by
    fun_prop (disch := positivity)
  apply h.congr_of_eventuallyEq
  filter_upwards [eventually_ne_nhds (by norm_num : (1 : ℝ) ≠ 0)] with c hc
  exact window_eq a c ha hc

private theorem window_scaled_tendsto (a : ℝ) (ha : 0 < a) :
    Tendsto (fun r : ℝ => 2 * (window a (1 - r⁻¹) + r * window a (r - 1)))
      atTop (𝓝 (2 * (window a 1 + 1))) := by
  have hshift : Tendsto (fun r : ℝ => r - 1) atTop atTop := by
    simpa only [sub_eq_add_neg, id_eq] using
      tendsto_atTop_add_const_right atTop (-1 : ℝ) tendsto_id
  have hnear : Tendsto (fun r : ℝ => window a (1 - r⁻¹)) atTop (𝓝 (window a 1)) := by
    apply (window_continuousAt_one a ha).tendsto.comp
    simpa using (tendsto_const_nhds.sub tendsto_inv_atTop_zero (a := (1 : ℝ)))
  have hratio : Tendsto (fun r : ℝ => r / (r - 1)) atTop (𝓝 (1 : ℝ)) := by
    have h := tendsto_const_nhds.add (tendsto_inv_atTop_zero.comp hshift) (a := (1 : ℝ))
    simp only [add_zero] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with r hr
    change 1 + (r - 1)⁻¹ = r / (r - 1)
    have hne : r - 1 ≠ 0 := (sub_pos.mpr hr).ne'
    field_simp [hne]
    ring
  have hfar : Tendsto (fun r : ℝ => r * window a (r - 1)) atTop (𝓝 (1 : ℝ)) := by
    have h := hratio.mul ((tendsto_sonin_timeBand_window_scaled a ha).comp hshift)
    simp only [one_mul] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with r hr
    change r / (r - 1) * ((r - 1) * window a (r - 1)) = _
    have hne : r - 1 ≠ 0 := (sub_pos.mpr hr).ne'
    field_simp [hne]
  exact tendsto_const_nhds.mul (hnear.add hfar)

/-- Original linear Euler coefficient applied to the complete Sonin correction
response, in the genuine trace-norm carrier. -/
def soninLinearPrimeNuclearSource (a : ℝ) (ha : 0 < a) (p : Nat.Primes) :
    SchattenOneOperator SoninL2 :=
  ⟨(((Real.sqrt (p : ℝ))⁻¹ : ℝ) : ℂ) •
      centralSoninCornerCorrectionResponse a (soninPrimeDilationSignal p),
    memSchattenClass_one_smul
      (centralSoninCornerCorrectionResponse_mem_timeBandIdeal a ha
        (soninPrimeDilationSignal p)).memSchattenClass_one _⟩

/-- Canonical harmonic trace coefficient of the original linear-prime source. -/
def soninLinearPrimeTraceCoefficient (a : ℝ) : ℝ :=
  2 * ((∫ x in Icc (-a) a, ∫ y in Icc (-a) a,
    Complex.exp (((2 * Real.pi * x * y : ℝ) : ℂ) * Complex.I)).re + 1)

/-- The linear-prime harmonic coefficient is strictly positive at every
positive aperture. -/
theorem soninLinearPrimeTraceCoefficient_pos (a : ℝ) (ha : 0 < a) :
    0 < soninLinearPrimeTraceCoefficient a := by
  have h := sonin_timeBand_window_re_pos a 1 ha zero_lt_one
  simp only [mul_one] at h
  unfold soninLinearPrimeTraceCoefficient
  linarith

private theorem linear_prime_trace_normalized (a : ℝ) (ha : 0 < a) (p : Nat.Primes) :
    (p : ℝ) * (opTrace (soninLinearPrimeNuclearSource a ha p).val).re =
      2 * (window a (1 - (p : ℝ)⁻¹) + (p : ℝ) * window a ((p : ℝ) - 1)) := by
  have hp : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.prop.one_lt
  have hp0 := zero_lt_one.trans hp
  have hs : Real.sqrt (p : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hp0).ne'
  have hscale : (p : ℝ) * (Real.sqrt (p : ℝ))⁻¹ = Real.sqrt (p : ℝ) := by
    field_simp [hs]
    nlinarith [Real.sq_sqrt hp0.le]
  have hprod := sqrt_mul_sqrt_inv (p : ℝ) hp0
  have hsq := Real.sq_sqrt hp0.le
  change (p : ℝ) * (opTrace ((((Real.sqrt (p : ℝ))⁻¹ : ℝ) : ℂ) •
    centralSoninCornerCorrectionResponse a (soninPrimeDilationSignal p))).re = _
  rw [opTrace_smul]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [soninPrimeDilationSignal,
    re_opTrace_centralSoninCornerCorrectionResponse_dilationSum a (p : ℝ) ha hp]
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  change (p : ℝ) * ((Real.sqrt (p : ℝ))⁻¹ *
    (2 * (Real.sqrt (p : ℝ)⁻¹ * window a (1 - (p : ℝ)⁻¹) +
      Real.sqrt (p : ℝ) * window a (1 - (p : ℝ))))) = _
  rw [← mul_assoc, hscale,
    show 1 - (p : ℝ) = -((p : ℝ) - 1) by ring,
    window_neg a _ ha (sub_pos.mpr hp).ne']
  calc
    _ = 2 * ((Real.sqrt (p : ℝ) * Real.sqrt (p : ℝ)⁻¹) *
        window a (1 - (p : ℝ)⁻¹) +
        (Real.sqrt (p : ℝ)) ^ (2 : ℕ) * window a ((p : ℝ) - 1)) := by ring
    _ = _ := by rw [hprod, hsq, one_mul]

private theorem prime_value_tendsto :
    Tendsto (fun p : Nat.Primes => (p : ℝ)) cofinite atTop := by
  have h : Tendsto (fun p : Nat.Primes => (p : ℕ)) cofinite atTop := by
    rw [← Nat.cofinite_eq_atTop]
    exact Subtype.val_injective.tendsto_cofinite
  exact tendsto_natCast_atTop_atTop.comp h

/-- Exact harmonic asymptotic of the complete original linear-prime source.
Both dilation directions survive: the coefficient is `2 (Phi_a(1) + 1)`. -/
theorem tendsto_soninLinearPrime_trace_harmonic (a : ℝ) (ha : 0 < a) :
    Tendsto (fun p : Nat.Primes =>
      (p : ℝ) * (opTrace (soninLinearPrimeNuclearSource a ha p).val).re)
      cofinite (𝓝 (soninLinearPrimeTraceCoefficient a)) := by
  have h := (window_scaled_tendsto a ha).comp prime_value_tendsto
  have hcoef : 2 * (window a 1 + 1) = soninLinearPrimeTraceCoefficient a := by
    simp only [window, mul_one, soninLinearPrimeTraceCoefficient]
  rw [hcoef] at h
  exact h.congr fun p => (linear_prime_trace_normalized a ha p).symm

private def traceReader : SchattenOneOperator SoninL2 →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun T => opTrace T.val
      map_add' := fun S T => opTrace_add_of_memSchattenClass_one S.property T.property
      map_smul' := fun c T => by
        change opTrace (c • T.val) = c * opTrace T.val
        exact opTrace_smul c T.val }
    1 (fun T => by
      change ‖opTrace T.val‖ ≤ 1 * traceNorm SoninL2 T.val
      rw [one_mul]
      exact norm_opTrace_le_traceNorm T.property)

/-- Raw original linear-prime traces cannot be summed. The obstruction is the
positive harmonic coefficient of the actual response, not coefficient energy. -/
theorem not_summable_soninLinearPrime_trace (a : ℝ) (ha : 0 < a) :
    ¬ Summable (fun p : Nat.Primes =>
      (opTrace (soninLinearPrimeNuclearSource a ha p).val).re) := by
  intro h
  let K := soninLinearPrimeTraceCoefficient a
  have hK : 0 < K := soninLinearPrimeTraceCoefficient_pos a ha
  have hev : ∀ᶠ p : Nat.Primes in cofinite, K / 2 <
      (p : ℝ) * (opTrace (soninLinearPrimeNuclearSource a ha p).val).re :=
    (tendsto_soninLinearPrime_trace_harmonic a ha).eventually
      (eventually_gt_nhds (by dsimp [K]; linarith : K / 2 < soninLinearPrimeTraceCoefficient a))
  have hrecip : Summable (fun p : Nat.Primes => (1 / (p : ℝ))) := by
    apply Summable.of_norm_bounded_eventually (h.mul_left (2 / K))
    filter_upwards [hev] with p hp
    have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.prop.pos
    rw [Real.norm_eq_abs, abs_of_pos (div_pos zero_lt_one hp0)]
    apply (div_le_iff₀ hp0).mpr
    calc
      1 = K / K := (div_self hK.ne').symm
      _ ≤ (2 * ((p : ℝ) * (opTrace (soninLinearPrimeNuclearSource a ha p).val).re)) / K :=
        div_le_div_of_nonneg_right (by linarith) hK.le
      _ = _ := by ring
  exact Nat.Primes.not_summable_one_div hrecip

/-- No unconditional sum of the raw original linear-prime responses exists in
Schatten-1. A joint source must cancel their canonical harmonic trace term. -/
theorem not_summable_soninLinearPrimeNuclearSource (a : ℝ) (ha : 0 < a) :
    ¬ Summable (soninLinearPrimeNuclearSource a ha) := by
  intro h
  exact not_summable_soninLinearPrime_trace a ha
    (Complex.reCLM.summable (traceReader.summable h))

end RHTower
