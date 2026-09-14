import GaloisForLFunctions.RHTower.PrimeArchObservableCarrierQuantization
import GaloisForLFunctions.RHTower.XiCTaylorThetaTailTelescope
import GaloisForLFunctions.HTGeometry.ProjectiveHorizonLogPotential

/-!
# Product-kernel form of the theta third cumulant

Independent enclosures of the first four theta moments discard the cancellation in the
third-cumulant numerator. This module represents that numerator as one signed integral over a
triple product measure. The existing sixth-trace cap is then exactly equivalent to a single
product-kernel inequality, preserving the cancellation for subsequent analytic estimates.
-/

open MeasureTheory
open Polynomial

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

/-- Symmetric kernel whose product expectation is
`m₀² m₃ - 15 m₀ m₁ m₂ + 30 m₁³`. -/
def signedThirdEvenCumulantKernel (p : ℝ × (ℝ × ℝ)) : ℝ :=
  (p.1 ^ 3 + p.2.1 ^ 3 + p.2.2 ^ 3) / 3 -
    (5 / 2 : ℝ) *
      (p.1 ^ 2 * p.2.1 + p.1 ^ 2 * p.2.2 +
        p.2.1 ^ 2 * p.1 + p.2.1 ^ 2 * p.2.2 +
        p.2.2 ^ 2 * p.1 + p.2.2 ^ 2 * p.2.1) +
    30 * p.1 * p.2.1 * p.2.2

/-- Exact product-integral identity for the signed third-cumulant kernel. -/
theorem integral_signedThirdEvenCumulantKernel
    (μ : Measure ℝ) [SFinite μ]
    (h0 : Integrable (fun _ : ℝ => (1 : ℝ)) μ)
    (h1 : Integrable (fun x : ℝ => x) μ)
    (h2 : Integrable (fun x : ℝ => x ^ 2) μ)
    (h3 : Integrable (fun x : ℝ => x ^ 3) μ) :
    (∫ p : ℝ × (ℝ × ℝ), signedThirdEvenCumulantKernel p ∂μ.prod (μ.prod μ)) =
      (∫ _ : ℝ, (1 : ℝ) ∂μ) ^ 2 * (∫ x : ℝ, x ^ 3 ∂μ) -
        15 * (∫ _ : ℝ, (1 : ℝ) ∂μ) * (∫ x : ℝ, x ∂μ) *
          (∫ x : ℝ, x ^ 2 ∂μ) +
        30 * (∫ x : ℝ, x ∂μ) ^ 3 := by
  let f : ℕ → ℕ → ℕ → ℝ × (ℝ × ℝ) → ℝ := fun i j k p =>
    p.1 ^ i * (p.2.1 ^ j * p.2.2 ^ k)
  have hf (i j k : ℕ)
      (hi : Integrable (fun x : ℝ => x ^ i) μ)
      (hj : Integrable (fun x : ℝ => x ^ j) μ)
      (hk : Integrable (fun x : ℝ => x ^ k) μ) :
      Integrable (f i j k) (μ.prod (μ.prod μ)) := by
    exact hi.mul_prod (hj.mul_prod hk)
  have hfi (i j k : ℕ) :
      (∫ p : ℝ × (ℝ × ℝ), f i j k p ∂μ.prod (μ.prod μ)) =
        (∫ x : ℝ, x ^ i ∂μ) * (∫ x : ℝ, x ^ j ∂μ) *
          (∫ x : ℝ, x ^ k ∂μ) := by
    calc
      (∫ p : ℝ × (ℝ × ℝ), f i j k p ∂μ.prod (μ.prod μ)) =
          (∫ x : ℝ, x ^ i ∂μ) *
            (∫ q : ℝ × ℝ, q.1 ^ j * q.2 ^ k ∂μ.prod μ) := by
              simpa only [f] using
                (MeasureTheory.integral_prod_mul
                  (μ := μ) (ν := μ.prod μ)
                  (fun x : ℝ => x ^ i)
                  (fun q : ℝ × ℝ => q.1 ^ j * q.2 ^ k))
      _ = (∫ x : ℝ, x ^ i ∂μ) * (∫ x : ℝ, x ^ j ∂μ) *
          (∫ x : ℝ, x ^ k ∂μ) := by
            rw [MeasureTheory.integral_prod_mul
              (μ := μ) (ν := μ) (fun x : ℝ => x ^ j) (fun x : ℝ => x ^ k)]
            ring
  have hp0 : (fun x : ℝ => x ^ 0) = fun _ : ℝ => (1 : ℝ) := by
    funext x
    simp
  have hf0 : Integrable (fun x : ℝ => x ^ 0) μ := by simpa only [hp0] using h0
  have hf1 : Integrable (fun x : ℝ => x ^ 1) μ := by simpa using h1
  let A := fun p => f 3 0 0 p + f 0 3 0 p + f 0 0 3 p
  let B := fun p =>
    f 2 1 0 p + f 2 0 1 p + f 1 2 0 p +
      f 0 2 1 p + f 1 0 2 p + f 0 1 2 p
  let C := f 1 1 1
  have hA : Integrable A (μ.prod (μ.prod μ)) :=
    ((hf 3 0 0 h3 hf0 hf0).add (hf 0 3 0 hf0 h3 hf0)).add
      (hf 0 0 3 hf0 hf0 h3)
  have hB : Integrable B (μ.prod (μ.prod μ)) :=
    (((((hf 2 1 0 h2 hf1 hf0).add (hf 2 0 1 h2 hf0 hf1)).add
      (hf 1 2 0 hf1 h2 hf0)).add (hf 0 2 1 hf0 h2 hf1)).add
      (hf 1 0 2 hf1 hf0 h2)).add (hf 0 1 2 hf0 hf1 h2)
  have hC : Integrable C (μ.prod (μ.prod μ)) := hf 1 1 1 hf1 hf1 hf1
  have integral_add_apply {g h : ℝ × (ℝ × ℝ) → ℝ}
      (hg : Integrable g (μ.prod (μ.prod μ)))
      (hh : Integrable h (μ.prod (μ.prod μ))) :
      (∫ p, g p + h p ∂μ.prod (μ.prod μ)) =
        (∫ p, g p ∂μ.prod (μ.prod μ)) + ∫ p, h p ∂μ.prod (μ.prod μ) := by
    simpa only [Pi.add_apply] using integral_add hg hh
  have integral_sub_apply {g h : ℝ × (ℝ × ℝ) → ℝ}
      (hg : Integrable g (μ.prod (μ.prod μ)))
      (hh : Integrable h (μ.prod (μ.prod μ))) :
      (∫ p, g p - h p ∂μ.prod (μ.prod μ)) =
        (∫ p, g p ∂μ.prod (μ.prod μ)) - ∫ p, h p ∂μ.prod (μ.prod μ) := by
    simpa only [Pi.sub_apply] using integral_sub hg hh
  have integral_const_mul_apply (c : ℝ) {g : ℝ × (ℝ × ℝ) → ℝ} :
      (∫ p, c * g p ∂μ.prod (μ.prod μ)) =
        c * ∫ p, g p ∂μ.prod (μ.prod μ) := by
    simpa only [Pi.smul_apply, smul_eq_mul] using
      (integral_const_mul c g)
  have hAi : (∫ p, A p ∂μ.prod (μ.prod μ)) =
      3 * (∫ _ : ℝ, (1 : ℝ) ∂μ) ^ 2 * (∫ x, x ^ 3 ∂μ) := by
    calc
      (∫ p, A p ∂μ.prod (μ.prod μ)) =
          (∫ p, f 3 0 0 p + f 0 3 0 p ∂μ.prod (μ.prod μ)) +
            ∫ p, f 0 0 3 p ∂μ.prod (μ.prod μ) := by
              dsimp only [A]
              exact integral_add
                ((hf 3 0 0 h3 hf0 hf0).add (hf 0 3 0 hf0 h3 hf0))
                (hf 0 0 3 hf0 hf0 h3)
      _ = ((∫ p, f 3 0 0 p ∂μ.prod (μ.prod μ)) +
            ∫ p, f 0 3 0 p ∂μ.prod (μ.prod μ)) +
            ∫ p, f 0 0 3 p ∂μ.prod (μ.prod μ) := by
              rw [integral_add (hf 3 0 0 h3 hf0 hf0) (hf 0 3 0 hf0 h3 hf0)]
      _ = _ := by rw [hfi, hfi, hfi, hp0]; ring
  have hBi : (∫ p, B p ∂μ.prod (μ.prod μ)) =
      6 * (∫ _ : ℝ, (1 : ℝ) ∂μ) * (∫ x, x ∂μ) *
        (∫ x, x ^ 2 ∂μ) := by
    have h21 := hf 2 1 0 h2 hf1 hf0
    have h20 := hf 2 0 1 h2 hf0 hf1
    have h12 := hf 1 2 0 hf1 h2 hf0
    have h02 := hf 0 2 1 hf0 h2 hf1
    have h10 := hf 1 0 2 hf1 hf0 h2
    have h01 := hf 0 1 2 hf0 hf1 h2
    calc
      (∫ p, B p ∂μ.prod (μ.prod μ)) =
          (∫ p, ((((f 2 1 0 p + f 2 0 1 p) + f 1 2 0 p) + f 0 2 1 p) +
            f 1 0 2 p) ∂μ.prod (μ.prod μ)) +
            ∫ p, f 0 1 2 p ∂μ.prod (μ.prod μ) := by
              simpa only [B, Pi.add_apply] using
                (integral_add_apply
                  (h21.add h20 |>.add h12 |>.add h02 |>.add h10) h01)
      _ = ((∫ p, (((f 2 1 0 p + f 2 0 1 p) + f 1 2 0 p) + f 0 2 1 p)
              ∂μ.prod (μ.prod μ)) +
            ∫ p, f 1 0 2 p ∂μ.prod (μ.prod μ)) +
            ∫ p, f 0 1 2 p ∂μ.prod (μ.prod μ) := by
              congr 1
              simpa only [Pi.add_apply] using
                (integral_add_apply (h21.add h20 |>.add h12 |>.add h02) h10)
      _ = (((∫ p, ((f 2 1 0 p + f 2 0 1 p) + f 1 2 0 p)
                ∂μ.prod (μ.prod μ)) +
              ∫ p, f 0 2 1 p ∂μ.prod (μ.prod μ)) +
            ∫ p, f 1 0 2 p ∂μ.prod (μ.prod μ)) +
            ∫ p, f 0 1 2 p ∂μ.prod (μ.prod μ) := by
              congr 2
              simpa only [Pi.add_apply] using
                (integral_add_apply (h21.add h20 |>.add h12) h02)
      _ = ((((∫ p, (f 2 1 0 p + f 2 0 1 p) ∂μ.prod (μ.prod μ)) +
              ∫ p, f 1 2 0 p ∂μ.prod (μ.prod μ)) +
            ∫ p, f 0 2 1 p ∂μ.prod (μ.prod μ)) +
            ∫ p, f 1 0 2 p ∂μ.prod (μ.prod μ)) +
            ∫ p, f 0 1 2 p ∂μ.prod (μ.prod μ) := by
              congr 3
              simpa only [Pi.add_apply] using
                (integral_add_apply (h21.add h20) h12)
      _ = (((((∫ p, f 2 1 0 p ∂μ.prod (μ.prod μ)) +
            ∫ p, f 2 0 1 p ∂μ.prod (μ.prod μ)) +
            ∫ p, f 1 2 0 p ∂μ.prod (μ.prod μ)) +
            ∫ p, f 0 2 1 p ∂μ.prod (μ.prod μ)) +
            ∫ p, f 1 0 2 p ∂μ.prod (μ.prod μ)) +
            ∫ p, f 0 1 2 p ∂μ.prod (μ.prod μ) := by
              congr 4
              simpa only [Pi.add_apply] using (integral_add_apply h21 h20)
      _ = _ := by
        rw [hfi, hfi, hfi, hfi, hfi, hfi, hp0]
        simp only [pow_one]
        ring
  have hCi : (∫ p, C p ∂μ.prod (μ.prod μ)) =
      (∫ x, x ∂μ) ^ 3 := by
    rw [show (∫ p, C p ∂μ.prod (μ.prod μ)) =
        (∫ x, x ^ 1 ∂μ) * (∫ x, x ^ 1 ∂μ) * (∫ x, x ^ 1 ∂μ) by
      simpa only [C] using hfi 1 1 1]
    simp only [pow_one]
    ring
  have hkernel : signedThirdEvenCumulantKernel = fun p =>
      (1 / 3 : ℝ) * A p - (5 / 2 : ℝ) * B p + 30 * C p := by
    funext p
    simp only [signedThirdEvenCumulantKernel, A, B, C, f]
    ring
  calc
    (∫ p, signedThirdEvenCumulantKernel p ∂μ.prod (μ.prod μ)) =
        (∫ p, (1 / 3 : ℝ) * A p - (5 / 2 : ℝ) * B p
          ∂μ.prod (μ.prod μ)) +
          ∫ p, 30 * C p ∂μ.prod (μ.prod μ) := by
            rw [hkernel]
            simpa only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] using
              (integral_add_apply
                ((hA.const_mul _).sub (hB.const_mul _)) (hC.const_mul _))
    _ = ((∫ p, (1 / 3 : ℝ) * A p ∂μ.prod (μ.prod μ)) -
          ∫ p, (5 / 2 : ℝ) * B p ∂μ.prod (μ.prod μ)) +
          ∫ p, 30 * C p ∂μ.prod (μ.prod μ) := by
            congr 1
            simpa only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] using
              (integral_sub_apply (hA.const_mul _) (hB.const_mul _))
    _ = ((1 / 3 : ℝ) * ∫ p, A p ∂μ.prod (μ.prod μ)) -
          ((5 / 2 : ℝ) * ∫ p, B p ∂μ.prod (μ.prod μ)) +
          30 * ∫ p, C p ∂μ.prod (μ.prod μ) := by
            rw [integral_const_mul_apply, integral_const_mul_apply,
              integral_const_mul_apply]
    _ = _ := by rw [hAi, hBi, hCi]; ring

private theorem thetaCuspContinuousSourceDensity_measurable :
    Measurable (fun x : ℝ => ENNReal.ofReal
      (thetaCuspContinuousSourceScale * (2 * thetaCuspFullSource x))) :=
  ENNReal.measurable_ofReal.comp
    continuous_thetaCuspContinuousSourceDensity.measurable

private theorem thetaCuspContinuousSourceDensity_nonneg_ae :
    0 ≤ᵐ[volume.restrict (Set.Ioi 0)]
      (fun x : ℝ => thetaCuspContinuousSourceScale * (2 * thetaCuspFullSource x)) := by
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact mul_nonneg thetaCuspContinuousSourceScale_pos.le
    (mul_nonneg (by positivity) (thetaCuspFullSource_pos_of_pos hx).le)

/-- Every even power is integrable against the calibrated continuous theta source. -/
theorem integrable_pow_thetaCuspContinuousSourceMeasure (j : ℕ) :
    Integrable (fun x : ℝ => x ^ (2 * j)) thetaCuspContinuousSourceMeasure := by
  rw [thetaCuspContinuousSourceMeasure,
    integrable_withDensity_iff_integrable_smul₀'
      thetaCuspContinuousSourceDensity_measurable.aemeasurable
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  have hbase := (integrableOn_thetaCuspRawMoment (2 * j)).const_mul
    (2 * thetaCuspContinuousSourceScale)
  apply hbase.congr
  filter_upwards [thetaCuspContinuousSourceDensity_nonneg_ae] with x hx
  simp only [ENNReal.toReal_ofReal hx, smul_eq_mul]
  ring

/-- Even moments of the calibrated continuous theta source are scaled raw theta moments. -/
theorem integral_pow_thetaCuspContinuousSourceMeasure (j : ℕ) :
    (∫ x : ℝ, x ^ (2 * j) ∂thetaCuspContinuousSourceMeasure) =
      thetaCuspContinuousSourceScale * thetaCuspRawEvenMoment j := by
  rw [thetaCuspContinuousSourceMeasure,
    integral_withDensity_eq_integral_toReal_smul
      thetaCuspContinuousSourceDensity_measurable
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  calc
    (∫ x : ℝ, (ENNReal.ofReal
        (thetaCuspContinuousSourceScale * (2 * thetaCuspFullSource x))).toReal •
          x ^ (2 * j)
        ∂volume.restrict (Set.Ioi 0)) =
        ∫ x : ℝ, thetaCuspContinuousSourceScale *
          (2 * (x ^ (2 * j) * thetaCuspFullSource x))
          ∂volume.restrict (Set.Ioi 0) := by
            apply integral_congr_ae
            filter_upwards [thetaCuspContinuousSourceDensity_nonneg_ae] with x hx
            simp only [ENNReal.toReal_ofReal hx, smul_eq_mul]
            ring
    _ = thetaCuspContinuousSourceScale * thetaCuspRawEvenMoment j := by
      rw [integral_const_mul, thetaCuspRawEvenMoment, integral_const_mul]

/-- Pushforward of the calibrated theta source under `x ↦ x²`. -/
def thetaCuspEvenMomentMeasure : Measure ℝ :=
  Measure.map (fun x : ℝ => x ^ 2) thetaCuspContinuousSourceMeasure

instance thetaCuspEvenMomentMeasure_isFiniteMeasure :
    IsFiniteMeasure thetaCuspEvenMomentMeasure := by
  constructor
  rw [thetaCuspEvenMomentMeasure,
    Measure.map_apply (by fun_prop) MeasurableSet.univ]
  simp

theorem integrable_pow_thetaCuspEvenMomentMeasure (j : ℕ) :
    Integrable (fun y : ℝ => y ^ j) thetaCuspEvenMomentMeasure := by
  rw [thetaCuspEvenMomentMeasure,
    integrable_map_measure (by fun_prop) (by fun_prop)]
  convert integrable_pow_thetaCuspContinuousSourceMeasure j using 1
  funext x
  simp only [Function.comp_apply]
  rw [pow_mul]

theorem integral_pow_thetaCuspEvenMomentMeasure (j : ℕ) :
    (∫ y : ℝ, y ^ j ∂thetaCuspEvenMomentMeasure) =
      thetaCuspContinuousSourceScale * thetaCuspRawEvenMoment j := by
  rw [thetaCuspEvenMomentMeasure,
    integral_map (by fun_prop) (by fun_prop)]
  convert integral_pow_thetaCuspContinuousSourceMeasure j using 1
  apply integral_congr_ae
  filter_upwards with x
  rw [pow_mul]

/-- Cancellation-preserving theta third-cumulant numerator. -/
def thetaCuspThirdCumulantProductIntegral : ℝ :=
  ∫ p : ℝ × (ℝ × ℝ), signedThirdEvenCumulantKernel p
    ∂thetaCuspEvenMomentMeasure.prod
      (thetaCuspEvenMomentMeasure.prod thetaCuspEvenMomentMeasure)

theorem thetaCuspThirdCumulantProductIntegral_eq_rawMoments :
    thetaCuspThirdCumulantProductIntegral =
      thetaCuspContinuousSourceScale ^ 3 *
        (thetaCuspRawEvenMoment 0 ^ 2 * thetaCuspRawEvenMoment 3 -
          15 * thetaCuspRawEvenMoment 0 * thetaCuspRawEvenMoment 1 *
            thetaCuspRawEvenMoment 2 +
          30 * thetaCuspRawEvenMoment 1 ^ 3) := by
  have h0 : Integrable (fun _ : ℝ => (1 : ℝ)) thetaCuspEvenMomentMeasure := by
    simpa only [pow_zero] using integrable_pow_thetaCuspEvenMomentMeasure 0
  have h := integral_signedThirdEvenCumulantKernel thetaCuspEvenMomentMeasure h0
    (by simpa only [pow_one] using integrable_pow_thetaCuspEvenMomentMeasure 1)
    (integrable_pow_thetaCuspEvenMomentMeasure 2)
    (integrable_pow_thetaCuspEvenMomentMeasure 3)
  have hm0 : (∫ _ : ℝ, (1 : ℝ) ∂thetaCuspEvenMomentMeasure) =
      thetaCuspContinuousSourceScale * thetaCuspRawEvenMoment 0 := by
    simpa only [pow_zero] using integral_pow_thetaCuspEvenMomentMeasure 0
  have hm1 : (∫ x : ℝ, x ∂thetaCuspEvenMomentMeasure) =
      thetaCuspContinuousSourceScale * thetaCuspRawEvenMoment 1 := by
    simpa only [pow_one] using integral_pow_thetaCuspEvenMomentMeasure 1
  rw [hm0, hm1,
    integral_pow_thetaCuspEvenMomentMeasure 2,
    integral_pow_thetaCuspEvenMomentMeasure 3] at h
  calc
    thetaCuspThirdCumulantProductIntegral =
        (thetaCuspContinuousSourceScale * thetaCuspRawEvenMoment 0) ^ 2 *
            (thetaCuspContinuousSourceScale * thetaCuspRawEvenMoment 3) -
          15 * (thetaCuspContinuousSourceScale * thetaCuspRawEvenMoment 0) *
            (thetaCuspContinuousSourceScale * thetaCuspRawEvenMoment 1) *
            (thetaCuspContinuousSourceScale * thetaCuspRawEvenMoment 2) +
          30 * (thetaCuspContinuousSourceScale * thetaCuspRawEvenMoment 1) ^ 3 := by
            simpa only [thetaCuspThirdCumulantProductIntegral] using h
    _ = _ := by ring

/-- The normalized sixth reciprocal trace is the product-kernel expectation divided by
`120` times the cube of total mass. -/
theorem normalizedPrimeArchMoment_two_eq_thirdCumulantProductRatio :
    normalizedPrimeArchMoment 2 =
      thetaCuspThirdCumulantProductIntegral /
        (120 * (∫ _ : ℝ, (1 : ℝ) ∂thetaCuspEvenMomentMeasure) ^ 3) := by
  have hm0 : (∫ _ : ℝ, (1 : ℝ) ∂thetaCuspEvenMomentMeasure) =
      thetaCuspContinuousSourceScale * thetaCuspRawEvenMoment 0 := by
    simpa only [pow_zero] using integral_pow_thetaCuspEvenMomentMeasure 0
  rw [normalizedPrimeArchMoment_two_eq_thetaCuspNormalizedEvenMoment,
    thetaCuspThirdCumulantProductIntegral_eq_rawMoments, hm0]
  simp only [thetaCuspNormalizedEvenMoment]
  field_simp [thetaCuspContinuousSourceScale_pos.ne',
    thetaCuspRawEvenMoment_zero_pos.ne']
  ring

/-- Exact replacement for the five-box quadrature certificate: the sixth-trace cap is equivalent
to one strict signed product-kernel estimate. -/
theorem normalizedPrimeArchMoment_two_lt_three_over_tenMillion_iff_productKernel :
    normalizedPrimeArchMoment 2 < (3 / 10000000 : ℝ) ↔
      thetaCuspThirdCumulantProductIntegral <
        (9 / 250000 : ℝ) *
          (∫ _ : ℝ, (1 : ℝ) ∂thetaCuspEvenMomentMeasure) ^ 3 := by
  have hmass : 0 < ∫ _ : ℝ, (1 : ℝ) ∂thetaCuspEvenMomentMeasure := by
    have hm0 : (∫ _ : ℝ, (1 : ℝ) ∂thetaCuspEvenMomentMeasure) =
        thetaCuspContinuousSourceScale * thetaCuspRawEvenMoment 0 := by
      simpa only [pow_zero] using integral_pow_thetaCuspEvenMomentMeasure 0
    rw [hm0]
    exact mul_pos thetaCuspContinuousSourceScale_pos thetaCuspRawEvenMoment_zero_pos
  rw [normalizedPrimeArchMoment_two_eq_thirdCumulantProductRatio,
    div_lt_iff₀ (mul_pos (by positivity : (0 : ℝ) < 120) (pow_pos hmass 3))]
  ring_nf

/-! ## The same obstruction as a logarithmic Xi coefficient -/

/-- Degree-three jet of the normalized completed-Xi series in square coordinate. -/
def thetaCuspXiSquareNormalizedThirdJet : Polynomial ℝ :=
  1 + C (thetaCuspNormalizedEvenMoment 1 / 2) * X +
    C (thetaCuspNormalizedEvenMoment 2 / 24) * X ^ 2 +
    C (thetaCuspNormalizedEvenMoment 3 / 720) * X ^ 3

theorem thetaCuspXiSquareNormalizedThirdJet_coeff_zero :
    thetaCuspXiSquareNormalizedThirdJet.coeff 0 = 1 := by
  simp [thetaCuspXiSquareNormalizedThirdJet]

/-- The explicit jet is the normalization of the corpus's actual Xi Taylor section. -/
theorem thetaCuspXiSquareNormalizedThirdJet_eq_normalizedPolynomial :
    thetaCuspXiSquareNormalizedThirdJet =
      normalizedPolynomial (xiCTaylorEvenMagnitudePolynomial 3) := by
  classical
  ext n
  by_cases h0 : n = 0
  · subst n
    simp [thetaCuspXiSquareNormalizedThirdJet, normalizedPolynomial,
      xiCTaylorEvenMagnitudePolynomial, thetaCuspNormalizedEvenMoment,
      Finset.sum_range_succ, thetaCuspRawEvenMoment_zero_pos.ne']
  by_cases h1 : n = 1
  · subst n
    simp [thetaCuspXiSquareNormalizedThirdJet, normalizedPolynomial,
      xiCTaylorEvenMagnitudePolynomial, thetaCuspNormalizedEvenMoment,
      Finset.sum_range_succ, Polynomial.coeff_one, Polynomial.coeff_X,
      Polynomial.coeff_C]
    field_simp [thetaCuspRawEvenMoment_zero_pos.ne']
  by_cases h2 : n = 2
  · subst n
    simp [thetaCuspXiSquareNormalizedThirdJet, normalizedPolynomial,
      xiCTaylorEvenMagnitudePolynomial, thetaCuspNormalizedEvenMoment,
      Finset.sum_range_succ, Polynomial.coeff_one, Polynomial.coeff_X,
      Polynomial.coeff_C, Nat.factorial]
    field_simp [thetaCuspRawEvenMoment_zero_pos.ne']
  by_cases h3 : n = 3
  · subst n
    simp [thetaCuspXiSquareNormalizedThirdJet, normalizedPolynomial,
      xiCTaylorEvenMagnitudePolynomial, thetaCuspNormalizedEvenMoment,
      Finset.sum_range_succ, Polynomial.coeff_one, Polynomial.coeff_X,
      Polynomial.coeff_C, Nat.factorial]
    field_simp [thetaCuspRawEvenMoment_zero_pos.ne']
  have h1' : 1 ≠ n := fun h => h1 h.symm
  simp [thetaCuspXiSquareNormalizedThirdJet, normalizedPolynomial,
    xiCTaylorEvenMagnitudePolynomial, thetaCuspNormalizedEvenMoment,
    Finset.sum_range_succ, Polynomial.coeff_C_mul, Polynomial.coeff_one,
    Polynomial.coeff_X, Polynomial.coeff_C, h0, h1', h2, h3]

/-- The third logarithmic coefficient of the normalized Xi square-coordinate jet. -/
def thetaCuspXiSquareThirdLogCoefficient : ℝ :=
  PowerSeries.coeff 3
    (PowerSeries.logOf
      (thetaCuspXiSquareNormalizedThirdJet : PowerSeries ℝ))

/-- Explicit third logarithmic coefficient of the normalized Xi square-coordinate jet. -/
theorem thetaCuspXiSquareThirdLogCoefficient_eq :
    thetaCuspXiSquareThirdLogCoefficient =
      thetaCuspNormalizedEvenMoment 3 / 720 -
        thetaCuspNormalizedEvenMoment 1 * thetaCuspNormalizedEvenMoment 2 / 48 +
        thetaCuspNormalizedEvenMoment 1 ^ 3 / 24 := by
  let a := thetaCuspNormalizedEvenMoment 1 / 2
  let b := thetaCuspNormalizedEvenMoment 2 / 24
  let c := thetaCuspNormalizedEvenMoment 3 / 720
  let R : Polynomial ℝ := C a + C b * X + C c * X ^ 2
  let Q : Polynomial ℝ := X * R
  have hsub : thetaCuspXiSquareNormalizedThirdJet - 1 = Q := by
    dsimp [thetaCuspXiSquareNormalizedThirdJet, Q, R, a, b, c]
    ring
  have hq1 : Q.coeff 3 = c := by
    dsimp [Q]
    simpa only [pow_one, Nat.reduceAdd] using
      (Polynomial.coeff_X_pow_mul R 1 2).trans (by simp [R])
  have hq2 : (Q ^ 2).coeff 3 = 2 * a * b := by
    dsimp [Q]
    rw [mul_pow]
    change (X ^ 2 * R ^ 2).coeff (1 + 2) = 2 * a * b
    rw [Polynomial.coeff_X_pow_mul, pow_two, Polynomial.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp [Finset.sum_range_succ, R]
    ring
  have hq3 : (Q ^ 3).coeff 3 = a ^ 3 := by
    dsimp [Q]
    rw [mul_pow]
    change (X ^ 3 * R ^ 3).coeff (0 + 3) = a ^ 3
    rw [Polynomial.coeff_X_pow_mul]
    rw [Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_pow]
    simp [R]
  rw [thetaCuspXiSquareThirdLogCoefficient,
    ← truncatedLogCoeff_eq_coeff_logOf 3
      thetaCuspXiSquareNormalizedThirdJet
      thetaCuspXiSquareNormalizedThirdJet_coeff_zero,
    truncatedLogCoeff]
  simp [Finset.sum_range_succ, logarithmicWeight, hsub, hq1, hq2, hq3]
  dsimp [a, b, c]
  ring

/-- The sixth reciprocal trace is six times the third Xi logarithmic coefficient. -/
theorem normalizedPrimeArchMoment_two_eq_six_mul_thetaCuspXiSquareThirdLogCoefficient :
    normalizedPrimeArchMoment 2 = 6 * thetaCuspXiSquareThirdLogCoefficient := by
  rw [thetaCuspXiSquareThirdLogCoefficient_eq,
    normalizedPrimeArchMoment_two_eq_thetaCuspNormalizedEvenMoment]
  ring

/-- Exact logarithmic-coefficient form of the order-24 sixth-trace cap. -/
theorem normalizedPrimeArchMoment_two_lt_three_over_tenMillion_iff_thirdLogCoefficient :
    normalizedPrimeArchMoment 2 < (3 / 10000000 : ℝ) ↔
      thetaCuspXiSquareThirdLogCoefficient < (1 / 20000000 : ℝ) := by
  rw [normalizedPrimeArchMoment_two_eq_six_mul_thetaCuspXiSquareThirdLogCoefficient]
  constructor <;> intro h <;> linarith

/-- Product-kernel and logarithmic-coefficient attacks are exactly the same cap. -/
theorem thetaCuspThirdCumulantProductKernel_lt_iff_thirdLogCoefficient :
    thetaCuspThirdCumulantProductIntegral <
        (9 / 250000 : ℝ) *
          (∫ _ : ℝ, (1 : ℝ) ∂thetaCuspEvenMomentMeasure) ^ 3 ↔
      thetaCuspXiSquareThirdLogCoefficient < (1 / 20000000 : ℝ) := by
  rw [← normalizedPrimeArchMoment_two_lt_three_over_tenMillion_iff_productKernel,
    normalizedPrimeArchMoment_two_lt_three_over_tenMillion_iff_thirdLogCoefficient]

end

end RHTower
