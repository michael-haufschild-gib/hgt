import GaloisForLFunctions.RHTower.ThetaCuspReflectedSourceFifthRootCurvature
import GaloisForLFunctions.RHTower.HedenmalmThetaKernelEnergy
import Mathlib.MeasureTheory.Measure.Real

/-!
# No positive Bernstein measure for the reflected theta square profile

The completed-theta reflected source product decays faster than every Gaussian in displacement.
After the squared-displacement substitution, it therefore decays faster than every exponential.
Every nonzero finite positive Laplace transform has an exponential minorant coming from a bounded
interval carrying positive mass.  These facts are incompatible.

Consequently the squared-displacement profile cannot be represented by a finite positive Bernstein
measure.  Any measure route to fifth-root curvature must retain signed cancellation, depend on the
scale, or act before the squared-displacement substitution.
-/

open Filter Topology MeasureTheory Set

namespace RHTower

noncomputable section

open HedenmalmThetaSource

/-- A uniform double-exponential envelope for the reflected completed-theta source product. -/
theorem thetaCuspReflectedSourceProduct_le_superGaussianEnvelope
    (u : ℝ) {t : ℝ} (hut : |u| ≤ t) :
    thetaCuspReflectedSourceProduct u t ≤
      thetaEnvelopeUpper ^ 2 *
        Real.exp (9 * t - 2 * Real.pi * Real.exp (2 * t)) := by
  have htu : u ≤ t := le_trans (le_abs_self u) hut
  have hnut : -u ≤ t := le_trans (neg_le_abs u) hut
  have hplus : 0 ≤ t + u := by linarith
  have hminus : 0 ≤ t - u := by linarith
  have hp := thetaCuspFullSource_le_envelope hplus
  have hm := thetaCuspFullSource_le_envelope hminus
  have hm0 := (thetaCuspFullSource_pos_all (t - u)).le
  have hU0 := thetaEnvelopeUpper_pos.le
  have henvp := (thetaEnvelope_pos (t + u)).le
  have hprod :
      thetaCuspFullSource (t + u) * thetaCuspFullSource (t - u) ≤
        (thetaEnvelopeUpper * thetaEnvelope (t + u)) *
          (thetaEnvelopeUpper * thetaEnvelope (t - u)) :=
    mul_le_mul hp hm hm0 (mul_nonneg hU0 henvp)
  have hsum : 2 ≤ Real.exp (2 * u) + Real.exp (-2 * u) := by
    have h := Real.one_le_cosh (2 * u)
    rw [Real.cosh_eq] at h
    have htwo : 2 ≤ Real.exp (2 * u) + Real.exp (-(2 * u)) := by
      linarith
    simpa only [neg_mul] using htwo
  unfold thetaCuspReflectedSourceProduct
  rw [show u + t = t + u by ring,
    show thetaCuspFullSource (u - t) = thetaCuspFullSource (t - u) by
      rw [show u - t = -(t - u) by ring, thetaCuspFullSource_neg]]
  apply hprod.trans
  rw [thetaEnvelope, thetaEnvelope]
  let A : ℝ := 9 * (t + u) / 2 + -Real.pi * Real.exp (2 * (t + u))
  let B : ℝ := 9 * (t - u) / 2 + -Real.pi * Real.exp (2 * (t - u))
  have hEA :
      Real.exp (9 * (t + u) / 2) *
          Real.exp (-Real.pi * Real.exp (2 * (t + u))) = Real.exp A := by
    rw [← Real.exp_add]
  have hEB :
      Real.exp (9 * (t - u) / 2) *
          Real.exp (-Real.pi * Real.exp (2 * (t - u))) = Real.exp B := by
    rw [← Real.exp_add]
  have hexpFactor :
      Real.exp (2 * (t + u)) + Real.exp (2 * (t - u)) =
        Real.exp (2 * t) * (Real.exp (2 * u) + Real.exp (-2 * u)) := by
    rw [show 2 * (t + u) = 2 * t + 2 * u by ring,
      show 2 * (t - u) = 2 * t + (-2 * u) by ring,
      Real.exp_add, Real.exp_add]
    ring
  have htail :
      2 * Real.pi * Real.exp (2 * t) ≤
        Real.pi * (Real.exp (2 * (t + u)) + Real.exp (2 * (t - u))) := by
    rw [hexpFactor]
    calc
      2 * Real.pi * Real.exp (2 * t) =
          (Real.pi * Real.exp (2 * t)) * 2 := by ring
      _ ≤ (Real.pi * Real.exp (2 * t)) *
          (Real.exp (2 * u) + Real.exp (-2 * u)) := by
        exact mul_le_mul_of_nonneg_left hsum
          (mul_nonneg Real.pi_pos.le (Real.exp_pos _).le)
      _ = Real.pi *
          (Real.exp (2 * t) * (Real.exp (2 * u) + Real.exp (-2 * u))) := by
        ring
  calc
    thetaEnvelopeUpper *
          (Real.exp (9 * (t + u) / 2) *
            Real.exp (-Real.pi * Real.exp (2 * (t + u)))) *
        (thetaEnvelopeUpper *
          (Real.exp (9 * (t - u) / 2) *
            Real.exp (-Real.pi * Real.exp (2 * (t - u))))) =
        thetaEnvelopeUpper ^ 2 * (Real.exp A * Real.exp B) := by
      rw [hEA, hEB]
      ring
    _ = thetaEnvelopeUpper ^ 2 * Real.exp (A + B) := by
      exact congrArg (fun z : ℝ => thetaEnvelopeUpper ^ 2 * z)
        (Real.exp_add A B).symm
    _ ≤ thetaEnvelopeUpper ^ 2 *
        Real.exp (9 * t - 2 * Real.pi * Real.exp (2 * t)) := by
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_)
        (sq_nonneg thetaEnvelopeUpper)
      dsimp only [A, B]
      nlinarith

/-- The reflected completed-theta source product decays faster than every Gaussian. -/
theorem tendsto_exp_sq_mul_thetaCuspReflectedSourceProduct_atTop_zero
    (u : ℝ) {a : ℝ} (ha : 0 ≤ a) :
    Tendsto (fun t : ℝ => Real.exp (a * t ^ 2) *
      thetaCuspReflectedSourceProduct u t) atTop (𝓝 0) := by
  have htwo : Tendsto (fun t : ℝ => 2 * t) atTop atTop :=
    tendsto_id.const_mul_atTop (by norm_num)
  have hratio :
      Tendsto (fun t : ℝ => Real.exp (2 * t) / (2 * t) ^ 2) atTop atTop :=
    (Real.tendsto_exp_div_pow_atTop 2).comp htwo
  have hlarge : ∀ᶠ t : ℝ in atTop,
      a + 10 ≤ Real.exp (2 * t) / (2 * t) ^ 2 :=
    Filter.tendsto_atTop.mp hratio (a + 10)
  have hbound : ∀ᶠ t : ℝ in atTop,
      Real.exp (a * t ^ 2) * thetaCuspReflectedSourceProduct u t ≤
        thetaEnvelopeUpper ^ 2 * Real.exp (-t ^ 2) := by
    filter_upwards [hlarge, eventually_ge_atTop |u|,
      eventually_ge_atTop (1 : ℝ)] with t hratioT hut ht
    have htpos : 0 < t := lt_of_lt_of_le (by norm_num) ht
    have hden : 0 < (2 * t) ^ 2 := by positivity
    have hcross : (a + 10) * (2 * t) ^ 2 ≤ Real.exp (2 * t) :=
      (le_div_iff₀ hden).mp hratioT
    have hdominance :
        (a + 10) * t ^ 2 ≤ 2 * Real.pi * Real.exp (2 * t) := by
      nlinarith [Real.pi_gt_three, Real.exp_pos (2 * t), sq_nonneg t]
    have hP := thetaCuspReflectedSourceProduct_le_superGaussianEnvelope u hut
    calc
      Real.exp (a * t ^ 2) * thetaCuspReflectedSourceProduct u t ≤
          Real.exp (a * t ^ 2) *
            (thetaEnvelopeUpper ^ 2 *
              Real.exp (9 * t - 2 * Real.pi * Real.exp (2 * t))) := by
        exact mul_le_mul_of_nonneg_left hP (Real.exp_pos _).le
      _ = thetaEnvelopeUpper ^ 2 *
          Real.exp (a * t ^ 2 + 9 * t -
            2 * Real.pi * Real.exp (2 * t)) := by
        rw [show a * t ^ 2 + 9 * t - 2 * Real.pi * Real.exp (2 * t) =
            a * t ^ 2 + (9 * t - 2 * Real.pi * Real.exp (2 * t)) by ring,
          Real.exp_add]
        ring
      _ ≤ thetaEnvelopeUpper ^ 2 * Real.exp (-t ^ 2) := by
        apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_)
          (sq_nonneg thetaEnvelopeUpper)
        nlinarith [sq_nonneg (t - 1)]
  have hgauss : Tendsto
      (fun t : ℝ => thetaEnvelopeUpper ^ 2 * Real.exp (-t ^ 2))
      atTop (𝓝 0) := by
    have hsq : Tendsto (fun t : ℝ => (1 : ℝ) * t ^ 2) atTop atTop :=
      Tendsto.const_mul_atTop (by norm_num)
        (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0))
    have hneg : Tendsto (fun t : ℝ => -((1 : ℝ) * t ^ 2)) atTop atBot :=
      tendsto_neg_atTop_atBot.comp hsq
    have hexp : Tendsto (fun t : ℝ => Real.exp (-((1 : ℝ) * t ^ 2)))
        atTop (𝓝 0) := Real.tendsto_exp_atBot.comp hneg
    simpa only [one_mul, mul_zero] using
      hexp.const_mul (thetaEnvelopeUpper ^ 2)
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun t =>
      mul_nonneg (Real.exp_pos _).le (by
        unfold thetaCuspReflectedSourceProduct
        exact mul_nonneg (thetaCuspFullSource_pos_all _).le
          (thetaCuspFullSource_pos_all _).le)
  · exact hbound
  · exact hgauss

/-- Laplace transform of a positive spectral measure on the nonnegative ray. -/
def positiveLaplaceTransform (μ : Measure NNReal) (x : ℝ) : ℝ :=
  ∫ s : NNReal, Real.exp (-x * (s : ℝ)) ∂μ

private theorem integrable_positiveLaplaceTransform
    (μ : Measure NNReal) [IsFiniteMeasure μ] {x : ℝ} (hx : 0 ≤ x) :
    Integrable (fun s : NNReal => Real.exp (-x * (s : ℝ))) μ := by
  apply (integrable_const (μ := μ) (1 : ℝ)).mono'
  · fun_prop
  · exact Filter.Eventually.of_forall fun s => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      rw [Real.exp_le_one_iff]
      exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hx) s.2

/-- Every nonzero finite positive Laplace transform has an exponential lower tail. -/
theorem positiveLaplaceTransform_has_exponential_minorant
    (μ : Measure NNReal) [IsFiniteMeasure μ] (hμ : μ ≠ 0) :
    ∃ N : NNReal, 0 < μ.real (Iic N) ∧ ∀ x : ℝ, 0 ≤ x →
      μ.real (Iic N) * Real.exp (-x * (N : ℝ)) ≤
        positiveLaplaceTransform μ x := by
  have hmass : 0 < μ univ := Measure.measure_univ_pos.mpr hμ
  have hevent : ∀ᶠ N : NNReal in atTop, 0 < μ (Iic N) :=
    (tendsto_measure_Iic_atTop μ).eventually (Ioi_mem_nhds hmass)
  obtain ⟨N, hN⟩ := hevent.exists
  have hNtop : μ (Iic N) ≠ ⊤ := ne_of_lt (measure_lt_top μ (Iic N))
  have hNreal : 0 < μ.real (Iic N) :=
    ENNReal.toReal_pos (ne_of_gt hN) hNtop
  refine ⟨N, hNreal, ?_⟩
  intro x hx
  let f : NNReal → ℝ := fun s => Real.exp (-x * (s : ℝ))
  let c : ℝ := Real.exp (-x * (N : ℝ))
  have hfμ : Integrable f μ := integrable_positiveLaplaceTransform μ hx
  have hfr : Integrable f (μ.restrict (Iic N)) :=
    hfμ.mono_measure Measure.restrict_le_self
  have hcr : Integrable (fun _ : NNReal => c) (μ.restrict (Iic N)) :=
    integrable_const c
  have hc_le : ∫ _ : NNReal, c ∂μ.restrict (Iic N) ≤
      ∫ s : NNReal, f s ∂μ.restrict (Iic N) := by
    apply integral_mono_ae hcr hfr
    filter_upwards [ae_restrict_mem measurableSet_Iic] with s hs
    dsimp only [c, f]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left
      (show (s : ℝ) ≤ (N : ℝ) by exact_mod_cast hs) (neg_nonpos.mpr hx))
  have hrestrict_le : ∫ s : NNReal, f s ∂μ.restrict (Iic N) ≤
      ∫ s : NNReal, f s ∂μ := by
    exact integral_mono_measure Measure.restrict_le_self
      (Filter.Eventually.of_forall fun s => (Real.exp_pos _).le) hfμ
  unfold positiveLaplaceTransform
  calc
    μ.real (Iic N) * c = ∫ _ : NNReal, c ∂μ.restrict (Iic N) := by
      rw [integral_const]
      simp only [measureReal_def, Measure.restrict_apply_univ, smul_eq_mul]
    _ ≤ ∫ s : NNReal, f s ∂μ.restrict (Iic N) := hc_le
    _ ≤ ∫ s : NNReal, f s ∂μ := hrestrict_le

/-- The squared-displacement reflected completed-theta product is not the Laplace transform of any
finite positive measure on the nonnegative ray. -/
theorem not_exists_finitePositiveLaplaceRepresentation_thetaCuspReflectedSquaredProduct
    (u : ℝ) :
    ¬ ∃ μ : Measure NNReal, μ univ < ⊤ ∧ ∀ x : ℝ, 0 ≤ x →
      thetaCuspReflectedSourceProduct u (Real.sqrt x) =
        positiveLaplaceTransform μ x := by
  rintro ⟨μ, hfinite, hrep⟩
  letI : IsFiniteMeasure μ := IsFiniteMeasure.mk hfinite
  have hμ : μ ≠ 0 := by
    intro hzero
    have hrep0 := hrep 0 (by norm_num)
    rw [hzero] at hrep0
    simp only [Real.sqrt_zero, positiveLaplaceTransform,
      MeasureTheory.integral_zero_measure] at hrep0
    have hP0 : 0 < thetaCuspReflectedSourceProduct u 0 := by
      unfold thetaCuspReflectedSourceProduct
      exact mul_pos (thetaCuspFullSource_pos_all _) (thetaCuspFullSource_pos_all _)
    linarith
  obtain ⟨N, hmass, hminor⟩ :=
    positiveLaplaceTransform_has_exponential_minorant μ hμ
  have hlimit := tendsto_exp_sq_mul_thetaCuspReflectedSourceProduct_atTop_zero
    u (a := (N : ℝ)) N.2
  have hevent : ∀ᶠ t : ℝ in atTop,
      Real.exp ((N : ℝ) * t ^ 2) * thetaCuspReflectedSourceProduct u t <
        μ.real (Iic N) :=
    hlimit.eventually (Iio_mem_nhds hmass)
  obtain ⟨t, hlt, ht⟩ :=
    (hevent.and (eventually_ge_atTop (0 : ℝ))).exists
  have hrepT := hrep (t ^ 2) (sq_nonneg t)
  rw [Real.sqrt_sq_eq_abs, abs_of_nonneg ht] at hrepT
  have hminorT := hminor (t ^ 2) (sq_nonneg t)
  rw [← hrepT] at hminorT
  have hlower : μ.real (Iic N) ≤
      Real.exp ((N : ℝ) * t ^ 2) * thetaCuspReflectedSourceProduct u t := by
    have hexpCancel :
        Real.exp ((N : ℝ) * t ^ 2) *
            Real.exp (-((N : ℝ) * t ^ 2)) = 1 := by
      rw [← Real.exp_add]
      ring_nf
      exact Real.exp_zero
    calc
      μ.real (Iic N) = Real.exp ((N : ℝ) * t ^ 2) *
          (μ.real (Iic N) * Real.exp (-(t ^ 2) * (N : ℝ))) := by
        rw [show -(t ^ 2) * (N : ℝ) = -((N : ℝ) * t ^ 2) by ring]
        rw [show Real.exp ((N : ℝ) * t ^ 2) *
              (μ.real (Iic N) * Real.exp (-((N : ℝ) * t ^ 2))) =
            μ.real (Iic N) *
              (Real.exp ((N : ℝ) * t ^ 2) *
                Real.exp (-((N : ℝ) * t ^ 2))) by ring,
          hexpCancel, mul_one]
      _ ≤ Real.exp ((N : ℝ) * t ^ 2) *
          thetaCuspReflectedSourceProduct u t :=
        mul_le_mul_of_nonneg_left hminorT (Real.exp_pos _).le
  linarith

end

end RHTower
