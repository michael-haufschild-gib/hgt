import GaloisForLFunctions.RHTower.CCMUnitRieszCompletedCurrentLaplace
import GaloisForLFunctions.RHTower.CCMUnitRieszFUCurvatureTransport
import GaloisForLFunctions.RHTower.XiCriticalMellinSourceFactorization

/-!
# The time-domain completed-source weld

The literal finite-aperture unit-Riesz completed-source response is the causal convolution of the
critically weighted completed current against the two-exponential aperture kernel.  Its Laplace
transform is therefore the aperture multiplier times the critical-Mellin defect.  Adding the
Stirling convolution — the causal convolution of the same positive aperture kernel against the
source-free Stirling correction — produces exactly the pole-filled unit-Riesz coefficient.

This file proves that weld, the strict sign and the exponential bound of the Stirling
convolution, and the resulting no-loss producer equivalence.

Unconditional; no zero-free input and no RH claim.
-/

open MeasureTheory Set Filter Topology Complex

noncomputable section

namespace GaloisForLFunctions.RHTower

open _root_.RHTower

/-! ## The response as a Volterra convolution of the completed current -/

theorem integrableOn_criticalMellinCompletedError_Ioc {t : ℝ} (ht : 0 ≤ t) :
    IntegrableOn criticalMellinCompletedError (Ioc (0 : ℝ) t) volume := by
  have h := intervalIntegrable_criticalMellinCompletedError_on_Icc (b := (0 : ℝ)) (t := t) ht
  rwa [intervalIntegrable_iff_integrableOn_Ioc_of_le ht] at h

theorem integrableOn_exp_mul_unitRieszCompletedCurrent
    {b t : ℝ} (hb : 0 ≤ b) (ht : 0 ≤ t) :
    IntegrableOn (fun h : ℝ => Real.exp (-(b * (t - h))) * unitRieszCompletedCurrent h)
      (Ioc (0 : ℝ) t) volume := by
  refine Integrable.mono' (integrableOn_criticalMellinCompletedError_Ioc ht).norm ?_ ?_
  · exact ((Real.measurable_exp.comp (by fun_prop)).mul
      measurable_unitRieszCompletedCurrent).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with h hh
    have hh0 : (0 : ℝ) < h := hh.1
    have hht : h ≤ t := hh.2
    have h1 : Real.exp (-(b * (t - h))) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      nlinarith
    have h2 : Real.exp (-h / 2) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      linarith
    have h1p : (0 : ℝ) < Real.exp (-(b * (t - h))) := Real.exp_pos _
    have h2p : (0 : ℝ) < Real.exp (-h / 2) := Real.exp_pos _
    rw [Real.norm_eq_abs, Real.norm_eq_abs, unitRieszCompletedCurrent, abs_mul, abs_mul,
      abs_of_pos h1p, abs_of_pos h2p]
    have step : Real.exp (-h / 2) * |criticalMellinCompletedError h| ≤
        |criticalMellinCompletedError h| := by
      nlinarith [abs_nonneg (criticalMellinCompletedError h)]
    nlinarith [step, h1, h1p, mul_nonneg h2p.le (abs_nonneg (criticalMellinCompletedError h))]

/-- **The literal completed-source response is a two-exponential Volterra convolution of the
critically weighted completed current.** -/
theorem unitRieszCompletedSourceResponse_eq_volterra {t : ℝ} (ht : 0 ≤ t) :
    unitRieszCompletedSourceResponse t =
      ((3 * (∫ h in Ioc (0 : ℝ) t,
            Real.exp (-(3 / 2 * (t - h))) * unitRieszCompletedCurrent h) -
          (3 / 2) * (∫ h in Ioc (0 : ℝ) t,
            Real.exp (-(1 * (t - h))) * unitRieszCompletedCurrent h) : ℝ) : ℂ) := by
  have hpt : ∀ h ∈ Ioc (0 : ℝ) t,
      (criticalMellinCompletedError h : ℂ) *
          ((3 * Real.exp (-3 * t / 2 + h) - (3 / 2 : ℝ) * Real.exp (-t + h / 2) : ℝ) : ℂ) =
        ((3 * (Real.exp (-(3 / 2 * (t - h))) * unitRieszCompletedCurrent h) -
          (3 / 2) * (Real.exp (-(1 * (t - h))) * unitRieszCompletedCurrent h) : ℝ) : ℂ) := by
    intro h _
    have e1 : Real.exp (-(3 / 2 * (t - h))) * Real.exp (-h / 2) =
        Real.exp (-3 * t / 2 + h) := by
      rw [← Real.exp_add]; congr 1; ring
    have e2 : Real.exp (-(1 * (t - h))) * Real.exp (-h / 2) =
        Real.exp (-t + h / 2) := by
      rw [← Real.exp_add]; congr 1; ring
    have hreal : (criticalMellinCompletedError h) *
        (3 * Real.exp (-3 * t / 2 + h) - (3 / 2 : ℝ) * Real.exp (-t + h / 2)) =
        3 * (Real.exp (-(3 / 2 * (t - h))) * unitRieszCompletedCurrent h) -
          (3 / 2) * (Real.exp (-(1 * (t - h))) * unitRieszCompletedCurrent h) := by
      rw [unitRieszCompletedCurrent]
      linear_combination
        (-(3 * criticalMellinCompletedError h)) * e1 +
          ((3 / 2 : ℝ) * criticalMellinCompletedError h) * e2
    rw [← hreal]
    push_cast
    ring
  rw [unitRieszCompletedSourceResponse_eq_twoMomentIntegral ht,
    setIntegral_congr_fun measurableSet_Ioc hpt, integral_complex_ofReal]
  congr 1
  have hI1 := integrableOn_exp_mul_unitRieszCompletedCurrent (b := 3 / 2) (by norm_num) ht
  have hI2 := integrableOn_exp_mul_unitRieszCompletedCurrent (b := 1) (by norm_num) ht
  have hs1 : IntegrableOn
      (fun h : ℝ => 3 * (Real.exp (-(3 / 2 * (t - h))) * unitRieszCompletedCurrent h))
      (Ioc (0 : ℝ) t) volume := hI1.const_mul 3
  have hs2 : IntegrableOn
      (fun h : ℝ => (3 / 2 : ℝ) * (Real.exp (-(1 * (t - h))) * unitRieszCompletedCurrent h))
      (Ioc (0 : ℝ) t) volume := hI2.const_mul _
  rw [integral_sub hs1 hs2, MeasureTheory.integral_const_mul,
    MeasureTheory.integral_const_mul]

/-! ## The Laplace transform of the response -/

theorem unitRieszCompletedCurrent_linear_bound :
    ∀ h : ℝ, 0 < h → |unitRieszCompletedCurrent h| ≤ 2 * (1 + h) :=
  fun h hh => abs_unitRieszCompletedCurrent_le hh.le

theorem unitRieszCompletedSourceResponse_laplace {z : ℂ} (hz : 0 < z.re) :
    (∫ t in Ioi (0 : ℝ), Complex.exp (-(z * (t : ℂ))) * unitRieszCompletedSourceResponse t) =
      (3 * (z + ((3 / 2 : ℝ) : ℂ))⁻¹ - (3 / 2) * (z + ((1 : ℝ) : ℂ))⁻¹) *
        ∫ h in Ioi (0 : ℝ),
          Complex.exp (-(z * (h : ℂ))) * ((unitRieszCompletedCurrent h : ℝ) : ℂ) := by
  have hbnd := unitRieszCompletedCurrent_linear_bound
  have hpt : ∀ t ∈ Ioi (0 : ℝ),
      Complex.exp (-(z * (t : ℂ))) * unitRieszCompletedSourceResponse t =
        3 * (Complex.exp (-(z * (t : ℂ))) *
            ((∫ h in Ioc (0 : ℝ) t,
              Real.exp (-(3 / 2 * (t - h))) * unitRieszCompletedCurrent h : ℝ) : ℂ)) -
          (3 / 2) * (Complex.exp (-(z * (t : ℂ))) *
            ((∫ h in Ioc (0 : ℝ) t,
              Real.exp (-(1 * (t - h))) * unitRieszCompletedCurrent h : ℝ) : ℂ)) := by
    intro t ht
    rw [unitRieszCompletedSourceResponse_eq_volterra (le_of_lt ht)]
    push_cast
    ring
  have hi1 := integrableOn_Ioi_cexp_mul_expVolterra (b := 3 / 2) (by norm_num) hz
    measurable_unitRieszCompletedCurrent hbnd
  have hi2 := integrableOn_Ioi_cexp_mul_expVolterra (b := 1) (by norm_num) hz
    measurable_unitRieszCompletedCurrent hbnd
  have h1c : IntegrableOn
      (fun t : ℝ => 3 * (Complex.exp (-(z * (t : ℂ))) *
        ((∫ h in Ioc (0 : ℝ) t,
          Real.exp (-(3 / 2 * (t - h))) * unitRieszCompletedCurrent h : ℝ) : ℂ)))
      (Ioi (0 : ℝ)) volume := hi1.const_mul 3
  have h2c : IntegrableOn
      (fun t : ℝ => (3 / 2 : ℂ) * (Complex.exp (-(z * (t : ℂ))) *
        ((∫ h in Ioc (0 : ℝ) t,
          Real.exp (-(1 * (t - h))) * unitRieszCompletedCurrent h : ℝ) : ℂ)))
      (Ioi (0 : ℝ)) volume := hi2.const_mul _
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_sub h1c h2c,
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
    integral_Ioi_expVolterra_laplace (b := 3 / 2) (by norm_num) hz
      measurable_unitRieszCompletedCurrent hbnd,
    integral_Ioi_expVolterra_laplace (b := 1) (by norm_num) hz
      measurable_unitRieszCompletedCurrent hbnd]
  ring

/-! ## The Stirling convolution -/

/-- Causal convolution of the positive aperture kernel against the Stirling correction:
the source-free part of the unit-Riesz coefficient in the time domain. -/
def unitRieszStirlingConvolution (t : ℝ) : ℝ :=
  ∫ s in Ioc (0 : ℝ) t,
    unitRieszCompletedSourceKernel (t - s) * unitRieszStirlingCorrection s

theorem integrableOn_exp_mul_unitRieszStirlingCorrection
    {b t : ℝ} (hb : 0 ≤ b) (ht : 0 ≤ t) :
    IntegrableOn (fun s : ℝ => Real.exp (-(b * (t - s))) * unitRieszStirlingCorrection s)
      (Ioc (0 : ℝ) t) volume := by
  haveI : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) t)) := ⟨by simp [Real.volume_Ioc]⟩
  refine Integrable.mono' (integrable_const (4 * (1 + t))) ?_ ?_
  · exact ((Real.measurable_exp.comp (by fun_prop)).mul
      measurable_unitRieszStirlingCorrection).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    have hs0 : (0 : ℝ) < s := hs.1
    have hst : s ≤ t := hs.2
    have h1 : Real.exp (-(b * (t - s))) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith
    have h1p : (0 : ℝ) < Real.exp (-(b * (t - s))) := Real.exp_pos _
    have ha := abs_unitRieszStirlingCorrection_le hs0.le
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos h1p]
    nlinarith [ha, h1p, abs_nonneg (unitRieszStirlingCorrection s)]

theorem unitRieszStirlingConvolution_eq {t : ℝ} (ht : 0 ≤ t) :
    unitRieszStirlingConvolution t =
      3 * (∫ s in Ioc (0 : ℝ) t,
          Real.exp (-(1 * (t - s))) * unitRieszStirlingCorrection s) -
        3 * (∫ s in Ioc (0 : ℝ) t,
          Real.exp (-(3 / 2 * (t - s))) * unitRieszStirlingCorrection s) := by
  have hpt : ∀ s ∈ Ioc (0 : ℝ) t,
      unitRieszCompletedSourceKernel (t - s) * unitRieszStirlingCorrection s =
        3 * (Real.exp (-(1 * (t - s))) * unitRieszStirlingCorrection s) -
          3 * (Real.exp (-(3 / 2 * (t - s))) * unitRieszStirlingCorrection s) := by
    intro s _
    have e1 : Real.exp (-(t - s)) = Real.exp (-(1 * (t - s))) := by congr 1; ring
    have e2 : Real.exp (-3 * (t - s) / 2) = Real.exp (-(3 / 2 * (t - s))) := by congr 1; ring
    rw [unitRieszCompletedSourceKernel, e1, e2]
    ring
  have hI1 := integrableOn_exp_mul_unitRieszStirlingCorrection (b := 1) (by norm_num) ht
  have hI2 := integrableOn_exp_mul_unitRieszStirlingCorrection (b := 3 / 2) (by norm_num) ht
  have hs1 : IntegrableOn
      (fun s : ℝ => 3 * (Real.exp (-(1 * (t - s))) * unitRieszStirlingCorrection s))
      (Ioc (0 : ℝ) t) volume := hI1.const_mul 3
  have hs2 : IntegrableOn
      (fun s : ℝ => 3 * (Real.exp (-(3 / 2 * (t - s))) * unitRieszStirlingCorrection s))
      (Ioc (0 : ℝ) t) volume := hI2.const_mul 3
  rw [unitRieszStirlingConvolution, setIntegral_congr_fun measurableSet_Ioc hpt,
    integral_sub hs1 hs2, MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]

/-- **Equation (22).**  The Stirling convolution is nonpositive at every aperture. -/
theorem unitRieszStirlingConvolution_nonpos {t : ℝ} (ht : 0 ≤ t) :
    unitRieszStirlingConvolution t ≤ 0 := by
  refine setIntegral_nonpos measurableSet_Ioc ?_
  intro s hs
  have hs0 : (0 : ℝ) < s := hs.1
  have hst : s ≤ t := hs.2
  have hk : 0 ≤ unitRieszCompletedSourceKernel (t - s) :=
    unitRieszCompletedSourceKernel_nonneg (by linarith)
  have ha : unitRieszStirlingCorrection s < 0 := unitRieszStirlingCorrection_neg hs0.le
  nlinarith

theorem integral_Ioc_linear (t : ℝ) (ht : 0 ≤ t) :
    (∫ s in Ioc (0 : ℝ) t, (s + 4)) = t ^ 2 / 2 + 4 * t := by
  have hd : ∀ x ∈ Set.uIcc (0 : ℝ) t, HasDerivAt (fun y : ℝ => y ^ 2 / 2 + 4 * y) (x + 4) x := by
    intro x _
    have h1 : HasDerivAt (fun y : ℝ => y ^ 2) ((2 : ℕ) * x ^ (2 - 1)) x := hasDerivAt_pow 2 x
    have h2 := h1.div_const 2
    have h3 := (hasDerivAt_id x).const_mul (4 : ℝ)
    exact (h2.add h3).congr_deriv (by push_cast; ring)
  rw [← intervalIntegral.integral_of_le ht,
    intervalIntegral.integral_eq_sub_of_hasDerivAt hd
      ((continuous_id.add continuous_const).intervalIntegrable _ _)]
  ring

/-- **Equation (23).**  Exact polynomial-times-exponential bound for the Stirling
convolution. -/
theorem abs_unitRieszStirlingConvolution_le {t : ℝ} (ht : 0 ≤ t) :
    |unitRieszStirlingConvolution t| ≤ 3 * Real.exp (-t) * (t ^ 2 / 2 + 4 * t) := by
  have hnonpos := unitRieszStirlingConvolution_nonpos ht
  have hkint : IntegrableOn
      (fun s : ℝ => unitRieszCompletedSourceKernel (t - s) * unitRieszStirlingCorrection s)
      (Ioc (0 : ℝ) t) volume := by
    have hI1 := integrableOn_exp_mul_unitRieszStirlingCorrection (b := 1) (by norm_num) ht
    have hI2 := integrableOn_exp_mul_unitRieszStirlingCorrection (b := 3 / 2) (by norm_num) ht
    have hs1 : IntegrableOn
        (fun s : ℝ => 3 * (Real.exp (-(1 * (t - s))) * unitRieszStirlingCorrection s))
        (Ioc (0 : ℝ) t) volume := hI1.const_mul 3
    have hs2 : IntegrableOn
        (fun s : ℝ => 3 * (Real.exp (-(3 / 2 * (t - s))) * unitRieszStirlingCorrection s))
        (Ioc (0 : ℝ) t) volume := hI2.const_mul 3
    refine (hs1.sub hs2).congr_fun ?_ measurableSet_Ioc
    intro s _
    have e1 : Real.exp (-(t - s)) = Real.exp (-(1 * (t - s))) := by congr 1; ring
    have e2 : Real.exp (-3 * (t - s) / 2) = Real.exp (-(3 / 2 * (t - s))) := by congr 1; ring
    show 3 * (Real.exp (-(1 * (t - s))) * unitRieszStirlingCorrection s) -
        3 * (Real.exp (-(3 / 2 * (t - s))) * unitRieszStirlingCorrection s) =
      unitRieszCompletedSourceKernel (t - s) * unitRieszStirlingCorrection s
    rw [unitRieszCompletedSourceKernel, e1, e2]
    ring
  haveI : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) t)) := ⟨by simp [Real.volume_Ioc]⟩
  have hmajint : IntegrableOn (fun s : ℝ => 3 * Real.exp (-t) * (s + 4))
      (Ioc (0 : ℝ) t) volume :=
    ((continuous_const.mul (continuous_id.add continuous_const)).integrableOn_Icc).mono_set
      Ioc_subset_Icc_self
  have hmono : (∫ s in Ioc (0 : ℝ) t,
      -(unitRieszCompletedSourceKernel (t - s) * unitRieszStirlingCorrection s)) ≤
      ∫ s in Ioc (0 : ℝ) t, 3 * Real.exp (-t) * (s + 4) := by
    refine setIntegral_mono_on hkint.neg hmajint measurableSet_Ioc ?_
    intro s hs
    have hs0 : (0 : ℝ) < s := hs.1
    have hst : s ≤ t := hs.2
    have hk : unitRieszCompletedSourceKernel (t - s) ≤ 3 * Real.exp (-(t - s)) :=
      unitRieszCompletedSourceKernel_le (by linarith)
    have hk0 : 0 ≤ unitRieszCompletedSourceKernel (t - s) :=
      unitRieszCompletedSourceKernel_nonneg (by linarith)
    have ha := unitRieszStirlingCorrection_lower hs0.le
    have hane : unitRieszStirlingCorrection s < 0 := unitRieszStirlingCorrection_neg hs0.le
    have hsplit : Real.exp (-(t - s)) * Real.exp (-s) = Real.exp (-t) := by
      rw [← Real.exp_add]; congr 1; ring
    have hexp : (0 : ℝ) < Real.exp (-s) := Real.exp_pos _
    have hstep : -(unitRieszCompletedSourceKernel (t - s) * unitRieszStirlingCorrection s) ≤
        3 * Real.exp (-(t - s)) * ((s + 4) * Real.exp (-s)) := by
      nlinarith [hk, hk0, ha, hane, Real.exp_pos (-(t - s))]
    calc -(unitRieszCompletedSourceKernel (t - s) * unitRieszStirlingCorrection s)
        ≤ 3 * Real.exp (-(t - s)) * ((s + 4) * Real.exp (-s)) := hstep
      _ = 3 * Real.exp (-t) * (s + 4) := by
          rw [show 3 * Real.exp (-(t - s)) * ((s + 4) * Real.exp (-s)) =
            3 * (Real.exp (-(t - s)) * Real.exp (-s)) * (s + 4) from by ring, hsplit]
  rw [MeasureTheory.integral_neg, MeasureTheory.integral_const_mul,
    integral_Ioc_linear t ht] at hmono
  rw [abs_of_nonpos hnonpos, unitRieszStirlingConvolution]
  linarith

/-- **Equation (24).**  The Stirling convolution is uniformly dominated by the half-unit
exponential. -/
theorem abs_unitRieszStirlingConvolution_le_exp {t : ℝ} (ht : 0 ≤ t) :
    |unitRieszStirlingConvolution t| ≤ 48 * Real.exp (-t / 2) := by
  have h := abs_unitRieszStirlingConvolution_le ht
  have e4 : Real.exp (-(1 / 4 * t)) * Real.exp (-(1 / 4 * t)) = Real.exp (-t / 2) := by
    rw [← Real.exp_add]; congr 1; ring
  have e2 : Real.exp (-t / 2) * Real.exp (-t / 2) = Real.exp (-t) := by
    rw [← Real.exp_add]; congr 1; ring
  have hq : t * Real.exp (-(1 / 4 * t)) ≤ 1 / (1 / 4 : ℝ) :=
    mul_exp_neg_le_inv (by norm_num) ht
  have hq4 : t * Real.exp (-(1 / 4 * t)) ≤ 4 := by norm_num at hq; linarith
  have hh : t * Real.exp (-(1 / 2 * t)) ≤ 1 / (1 / 2 : ℝ) :=
    mul_exp_neg_le_inv (by norm_num) ht
  have hhrw : Real.exp (-(1 / 2 * t)) = Real.exp (-t / 2) := by congr 1; ring
  have hh' : t * Real.exp (-t / 2) ≤ 2 := by
    rw [hhrw] at hh; norm_num at hh; linarith
  have hq0 : (0 : ℝ) ≤ t * Real.exp (-(1 / 4 * t)) := by positivity
  have hsq : t ^ 2 * Real.exp (-t / 2) ≤ 16 := by
    have hrw : t ^ 2 * Real.exp (-t / 2) = (t * Real.exp (-(1 / 4 * t))) ^ 2 := by
      rw [← e4]; ring
    rw [hrw]
    nlinarith [hq4, hq0]
  have hpos : (0 : ℝ) < Real.exp (-t / 2) := Real.exp_pos _
  have hfinal : 3 * Real.exp (-t) * (t ^ 2 / 2 + 4 * t) ≤ 48 * Real.exp (-t / 2) := by
    rw [← e2]
    nlinarith [hsq, hh', hpos]
  linarith

/-! ## The Laplace transform of the Stirling convolution -/

theorem unitRieszStirlingCorrection_linear_bound :
    ∀ t : ℝ, 0 < t → |unitRieszStirlingCorrection t| ≤ 4 * (1 + t) :=
  fun t ht => abs_unitRieszStirlingCorrection_le ht.le

theorem unitRieszStirlingConvolution_laplace {z : ℂ} (hz : 0 < z.re) :
    (∫ t in Ioi (0 : ℝ),
        Complex.exp (-(z * (t : ℂ))) * ((unitRieszStirlingConvolution t : ℝ) : ℂ)) =
      (3 * (z + ((1 : ℝ) : ℂ))⁻¹ - 3 * (z + ((3 / 2 : ℝ) : ℂ))⁻¹) *
        ∫ t in Ioi (0 : ℝ),
          Complex.exp (-(z * (t : ℂ))) * ((unitRieszStirlingCorrection t : ℝ) : ℂ) := by
  have hbnd := unitRieszStirlingCorrection_linear_bound
  have hpt : ∀ t ∈ Ioi (0 : ℝ),
      Complex.exp (-(z * (t : ℂ))) * ((unitRieszStirlingConvolution t : ℝ) : ℂ) =
        3 * (Complex.exp (-(z * (t : ℂ))) *
            ((∫ s in Ioc (0 : ℝ) t,
              Real.exp (-(1 * (t - s))) * unitRieszStirlingCorrection s : ℝ) : ℂ)) -
          3 * (Complex.exp (-(z * (t : ℂ))) *
            ((∫ s in Ioc (0 : ℝ) t,
              Real.exp (-(3 / 2 * (t - s))) * unitRieszStirlingCorrection s : ℝ) : ℂ)) := by
    intro t ht
    rw [unitRieszStirlingConvolution_eq (le_of_lt ht)]
    push_cast
    ring
  have hi1 := integrableOn_Ioi_cexp_mul_expVolterra (b := 1) (by norm_num) hz
    measurable_unitRieszStirlingCorrection hbnd
  have hi2 := integrableOn_Ioi_cexp_mul_expVolterra (b := 3 / 2) (by norm_num) hz
    measurable_unitRieszStirlingCorrection hbnd
  have h1c : IntegrableOn
      (fun t : ℝ => 3 * (Complex.exp (-(z * (t : ℂ))) *
        ((∫ s in Ioc (0 : ℝ) t,
          Real.exp (-(1 * (t - s))) * unitRieszStirlingCorrection s : ℝ) : ℂ)))
      (Ioi (0 : ℝ)) volume := hi1.const_mul 3
  have h2c : IntegrableOn
      (fun t : ℝ => 3 * (Complex.exp (-(z * (t : ℂ))) *
        ((∫ s in Ioc (0 : ℝ) t,
          Real.exp (-(3 / 2 * (t - s))) * unitRieszStirlingCorrection s : ℝ) : ℂ)))
      (Ioi (0 : ℝ)) volume := hi2.const_mul 3
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_sub h1c h2c,
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
    integral_Ioi_expVolterra_laplace (b := 1) (by norm_num) hz
      measurable_unitRieszStirlingCorrection hbnd,
    integral_Ioi_expVolterra_laplace (b := 3 / 2) (by norm_num) hz
      measurable_unitRieszStirlingCorrection hbnd]
  ring

end GaloisForLFunctions.RHTower
