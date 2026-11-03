import GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering.TheEisensteinPeriodIsAHeckeEigenfunctionForEveryPrime
import GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering.CauchyWindowRangeDensity
import GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering.LewisHeckeEisensteinEigenvalue
import GaloisForLFunctions.HTGeometry.AnalyticPrimitive
import GaloisForLFunctions.HTGeometry.TwoSidedExponentialMoments
import Mathlib.Analysis.Convolution

/-!
# Global continuation of the literal Cauchy core

Removing the theta field's constant lower trace gives an exponentially decaying
logarithmic source. Its Cauchy average and the retained step response are real
analytic. Connected continuation then identifies the literal core with the global
completed Lewis period minus its two explicit boundary channels.
-/

set_option autoImplicit false
noncomputable section
open Complex Set MeasureTheory Filter Topology
open scoped ENNReal
open GaloisForLFunctions RenormalizedIntersectionTheory
open MayerScatteringCore MayerQuadraticCone MayerEpsteinHeightMeasurability

namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering

private theorem field_tail_coefficient_nonneg (w : ℂ) : 0 ≤ tailCoefficient w := by
  unfold tailCoefficient
  exact div_nonneg (_root_.RHTower.tailConst_nonneg _) (by positivity)

private theorem field_corrected_large_bound {w : ℂ} (hw : 0 < w.re) (him : 0 < w.im)
    {a : ℝ} (ha : 1 ≤ a) :
    ‖fieldCore w a + riemannZeta w * (a : ℂ) ^ (-w)‖ ≤
      (‖scatteringCoefficient w‖ + tailCoefficient w) * a ^ (-1 : ℝ) := by
  have ha0 : 0 < a := zero_lt_one.trans_le ha
  have he : fieldCore w a + riemannZeta w * (a : ℂ) ^ (-w) =
      normalizedTail w a - scatteringCoefficient w * (a : ℂ) ^ (-1 : ℂ) := by
    rw [fieldCore_eq_tail hw him ha0]
    ring
  rw [he]
  calc
    _ ≤ ‖normalizedTail w a‖ + ‖scatteringCoefficient w * (a : ℂ) ^ (-1 : ℂ)‖ := norm_sub_le _ _
    _ ≤ tailCoefficient w * a ^ (-w.re / 2 - 1) +
        ‖scatteringCoefficient w‖ * a ^ (-1 : ℝ) := by
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ha0]
      exact add_le_add (normalizedTail_norm_le ha) (by norm_num)
    _ ≤ tailCoefficient w * a ^ (-1 : ℝ) + ‖scatteringCoefficient w‖ * a ^ (-1 : ℝ) :=
      add_le_add (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le ha (by linarith only [hw]))
        (field_tail_coefficient_nonneg w)) le_rfl
    _ = _ := by ring

private theorem field_corrected_small_bound {w : ℂ} (hw : 0 < w.re) (him : 0 < w.im)
    {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    ‖fieldCore w a + riemannZeta w‖ ≤
      (‖scatteringCoefficient w‖ + tailCoefficient w) * a ^ (1 - w.re) := by
  have hi : 1 ≤ 1 / a := (le_div_iff₀ ha).mpr (by simpa only [one_mul] using ha1)
  have hp : (a : ℂ) ^ (-w) * ((1 / a : ℝ) : ℂ) ^ (-w) = 1 := by
    rw [← Complex.mul_cpow_ofReal_nonneg ha.le (one_div_pos.mpr ha).le, ← Complex.ofReal_mul]
    have hunit : a * (1 / a) = 1 := by field_simp [ha.ne']
    rw [hunit, Complex.ofReal_one, Complex.one_cpow]
  have he : fieldCore w a + riemannZeta w =
      (a : ℂ) ^ (-w) * (fieldCore w (1 / a) +
        riemannZeta w * ((1 / a : ℝ) : ℂ) ^ (-w)) := by
    rw [fieldCore_reciprocity hw him ha]
    linear_combination -riemannZeta w * hp
  rw [he, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ha, Complex.neg_re]
  calc
    _ ≤ a ^ (-w.re) * ((‖scatteringCoefficient w‖ + tailCoefficient w) *
        (1 / a) ^ (-1 : ℝ)) :=
      mul_le_mul_of_nonneg_left (field_corrected_large_bound hw him hi)
        (Real.rpow_pos_of_pos ha _).le
    _ = (‖scatteringCoefficient w‖ + tailCoefficient w) *
        (a ^ (-w.re) * a ^ (1 : ℝ)) := by
      rw [Real.rpow_neg_one, one_div, inv_inv, Real.rpow_one]
      ring
    _ = _ := by rw [← Real.rpow_add ha]; congr 2; ring

private theorem field_boundary_bounds {w : ℂ} (hw : 0 < w.re) (hw1 : w.re < 1)
    (him : 0 < w.im) :
    ∃ C : ℝ, 0 ≤ C ∧
      (∀ a ≥ 1, ‖fieldCore w a‖ ≤ C * a ^ (-w.re)) ∧
      (∀ a > 0, a ≤ 1 → ‖fieldCore w a + riemannZeta w‖ ≤ C * a ^ (1 - w.re)) := by
  let C := ‖riemannZeta w‖ + ‖scatteringCoefficient w‖ + tailCoefficient w
  have hT := field_tail_coefficient_nonneg w
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_, ?_⟩
  · intro a ha
    have h1 : a ^ (-1 : ℝ) ≤ a ^ (-w.re) :=
      Real.rpow_le_rpow_of_exponent_le ha (by linarith only [hw1])
    have h2 : a ^ (-w.re / 2 - 1) ≤ a ^ (-w.re) :=
      Real.rpow_le_rpow_of_exponent_le ha (by linarith only [hw1])
    calc
      _ ≤ ‖riemannZeta w‖ * a ^ (-w.re) + ‖scatteringCoefficient w‖ * a ^ (-1 : ℝ) +
          tailCoefficient w * a ^ (-w.re / 2 - 1) := core_large_bound hw him ha
      _ ≤ ‖riemannZeta w‖ * a ^ (-w.re) + ‖scatteringCoefficient w‖ * a ^ (-w.re) +
          tailCoefficient w * a ^ (-w.re) :=
        add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_left h1 (norm_nonneg _)))
          (mul_le_mul_of_nonneg_left h2 hT)
      _ = _ := by dsimp only [C]; ring
  · intro a ha ha1
    exact (field_corrected_small_bound hw him ha ha1).trans
      (mul_le_mul_of_nonneg_right (by dsimp only [C]; linarith only [norm_nonneg (riemannZeta w)])
        (Real.rpow_pos_of_pos ha _).le)

/-- The single nonresonant field trace is retained outside the Haar-integrable source remainder. -/
def mayerFieldLogRemainder (s : ℂ) (x : ℝ) : ℂ :=
  Gammaℝ (2 * s) * (fieldCore (2 * s) (Real.exp (-x)) +
    (Ioi (0 : ℝ)).indicator (fun _ => riemannZeta (2 * s)) x)

private theorem measurable_field_log_remainder {s : ℂ} (him : 0 < s.im) :
    Measurable (mayerFieldLogRemainder s) := by
  have hwi : 0 < (2 * s).im := by simp; linarith only [him]
  have hw0 : 2 * s ≠ 0 := by intro h; rw [h, Complex.zero_im] at hwi; exact lt_irrefl _ hwi
  have hw2 : 2 * s ≠ 2 := by intro h; rw [h] at hwi; norm_num at hwi
  have he := measurable_epsteinField hw0 hw2
  have hf : Measurable (fieldCore (2 * s)) := by unfold fieldCore scatteringPowers; fun_prop
  have hi : Measurable ((Ioi (0 : ℝ)).indicator (fun _ => riemannZeta (2 * s))) :=
    measurable_const.indicator measurableSet_Ioi
  unfold mayerFieldLogRemainder
  fun_prop

/-- Removing the literal field trace gives exponential decay at both logarithmic endpoints. -/
theorem mayerFieldLogRemainder_exponential_bound {s : ℂ}
    (hs : 0 < s.re) (hs1 : s.re < 1 / 2) (him : 0 < s.im) :
    ∃ C ε : ℝ, 0 ≤ C ∧ 0 < ε ∧ ∀ x : ℝ,
      ‖mayerFieldLogRemainder s x‖ ≤ C * Real.exp (-(ε * |x|)) := by
  have hw : 0 < (2 * s).re := by simp; linarith only [hs]
  have hw1 : (2 * s).re < 1 := by simp; linarith only [hs1]
  have hwi : 0 < (2 * s).im := by simp; linarith only [him]
  obtain ⟨C, hC, hlarge, hsmall⟩ := field_boundary_bounds hw hw1 hwi
  let ε := min (2 * s).re (1 - (2 * s).re)
  have hε : 0 < ε := lt_min hw (by linarith only [hw1])
  have hεw : ε ≤ (2 * s).re := min_le_left _ _
  have hεb : ε ≤ 1 - (2 * s).re := min_le_right _ _
  refine ⟨‖Gammaℝ (2 * s)‖ * C, ε, mul_nonneg (norm_nonneg _) hC, hε, fun x => ?_⟩
  rw [mayerFieldLogRemainder, norm_mul]
  have hf : ‖fieldCore (2 * s) (Real.exp (-x)) +
      (Ioi (0 : ℝ)).indicator (fun _ => riemannZeta (2 * s)) x‖ ≤
      C * Real.exp (-(ε * |x|)) := by
    by_cases hx : 0 < x
    · rw [indicator_of_mem (show x ∈ Ioi (0 : ℝ) from hx)]
      have ha : Real.exp (-x) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith only [hx])
      have hb := hsmall (Real.exp (-x)) (Real.exp_pos _) ha
      rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp] at hb
      apply hb.trans
      apply mul_le_mul_of_nonneg_left _ hC
      apply Real.exp_le_exp.mpr
      rw [abs_of_pos hx]
      nlinarith only [mul_le_mul_of_nonneg_right hεb hx.le]
    · have hx0 : x ≤ 0 := le_of_not_gt hx
      rw [indicator_of_notMem (show x ∉ Ioi (0 : ℝ) from hx), add_zero]
      have ha : 1 ≤ Real.exp (-x) := Real.one_le_exp_iff.mpr (by linarith only [hx0])
      have hb := hlarge (Real.exp (-x)) ha
      rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp] at hb
      apply hb.trans
      apply mul_le_mul_of_nonneg_left _ hC
      apply Real.exp_le_exp.mpr
      rw [abs_of_nonpos hx0]
      nlinarith only [mul_le_mul_of_nonneg_right hεw (neg_nonneg.mpr hx0)]
  exact (mul_le_mul_of_nonneg_left hf (norm_nonneg _)).trans_eq (mul_assoc _ _ _).symm

/-- The nonresonant field remainder belongs to both source spaces used by literal convolution
and Cauchy strip smoothing. -/
theorem mayerFieldLogRemainder_integrable_memLp {s : ℂ}
    (hs : 0 < s.re) (hs1 : s.re < 1 / 2) (him : 0 < s.im) :
    Integrable (mayerFieldLogRemainder s) ∧ MemLp (mayerFieldLogRemainder s) 2 := by
  obtain ⟨C, ε, hC, hε, hb⟩ := mayerFieldLogRemainder_exponential_bound hs hs1 him
  have hbase : Integrable (fun x : ℝ => Real.exp (-(ε * |x|))) := by
    simpa only [pow_zero, one_mul, neg_mul] using
      _root_.HTGeometry.integrable_abs_pow_mul_exp_neg_abs 0 hε
  have hi : Integrable (mayerFieldLogRemainder s) :=
    (hbase.const_mul C).mono' (measurable_field_log_remainder him).aestronglyMeasurable
      (Eventually.of_forall hb)
  refine ⟨hi, _root_.RHTower.memLp_two_of_integrable_of_norm_le (C := C) hi (fun x => ?_)⟩
  exact (hb x).trans ((mul_le_mul_of_nonneg_left
    (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hε.le (abs_nonneg x)))) hC).trans_eq
      (mul_one C))

#print axioms mayerFieldLogRemainder_exponential_bound
#print axioms mayerFieldLogRemainder_integrable_memLp


private theorem analyticAt_cauchy_log_kernel (s : ℂ) (x : ℝ) :
    AnalyticAt ℝ (mayerCauchyHaarKernel s) x := by
  have he : AnalyticAt ℝ (fun y : ℝ => Real.exp (-y)) x :=
    analyticAt_id.neg.rexp
  have heC : AnalyticAt ℝ (fun y : ℝ => (Real.exp (-y) : ℂ)) x :=
    (Complex.ofRealCLM.analyticAt _).comp he
  have hb : AnalyticAt ℝ (fun y : ℝ => ((1 + (Real.exp (-y)) ^ 2 : ℝ) : ℂ)) x :=
    (Complex.ofRealCLM.analyticAt _).comp (analyticAt_const.add (he.pow 2))
  have hpos : 0 < 1 + (Real.exp (-x)) ^ 2 := by positivity
  have hp : AnalyticAt ℂ (fun z : ℂ => z ^ (-((2 * s + 2) / 2)))
      ((1 + (Real.exp (-x)) ^ 2 : ℝ) : ℂ) :=
    analyticAt_id.cpow analyticAt_const (Complex.ofReal_mem_slitPlane.mpr hpos)
  have hpR : AnalyticAt ℝ (fun z : ℂ => z ^ (-((2 * s + 2) / 2)))
      ((1 + (Real.exp (-x)) ^ 2 : ℝ) : ℂ) := hp.restrictScalars
  have hc := hpR.comp (x := x)
    (f := fun y : ℝ => ((1 + (Real.exp (-y)) ^ 2 : ℝ) : ℂ)) hb
  exact analyticAt_const.mul ((analyticAt_const.mul heC).mul hc)

private theorem continuous_cauchy_log_kernel (s : ℂ) : Continuous (mayerCauchyHaarKernel s) :=
  continuous_iff_continuousAt.mpr fun x => (analyticAt_cauchy_log_kernel s x).continuousAt

private theorem bounded_cauchy_log_kernel {s : ℂ} (hs : 0 < s.re) :
    BddAbove (range fun x => ‖mayerCauchyHaarKernel s x‖) := by
  refine ⟨‖(Gammaℝ (2 * s))⁻¹‖ * ‖(averagingFactor (2 * s))⁻¹‖, ?_⟩
  rintro _ ⟨x, rfl⟩
  let t := Real.exp (-x)
  have ht : 0 < t := Real.exp_pos _
  have hw : 0 ≤ (2 * s).re := by simp; linarith only [hs]
  have hprod : t * ‖cauchyWeight (2 * s) t‖ ≤ 1 := by
    by_cases ht1 : t ≤ 1
    · exact (mul_le_mul_of_nonneg_left
        (MayerEpsteinEndpointBounds.norm_cauchyWeight_le_one hw t) ht.le).trans
        (by simpa only [mul_one] using ht1)
    · have hlarge : 1 ≤ t := (lt_of_not_ge ht1).le
      calc
        _ ≤ t * t ^ (-(2 * s).re - 2) := mul_le_mul_of_nonneg_left
          (MayerEpsteinEndpointBounds.norm_cauchyWeight_le_power hw ht) ht.le
        _ = t ^ (-(2 * s).re - 1) := by
          calc
            _ = t ^ (1 : ℝ) * t ^ (-(2 * s).re - 2) := by rw [Real.rpow_one]
            _ = _ := by
              rw [← Real.rpow_add ht]
              congr 1
              ring
        _ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hlarge (by linarith only [hw])
  change ‖(Gammaℝ (2 * s))⁻¹ * ((averagingFactor (2 * s))⁻¹ * (t : ℂ) *
    cauchyWeight (2 * s) t)‖ ≤ _
  rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
  calc
    _ = (‖(Gammaℝ (2 * s))⁻¹‖ * ‖(averagingFactor (2 * s))⁻¹‖) *
      (t * ‖cauchyWeight (2 * s) t‖) := by ring
    _ ≤ _ := (mul_le_mul_of_nonneg_left hprod (by positivity)).trans_eq (mul_one _)

/-- The literal convolution of the retained source remainder is real analytic everywhere. -/
theorem mayerFieldLogRemainder_cauchy_analytic {s : ℂ}
    (hs : 0 < s.re) (hs1 : s.re < 1 / 2) (him : 0 < s.im) :
    ∀ x : ℝ, AnalyticAt ℝ
      (fun y : ℝ => ∫ z : ℝ, mayerCauchyHaarKernel s z * mayerFieldLogRemainder s (y - z)) x := by
  obtain ⟨hi, hL⟩ := mayerFieldLogRemainder_integrable_memLp hs hs1 him
  let f : Lp ℂ 2 (volume : Measure ℝ) := hL.toLp (mayerFieldLogRemainder s)
  obtain ⟨F, hF, hAE⟩ := mayerCauchyHaarOperator_analytic_representative s hs f
  have hcoe : (f : ℝ → ℂ) =ᵐ[volume] mayerFieldLogRemainder s := hL.coeFn_toLp
  have hconv : (fun y : ℝ => ∫ z : ℝ, mayerCauchyHaarKernel s z *
      mayerFieldLogRemainder s (y - z)) =ᵐ[volume] fun x : ℝ => F (x : ℂ) := by
    filter_upwards [mayerCauchyHaarOperator_coeFn s hs f, hAE] with y hy hFy
    rw [← hFy, hy]
    calc
      _ = ∫ z : ℝ, mayerCauchyHaarKernel s (y - z) * mayerFieldLogRemainder s z := by
        have he := integral_sub_left_eq_self
          (fun z : ℝ => mayerCauchyHaarKernel s z * mayerFieldLogRemainder s (y - z)) volume y
        simpa only [sub_sub_self] using he.symm
      _ = _ := integral_congr_ae (hcoe.mono fun z hz => by rw [hz])
  have hcont : Continuous (fun y : ℝ => ∫ z : ℝ, mayerCauchyHaarKernel s z *
      mayerFieldLogRemainder s (y - z)) :=
    (bounded_cauchy_log_kernel hs).continuous_convolution_left_of_integrable
      (ContinuousLinearMap.mul ℂ ℂ) (continuous_cauchy_log_kernel s) hi
  have hreal : ∀ x : ℝ, AnalyticAt ℝ (fun y : ℝ => F (y : ℂ)) x := by
    intro x
    have hx : |(x : ℂ).im| < Real.pi / 4 := by simpa using (by positivity : (0 : ℝ) < Real.pi / 4)
    exact (hF _ hx).restrictScalars.comp (Complex.ofRealCLM.analyticAt x)
  have he := (hcont.ae_eq_iff_eq volume
    (continuous_iff_continuousAt.mpr fun x => (hreal x).continuousAt)).mp hconv
  rw [he]
  exact hreal

#print axioms mayerFieldLogRemainder_cauchy_analytic


private theorem analyticAt_cauchy_cumulative {s : ℂ} (hs : 0 < s.re) (x₀ : ℝ) :
    AnalyticAt ℝ (fun x : ℝ => ∫ z in Iic x, mayerCauchyHaarKernel s z) x₀ := by
  let k := mayerCauchyHaarKernel s
  have hk : Integrable k := integrable_mayerCauchyHaarKernel s hs
  have hshift : AnalyticAt ℝ (fun t : ℝ => k (t + x₀)) 0 := by
    have hf : AnalyticAt ℝ k ((0 : ℝ) + x₀) := by
      simpa only [zero_add] using analyticAt_cauchy_log_kernel s x₀
    exact hf.comp (x := (0 : ℝ)) (f := fun t : ℝ => t + x₀)
      (analyticAt_id.add analyticAt_const)
  have hR : AnalyticAt ℝ (fun t : ℝ => (k (t + x₀)).re) 0 :=
    (Complex.reCLM.analyticAt _).comp hshift
  have hI : AnalyticAt ℝ (fun t : ℝ => (k (t + x₀)).im) 0 :=
    (Complex.imCLM.analyticAt _).comp hshift
  let P : ℝ → ℂ := fun x =>
    (HTGeometry.primitiveAtZero (fun t : ℝ => (k (t + x₀)).re) x : ℂ) +
      (HTGeometry.primitiveAtZero (fun t : ℝ => (k (t + x₀)).im) x : ℂ) * I
  have hP : AnalyticAt ℝ P 0 :=
    ((Complex.ofRealCLM.analyticAt _).comp (HTGeometry.analyticAt_primitiveAtZero hR)).add
      (((Complex.ofRealCLM.analyticAt _).comp
        (HTGeometry.analyticAt_primitiveAtZero hI)).mul analyticAt_const)
  have htrans : AnalyticAt ℝ (fun x : ℝ => P (x - x₀)) x₀ := by
    have hsub : AnalyticAt ℝ (fun x : ℝ => x - x₀) x₀ :=
      analyticAt_id.sub analyticAt_const
    have hPa : AnalyticAt ℝ P (x₀ - x₀) := by simpa only [sub_self] using hP
    exact hPa.comp (x := x₀) (f := fun x : ℝ => x - x₀) hsub
  have he (x : ℝ) : P (x - x₀) = ∫ z in x₀..x, k z := by
    have hi : IntervalIntegrable (fun t : ℝ => k (t + x₀)) volume 0 (x - x₀) :=
      ((continuous_cauchy_log_kernel s).comp
        (continuous_id.add continuous_const)).intervalIntegrable _ _
    calc
      _ = ∫ t in (0 : ℝ)..(x - x₀), k (t + x₀) := by
        dsimp only [P, HTGeometry.primitiveAtZero]
        have hre : (∫ t in (0 : ℝ)..(x - x₀), (k (t + x₀)).re) =
            (∫ t in (0 : ℝ)..(x - x₀), k (t + x₀)).re := intervalIntegral.intervalIntegral_re hi
        have him : (∫ t in (0 : ℝ)..(x - x₀), (k (t + x₀)).im) =
            (∫ t in (0 : ℝ)..(x - x₀), k (t + x₀)).im := intervalIntegral.intervalIntegral_im hi
        rw [hre, him]
        exact Complex.re_add_im _
      _ = _ := by
        rw [intervalIntegral.integral_comp_add_right]
        simp only [zero_add, sub_add_cancel]
  have hfun : (fun x : ℝ => ∫ z in Iic x, k z) =
      fun x => (∫ z in Iic x₀, k z) + P (x - x₀) := by
    funext x
    rw [he, ← intervalIntegral.integral_Iic_sub_Iic hk.integrableOn hk.integrableOn]
    ring
  change AnalyticAt ℝ (fun x : ℝ => ∫ z in Iic x, k z) x₀
  rw [hfun]
  exact analyticAt_const.add htrans


private theorem literal_core_log_integral (s : ℂ) (x : ℝ) :
    mayerPeriodCore s (Real.exp (-x)) = ∫ z : ℝ,
      cauchyKernel (2 * s) (Real.exp (-z)) * fieldCore (2 * s) (Real.exp (-(x - z))) := by
  have hd : ∀ z ∈ (univ : Set ℝ),
      HasDerivWithinAt (Real.exp ∘ Neg.neg) (-Real.exp (-z)) univ z :=
    fun z _ => mul_neg_one (Real.exp (-z)) ▸
      ((Real.hasDerivAt_exp (-z)).comp z (hasDerivAt_neg z)).hasDerivWithinAt
  have he : Real.exp ∘ Neg.neg '' (univ : Set ℝ) = Ioi 0 := by
    rw [Set.image_comp, Set.image_univ_of_surjective neg_surjective,
      Set.image_univ, Real.range_exp]
  have hj : (univ : Set ℝ).InjOn (Real.exp ∘ Neg.neg) :=
    Real.exp_injective.injOn.comp neg_injective.injOn (univ.mapsTo_univ _)
  rw [mayerPeriodCore, _root_.RHTower.positiveMellinConvolution, ← he,
    integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ hd hj]
  simp only [Function.comp_apply, abs_neg, abs_of_pos (Real.exp_pos _), Measure.restrict_univ]
  apply integral_congr_ae
  filter_upwards with z
  have hz : (Real.exp (-z) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)
  have hxz : Real.exp (-x) / Real.exp (-z) = Real.exp (-(x - z)) := by
    rw [← Real.exp_sub]
    congr 1
    ring
  change (Real.exp (-z) : ℂ) * (cauchyKernel (2 * s) (Real.exp (-z)) *
    fieldCore (2 * s) (Real.exp (-x) / Real.exp (-z)) / (Real.exp (-z) : ℂ)) = _
  rw [hxz]
  field_simp

/-- The literal core splits into the analytic Cauchy average of its integrable field
remainder and the retained constant-field response. -/
theorem mayerPeriodCore_log_boundary_decomposition {s : ℂ}
    (hs : 0 < s.re) (hs1 : s.re < 1 / 2) (him : 0 < s.im) (x : ℝ) :
    mayerPeriodCore s (Real.exp (-x)) =
      (∫ z : ℝ, mayerCauchyHaarKernel s z * mayerFieldLogRemainder s (x - z)) -
        Gammaℝ (2 * s) * riemannZeta (2 * s) *
          ∫ z in Iic x, mayerCauchyHaarKernel s z := by
  have hg : Gammaℝ (2 * s) ≠ 0 :=
    Complex.Gammaℝ_ne_zero_of_re_pos (by simp; linarith only [hs])
  have hk := integrable_mayerCauchyHaarKernel s hs
  obtain ⟨C, ε, hC, hε, hb⟩ := mayerFieldLogRemainder_exponential_bound hs hs1 him
  have hbound (z : ℝ) : ‖mayerFieldLogRemainder s z‖ ≤ C :=
    (hb z).trans ((mul_le_mul_of_nonneg_left
      (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hε.le (abs_nonneg z)))) hC).trans_eq
        (mul_one C))
  have hi : Integrable (fun z : ℝ => mayerCauchyHaarKernel s z *
      mayerFieldLogRemainder s (x - z)) := by
    apply (hk.norm.mul_const C).mono'
    · exact ((measurable_mayerCauchyHaarKernel s).mul
        ((measurable_field_log_remainder him).comp
          (measurable_const.sub measurable_id))).aestronglyMeasurable
    · exact Eventually.of_forall fun z => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hbound _) (norm_nonneg _)
  have ht : Integrable (fun z : ℝ => Gammaℝ (2 * s) * riemannZeta (2 * s) *
      (Iio x).indicator (mayerCauchyHaarKernel s) z) :=
    (hk.indicator measurableSet_Iio).const_mul _
  rw [literal_core_log_integral]
  calc
    _ = ∫ z : ℝ, (mayerCauchyHaarKernel s z * mayerFieldLogRemainder s (x - z) -
        Gammaℝ (2 * s) * riemannZeta (2 * s) * (Iio x).indicator (mayerCauchyHaarKernel s) z) := by
      apply integral_congr_ae
      filter_upwards with z
      by_cases hz : z < x
      · have hxz : x - z ∈ Ioi (0 : ℝ) := sub_pos.mpr hz
        rw [indicator_of_mem (show z ∈ Iio x from hz), mayerFieldLogRemainder,
          indicator_of_mem hxz, mayerCauchyHaarKernel]
        field_simp [hg]
        ring
      · have hxz : x - z ∉ Ioi (0 : ℝ) := not_lt.mpr (sub_nonpos.mpr (le_of_not_gt hz))
        rw [indicator_of_notMem (show z ∉ Iio x from hz), mayerFieldLogRemainder,
          indicator_of_notMem hxz, mayerCauchyHaarKernel]
        field_simp [hg]
        ring
    _ = _ := by
      rw [integral_sub hi ht, integral_const_mul, integral_indicator measurableSet_Iio,
        integral_Iic_eq_integral_Iio]

#print axioms mayerPeriodCore_log_boundary_decomposition


/-- The literal Cauchy core is real analytic on the whole positive physical axis,
including nonresonant parameters. -/
theorem mayerPeriodCore_real_analytic {s : ℂ}
    (hs : 0 < s.re) (hs1 : s.re < 1 / 2) (him : 0 < s.im) :
    AnalyticOnNhd ℝ (mayerPeriodCore s) (Ioi 0) := by
  have hlog (x : ℝ) : AnalyticAt ℝ (fun y : ℝ => mayerPeriodCore s (Real.exp (-y))) x := by
    have he : (fun y : ℝ => mayerPeriodCore s (Real.exp (-y))) =
        fun y => (∫ z : ℝ, mayerCauchyHaarKernel s z * mayerFieldLogRemainder s (y - z)) -
          Gammaℝ (2 * s) * riemannZeta (2 * s) * ∫ z in Iic y, mayerCauchyHaarKernel s z :=
      funext (mayerPeriodCore_log_boundary_decomposition hs hs1 him)
    rw [he]
    exact (mayerFieldLogRemainder_cauchy_analytic hs hs1 him x).sub
      (analyticAt_const.mul (analyticAt_cauchy_cumulative hs x))
  intro a ha
  have ha0 : 0 < a := ha
  have hcomp := (hlog (-Real.log a)).comp (x := a)
    (f := fun x : ℝ => -Real.log x) (analyticAt_log ha0).neg
  apply hcomp.congr
  filter_upwards [isOpen_Ioi.mem_nhds ha] with x hx
  change mayerPeriodCore s (Real.exp (-(-Real.log x))) = mayerPeriodCore s x
  rw [neg_neg, Real.exp_log hx]

private theorem completed_period_real_analytic {s : ℂ} (hs : 0 < s.re) :
    AnalyticOnNhd ℝ (fun a : ℝ => eisensteinLewisPeriod s a) (Ioi 0) := by
  have hw : 0 < (2 * s).re := by simp; linarith only [hs]
  have ho : IsOpen MayerGlobalPeriods.domain :=
    isOpen_lt continuous_const Complex.continuous_re
  have hhol : AnalyticOnNhd ℂ (eisensteinLewisPeriod s) {a : ℂ | 0 < a.re} := by
    apply DifferentiableOn.analyticOnNhd _ (isOpen_lt continuous_const Complex.continuous_re)
    intro a ha
    change 0 < a.re at ha
    have hd : a - 1 ∈ MayerGlobalPeriods.domain := by
      change -1 < (a - 1).re
      simp only [Complex.sub_re, Complex.one_re]
      linarith only [ha]
    have hh := (MayerGlobalPeriods.extension_differentiableOn hw 1 (-riemannZeta (2 * s))
      (MayerScatteringMellin.state (2 * s))).differentiableAt (ho.mem_nhds hd)
    exact (hh.comp a (by fun_prop : DifferentiableAt ℂ (fun z : ℂ => z - 1) a)).differentiableWithinAt
  intro a ha
  have h := hhol (a : ℂ) (by simpa using ha)
  exact h.restrictScalars.comp (Complex.ofRealCLM.analyticAt a)

private theorem positive_cpow_real_analytic (w : ℂ) :
    AnalyticOnNhd ℝ (fun a : ℝ => (a : ℂ) ^ w) (Ioi 0) := by
  intro a ha
  have hp : AnalyticAt ℂ (fun z : ℂ => z ^ w) (a : ℂ) :=
    analyticAt_id.cpow analyticAt_const (Complex.ofReal_mem_slitPlane.mpr ha)
  exact hp.restrictScalars.comp (Complex.ofRealCLM.analyticAt a)

/-- The exact two boundary channels relate the actual PM core to the completed Lewis
period on every positive coordinate. Analytic continuation retains both coefficients. -/
theorem mayerPeriodCore_eq_eisenstein_sub_boundary {s : ℂ}
    (hs : 0 < s.re) (hs1 : s.re < 1 / 2) (him : 0 < s.im) {a : ℝ} (ha : 0 < a) :
    mayerPeriodCore s a = eisensteinLewisPeriod s a -
      riemannZeta (2 * s) * (1 + (a : ℂ) ^ (-(2 * s))) -
        (2 * riemannZeta (2 * s - 1) / (2 * s - 1)) * scatteringPowers (2 * s) a := by
  have hw : 0 < (2 * s).re := by simp; linarith only [hs]
  have hw1 : (2 * s).re < 1 := by simp; linarith only [hs1]
  have hwi : 0 < (2 * s).im := by simp; linarith only [him]
  have hr : 2 * s ∈ regularParameters :=
    mem_regularParameters_of_re hw hw1.ne (by linarith only [hw1])
  let B : ℝ → ℂ := fun x => eisensteinLewisPeriod s x -
    riemannZeta (2 * s) * (1 + (x : ℂ) ^ (-(2 * s))) -
      (2 * riemannZeta (2 * s - 1) / (2 * s - 1)) * scatteringPowers (2 * s) x
  have hB : AnalyticOnNhd ℝ B (Ioi 0) :=
    ((completed_period_real_analytic hs).sub
      (analyticOnNhd_const.mul (analyticOnNhd_const.add (positive_cpow_real_analytic _)))).sub
      (analyticOnNhd_const.mul
        ((positive_cpow_real_analytic (-1 : ℂ)).add (positive_cpow_real_analytic (1 - 2 * s))))
  have hD : AnalyticOnNhd ℝ (fun x => mayerPeriodCore s x - B x) (Ioi 0) :=
    (mayerPeriodCore_real_analytic hs hs1 him).sub hB
  have he : (fun x => mayerPeriodCore s x - B x) =ᶠ[𝓝 (1 : ℝ)] 0 := by
    filter_upwards [isOpen_Ioo.mem_nhds
      (show (1 : ℝ) ∈ Ioo (3 / 4 : ℝ) (5 / 4) by norm_num)] with x hx
    have hxS : x ∈ MayerScatteringPeriod.periodSegment := by
      constructor <;> linarith only [hx.1, hx.2]
    have hxE : x ∈ Ioo (1 / 2 : ℝ) (7 / 2) := by
      constructor <;> linarith only [hx.1, hx.2]
    have hE : eisensteinLewisPeriod s x = MayerScatteringPeriod.periodValue (2 * s) x :=
      (eisensteinLewisPeriod_eq s x).trans (eisensteinPeriod_eq_periodValue hr hxE)
    change mayerPeriodCore s x - B x = 0
    apply sub_eq_zero.mpr
    dsimp only [B]
    rw [hE]
    exact cauchyKernel_core_period hw hwi hxS
  exact sub_eq_zero.mp (hD.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    isPreconnected_Ioi (by norm_num : (1 : ℝ) ∈ Ioi 0) he ha)

#print axioms mayerPeriodCore_real_analytic
#print axioms mayerPeriodCore_eq_eisenstein_sub_boundary

end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering
