import GaloisForLFunctions.RHTower.MobiusLaplaceCriterionFrontier
import GaloisForLFunctions.RHTower.ThueMorseMellinFlatness
import GaloisForLFunctions.RHTower.LandauIntegralTransfer
import GaloisForLFunctions.RHTower.XiZerosInfinite
import GaloisForLFunctions.RHTower.XiEndpointStrongHeightGap
import GaloisForLFunctions.HTGeometry.GammaAnalyticOffPoles

/-!
# Subcritical Landau carriers for the Möbius--Laplace source

For a real exponent `a < 1`, adjoin the comparison kernel `K x⁻ᵃ 1_(0,1](x)` to the
Möbius--Laplace transform.  Its classical Mellin transform is

`Gamma(s) / zeta(s) + K / (s - a)`.

Cutting this carrier at any positive scale `d` leaves a tail which vanishes near zero, has the
same exponential decay as the original source at infinity, and consequently has an entire
Mellin transform.  This isolates the compact analytic correction needed by Landau's oscillation
argument without any asymptotic or numerical input.
-/

open Complex MeasureTheory Filter Set Asymptotics ProbabilityTheory
open scoped Topology Interval

noncomputable section

namespace RHTower

/-- The complex-valued power comparison `x⁻ᵃ` restricted to `(0,1]`. -/
def mobiusLaplacePowerKernel (a : ℝ) : ℝ → ℂ :=
  (Ioc 0 1).indicator fun x => (x : ℂ) ^ (-(a : ℂ))

/-- Möbius--Laplace source with a subcritical power comparison added. -/
def mobiusLaplaceComparisonCarrier (a K : ℝ) (x : ℝ) : ℂ :=
  mobiusDiscreteLaplaceTransform x + (K : ℂ) * mobiusLaplacePowerKernel a x

/-- Carrier tail above scale `d`.  On the positive axis it complements the cutoff `(0,d]`. -/
def mobiusLaplaceComparisonTail (a K d : ℝ) : ℝ → ℂ :=
  (Ioi d).indicator (mobiusLaplaceComparisonCarrier a K)

/-- Near-zero carrier obtained by removing the tail above `d`. -/
def mobiusLaplaceComparisonCutoff (a K d : ℝ) : ℝ → ℂ :=
  mobiusLaplaceComparisonCarrier a K - mobiusLaplaceComparisonTail a K d

/-- Pole-regularized analytic expression for `Gamma(s) / zeta(s)`. -/
def mobiusLaplaceRegularizedMellin (s : ℂ) : ℂ :=
  Complex.Gamma s * (s - 1) / zetaResidueUnit s

/-- Candidate continuation of the cutoff Mellin transform. -/
def mobiusLaplaceComparisonCutoffContinuation (a K d : ℝ) (s : ℂ) : ℂ :=
  mobiusLaplaceRegularizedMellin s + K / (s - a) -
    mellin (mobiusLaplaceComparisonTail a K d) s

/-- Fixed classical Mellin node used to center Landau's Taylor argument. -/
def mobiusLaplaceLandauCenter : ℝ := 5 / 2

/-- Absolute Mellin density of the cutoff at the classical node `5/2`. -/
def mobiusLaplaceLandauDensity (a K d : ℝ) (x : ℝ) : ℝ :=
  ‖(x : ℂ) ^ ((mobiusLaplaceLandauCenter : ℂ) - 1) *
    mobiusLaplaceComparisonCutoff a K d x‖

/-- Positive measure carrying the near-zero cutoff. -/
def mobiusLaplaceLandauMeasure (a K d : ℝ) : Measure ℝ :=
  (volume.restrict (Ioi 0)).withDensity fun x =>
    ENNReal.ofReal (mobiusLaplaceLandauDensity a K d x)

/-- Logarithmic random variable whose complex MGF is a translated Mellin transform. -/
def mobiusLaplaceLandauLog (x : ℝ) : ℝ := -Real.log x

/-- Cutoff continuation translated so the classical node `5/2` becomes the MGF origin. -/
def mobiusLaplaceLandauContinuation (a K d : ℝ) (z : ℂ) : ℂ :=
  mobiusLaplaceComparisonCutoffContinuation a K d
    ((mobiusLaplaceLandauCenter : ℂ) - z)

/-- Mellin transform reconstructed from the positive MGF, entire tail, and comparison pole. -/
def mobiusLaplaceReconstructedMellin (a K d : ℝ) (s : ℂ) : ℂ :=
  complexMGF mobiusLaplaceLandauLog (mobiusLaplaceLandauMeasure a K d)
      ((mobiusLaplaceLandauCenter : ℂ) - s) +
    mellin (mobiusLaplaceComparisonTail a K d) s - K / (s - a)

/-- Positivity condition on the near-zero carrier used in Landau's theorem. -/
def MobiusLaplaceComparisonCutoffNonnegative (a K d : ℝ) : Prop :=
  ∀ x : ℝ, 0 < x → 0 ≤ (mobiusLaplaceComparisonCutoff a K d x).re

/-- The power kernel has its expected real value on `(0,1]`. -/
theorem mobiusLaplacePowerKernel_eq_of_pos_le_one {a x : ℝ}
    (hx0 : 0 < x) (hx1 : x ≤ 1) :
    mobiusLaplacePowerKernel a x = (x ^ (-a : ℝ) : ℝ) := by
  rw [mobiusLaplacePowerKernel,
    Set.indicator_of_mem (show x ∈ Ioc (0 : ℝ) 1 from ⟨hx0, hx1⟩)]
  rw [show -(a : ℂ) = ((-a : ℝ) : ℂ) by simp]
  exact (Complex.ofReal_cpow hx0.le (-a)).symm

/-- The comparison carrier is real-valued on the positive axis. -/
theorem mobiusLaplaceComparisonCarrier_im_eq_zero {a K x : ℝ} (hx : 0 < x) :
    (mobiusLaplaceComparisonCarrier a K x).im = 0 := by
  rw [mobiusLaplaceComparisonCarrier, add_im, mul_im,
    mobiusDiscreteLaplaceTransform_im_eq_zero hx]
  by_cases hx1 : x ≤ 1
  · rw [mobiusLaplacePowerKernel_eq_of_pos_le_one hx hx1]
    simp
  · rw [mobiusLaplacePowerKernel, Set.indicator_of_notMem]
    · simp
    · exact fun h => hx1 h.2

/-- On `(0,d]`, the cutoff is exactly the comparison carrier. -/
theorem mobiusLaplaceComparisonCutoff_eq_carrier {a K d x : ℝ}
    (hxd : x ≤ d) :
    mobiusLaplaceComparisonCutoff a K d x = mobiusLaplaceComparisonCarrier a K x := by
  simp [mobiusLaplaceComparisonCutoff, mobiusLaplaceComparisonTail,
    not_lt_of_ge hxd]

/-- Above `d`, the cutoff vanishes. -/
theorem mobiusLaplaceComparisonCutoff_eq_zero {a K d x : ℝ}
    (hxd : d < x) : mobiusLaplaceComparisonCutoff a K d x = 0 := by
  simp [mobiusLaplaceComparisonCutoff, mobiusLaplaceComparisonTail, hxd]

/-- The cutoff remains real-valued on the positive axis. -/
theorem mobiusLaplaceComparisonCutoff_im_eq_zero {a K d x : ℝ} (hx : 0 < x) :
    (mobiusLaplaceComparisonCutoff a K d x).im = 0 := by
  by_cases hxd : x ≤ d
  · rw [mobiusLaplaceComparisonCutoff_eq_carrier hxd,
      mobiusLaplaceComparisonCarrier_im_eq_zero hx]
  · rw [mobiusLaplaceComparisonCutoff_eq_zero (lt_of_not_ge hxd)]
    simp

/-- Mellin convergence of the power comparison in its natural half-plane. -/
theorem mellinConvergent_mobiusLaplacePowerKernel {a : ℝ} {s : ℂ}
    (hs : a < s.re) : MellinConvergent (mobiusLaplacePowerKernel a) s := by
  simpa [mobiusLaplacePowerKernel] using
    (hasMellin_cpow_Ioc (-(a : ℂ)) (s := s) (by simp; linarith)).1

/-- Exact Mellin transform of the power comparison. -/
theorem mellin_mobiusLaplacePowerKernel {a : ℝ} {s : ℂ} (hs : a < s.re) :
    mellin (mobiusLaplacePowerKernel a) s = 1 / (s - a) := by
  have h := (hasMellin_cpow_Ioc (-(a : ℂ)) (s := s) (by simp; linarith)).2
  simpa [mobiusLaplacePowerKernel, sub_eq_add_neg] using h

/-- Classical Mellin identity for the comparison carrier. -/
theorem mellin_mobiusLaplaceComparisonCarrier {a K : ℝ} {s : ℂ}
    (ha : a < 1) (hs : 1 < s.re) :
    HasMellin (mobiusLaplaceComparisonCarrier a K) s
      (Complex.Gamma s * (riemannZeta s)⁻¹ + K / (s - a)) := by
  have hsource := mellinConvergent_mobiusDiscreteLaplaceTransform hs
  have hpower := mellinConvergent_mobiusLaplacePowerKernel (lt_trans ha hs)
  have hadd := hasMellin_add hsource (hpower.const_smul (K : ℂ))
  refine ⟨?_, ?_⟩
  · simpa [mobiusLaplaceComparisonCarrier, Pi.add_apply, smul_eq_mul] using hadd.1
  · rw [show mellin (mobiusLaplaceComparisonCarrier a K) s =
        mellin mobiusDiscreteLaplaceTransform s +
          mellin (fun x => (K : ℂ) • mobiusLaplacePowerKernel a x) s by
      simpa [mobiusLaplaceComparisonCarrier, Pi.add_apply, smul_eq_mul] using hadd.2]
    rw [mellin_mobiusDiscreteLaplaceTransform_eq_gamma_div_zeta hs,
      mellin_const_smul, mellin_mobiusLaplacePowerKernel (lt_trans ha hs)]
    simp [smul_eq_mul, div_eq_mul_inv]

/-- The source and power comparison are locally integrable on the positive axis. -/
theorem mobiusLaplaceComparisonCarrier_locallyIntegrableOn {a K : ℝ} (ha : a < 1) :
    LocallyIntegrableOn (mobiusLaplaceComparisonCarrier a K) (Ioi 0) := by
  have hpower : IntegrableOn (mobiusLaplacePowerKernel a) (Ioi 0) := by
    have h := mellinConvergent_mobiusLaplacePowerKernel (s := (1 : ℂ)) ha
    simpa [MellinConvergent] using h
  have hscaled : LocallyIntegrableOn
      (fun x => (K : ℂ) • mobiusLaplacePowerKernel a x) (Ioi 0) := by
    intro x hx
    rcases hpower.locallyIntegrableOn x hx with ⟨u, hu, hint⟩
    exact ⟨u, hu, by simpa [smul_eq_mul] using hint.const_mul (K : ℂ)⟩
  have hadd := mobiusDiscreteLaplaceTransform_locallyIntegrableOn.add hscaled
  simpa [mobiusLaplaceComparisonCarrier, Pi.add_apply, smul_eq_mul] using hadd

/-- Above a positive cutoff, the comparison tail is a globally Mellin-flat correction. -/
theorem mobiusLaplaceComparisonTail_isMellinFlatKernel {a K d : ℝ}
    (ha : a < 1) (hd : 0 < d) :
    IsMellinFlatKernel (mobiusLaplaceComparisonTail a K d) := by
  have hcarrier := mobiusLaplaceComparisonCarrier_locallyIntegrableOn (K := K) ha
  have hloc : LocallyIntegrableOn (mobiusLaplaceComparisonTail a K d) (Ioi 0) := by
    intro x hx
    rcases hcarrier x hx with ⟨u, hu, hint⟩
    exact ⟨u, hu, hint.indicator measurableSet_Ioi⟩
  have htail_eq_source : mobiusLaplaceComparisonTail a K d =ᶠ[atTop]
      mobiusDiscreteLaplaceTransform := by
    filter_upwards [eventually_gt_atTop d, eventually_gt_atTop (1 : ℝ)] with x hxd hx1
    simp [mobiusLaplaceComparisonTail, hxd, mobiusLaplaceComparisonCarrier,
      mobiusLaplacePowerKernel, not_le_of_gt hx1]
  have htop : ∃ c : ℝ, 0 < c ∧
      mobiusLaplaceComparisonTail a K d =O[atTop]
        (fun x : ℝ => Real.exp (-c * x)) := by
    exact ⟨1, by norm_num, htail_eq_source.trans_isBigO
      mobiusDiscreteLaplaceTransform_isBigO_exp_neg⟩
  have hzero : SuperpolynomialDecayAtZero (mobiusLaplaceComparisonTail a K d) := by
    intro b
    have heq : mobiusLaplaceComparisonTail a K d =ᶠ[𝓝[>] 0] (fun _ => 0) := by
      have hlt : ∀ᶠ x : ℝ in 𝓝[>] 0, x < d :=
        (eventually_lt_nhds hd).filter_mono nhdsWithin_le_nhds
      filter_upwards [hlt] with x hxd
      simp [mobiusLaplaceComparisonTail, not_lt_of_ge hxd.le]
    exact heq.trans_isBigO (isBigO_zero (fun x : ℝ => x ^ (-b)) (𝓝[>] 0))
  exact ⟨hloc, htop, hzero⟩

/-- The cutoff tail has an entire Mellin transform. -/
theorem mobiusLaplaceComparisonTail_mellin_analyticOnNhd {a K d : ℝ}
    (ha : a < 1) (hd : 0 < d) :
    AnalyticOnNhd ℂ (mellin (mobiusLaplaceComparisonTail a K d)) univ :=
  (mobiusLaplaceComparisonTail_isMellinFlatKernel ha hd).mellin_analyticOnNhd

/-- Exact Mellin transform of the near-zero cutoff on the classical half-plane. -/
theorem mellin_mobiusLaplaceComparisonCutoff {a K d : ℝ} {s : ℂ}
    (ha : a < 1) (hd : 0 < d) (hs : 1 < s.re) :
    HasMellin (mobiusLaplaceComparisonCutoff a K d) s
      (Complex.Gamma s * (riemannZeta s)⁻¹ + K / (s - a) -
        mellin (mobiusLaplaceComparisonTail a K d) s) := by
  have hcarrier := mellin_mobiusLaplaceComparisonCarrier (K := K) ha hs
  have htail :=
    (mobiusLaplaceComparisonTail_isMellinFlatKernel (K := K) ha hd).mellinConvergent s
  have hsub := hasMellin_sub hcarrier.1 htail
  refine ⟨?_, ?_⟩
  · simpa [mobiusLaplaceComparisonCutoff, Pi.sub_apply] using hsub.1
  · rw [show mellin (mobiusLaplaceComparisonCutoff a K d) s =
        mellin (mobiusLaplaceComparisonCarrier a K) s -
          mellin (mobiusLaplaceComparisonTail a K d) s by
      simpa [mobiusLaplaceComparisonCutoff, Pi.sub_apply] using hsub.2]
    rw [hcarrier.2]

/-- The unconditional low-height Xi gap makes the residue unit nonzero. -/
theorem zetaResidueUnit_ne_zero_of_re_pos_abs_im_le_four {s : ℂ}
    (hre : 0 < s.re) (him : |s.im| ≤ 4) : zetaResidueUnit s ≠ 0 := by
  by_cases hs1 : s = 1
  · subst s
    simp [zetaResidueUnit]
  · intro hunit
    have hzeta : riemannZeta s = 0 := by
      simpa [zetaResidueUnit, hs1, sub_ne_zero.mpr hs1] using hunit
    have hxi : xi s = 0 := (xi_eq_zero_iff hre hs1).2 hzeta
    exact xi_ne_zero_of_abs_im_le_four him hxi

/-- The regularized quotient agrees with `Gamma / zeta` in the classical half-plane. -/
theorem mobiusLaplaceRegularizedMellin_eq {s : ℂ} (hs : 1 < s.re) :
    mobiusLaplaceRegularizedMellin s = Complex.Gamma s * (riemannZeta s)⁻¹ := by
  have hs1 : s ≠ 1 := by
    intro h
    subst s
    norm_num at hs
  have hzeta : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs
  rw [mobiusLaplaceRegularizedMellin]
  simp only [zetaResidueUnit, Function.update_of_ne hs1]
  field_simp [sub_ne_zero.mpr hs1]

/-- On `Re s > 1`, the candidate continuation is the actual cutoff Mellin transform. -/
theorem mobiusLaplaceComparisonCutoffContinuation_eq_mellin
    {a K d : ℝ} (ha : a < 1) (hd : 0 < d) {s : ℂ} (hs : 1 < s.re) :
    mobiusLaplaceComparisonCutoffContinuation a K d s =
      mellin (mobiusLaplaceComparisonCutoff a K d) s := by
  rw [mobiusLaplaceComparisonCutoffContinuation,
    mobiusLaplaceRegularizedMellin_eq hs]
  exact (mellin_mobiusLaplaceComparisonCutoff ha hd hs).2.symm

/-- The cutoff continuation is analytic wherever the residue unit and comparison denominator
stay nonzero.  Low-height nonvanishing supplies the former unconditionally. -/
theorem analyticAt_mobiusLaplaceComparisonCutoffContinuation
    {a K d : ℝ} (ha : a < 1) (hd : 0 < d) {s : ℂ}
    (hapos : a < s.re) (hre : 0 < s.re) (him : |s.im| ≤ 4) :
    AnalyticAt ℂ (mobiusLaplaceComparisonCutoffContinuation a K d) s := by
  have hunit := zetaResidueUnit_ne_zero_of_re_pos_abs_im_le_four hre him
  have hreg : AnalyticAt ℂ mobiusLaplaceRegularizedMellin s := by
    exact ((HTGeometry.analyticAt_Gamma_of_re_pos hre).mul
      (analyticAt_id.sub analyticAt_const)).div
        (RHTower.analyticAt_zetaResidueUnit s) hunit
  have hsa : s - (a : ℂ) ≠ 0 := by
    intro h
    have heq : s = (a : ℂ) := sub_eq_zero.mp h
    have := congrArg Complex.re heq
    simp at this
    linarith
  have hpower : AnalyticAt ℂ (fun z : ℂ => (K : ℂ) / (z - a)) s :=
    analyticAt_const.div (analyticAt_id.sub analyticAt_const) hsa
  have htail : AnalyticAt ℂ (mellin (mobiusLaplaceComparisonTail a K d)) s :=
    mobiusLaplaceComparisonTail_mellin_analyticOnNhd ha hd s (mem_univ s)
  exact hreg.add hpower |>.sub htail

/-- The absolute cutoff density is integrable at the classical center. -/
theorem integrable_mobiusLaplaceLandauDensity {a K d : ℝ}
    (ha : a < 1) (hd : 0 < d) :
    Integrable (mobiusLaplaceLandauDensity a K d) (volume.restrict (Ioi 0)) := by
  have hconv :=
    (mellin_mobiusLaplaceComparisonCutoff (K := K) ha hd
      (s := (mobiusLaplaceLandauCenter : ℂ)) (by
        rw [mobiusLaplaceLandauCenter]
        norm_num)).1
  rw [MellinConvergent] at hconv
  change Integrable (fun x : ℝ =>
    ‖(x : ℂ) ^ ((mobiusLaplaceLandauCenter : ℂ) - 1) *
      mobiusLaplaceComparisonCutoff a K d x‖) (volume.restrict (Ioi 0))
  simpa only [IntegrableOn, smul_eq_mul] using hconv.norm

/-- The Landau carrier measure is finite. -/
theorem mobiusLaplaceLandauMeasure_finite {a K d : ℝ}
    (ha : a < 1) (hd : 0 < d) :
    IsFiniteMeasure (mobiusLaplaceLandauMeasure a K d) := by
  rw [mobiusLaplaceLandauMeasure]
  exact isFiniteMeasure_withDensity_ofReal
    (integrable_mobiusLaplaceLandauDensity ha hd).hasFiniteIntegral

/-- If the cutoff lies in `(0,1]`, its logarithmic variable is nonnegative almost everywhere. -/
theorem mobiusLaplaceLandauLog_nonneg_ae {a K d : ℝ}
    (ha : a < 1) (hd : 0 < d) (hd1 : d ≤ 1) :
    ∀ᵐ x ∂mobiusLaplaceLandauMeasure a K d, 0 ≤ mobiusLaplaceLandauLog x := by
  have hdens := integrable_mobiusLaplaceLandauDensity (K := K) ha hd
  have hmeas : AEMeasurable
      (fun x => ENNReal.ofReal (mobiusLaplaceLandauDensity a K d x))
      (volume.restrict (Ioi 0)) :=
    hdens.aestronglyMeasurable.aemeasurable.ennreal_ofReal
  rw [mobiusLaplaceLandauMeasure, ae_withDensity_iff' hmeas]
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx hden
  have hxd : x ≤ d := by
    by_contra h
    have hzero := mobiusLaplaceComparisonCutoff_eq_zero
      (a := a) (K := K) (lt_of_not_ge h)
    simp [mobiusLaplaceLandauDensity, hzero] at hden
  have hx1 : x ≤ 1 := hxd.trans hd1
  exact neg_nonneg.mpr (Real.log_nonpos hx.le hx1)

/-- Exponential tilting of the center density is exactly translation of the real Mellin
exponent. -/
theorem exp_mul_mobiusLaplaceLandauDensity_eq_norm {a K d t x : ℝ}
    (hx : 0 < x) :
    Real.exp (t * mobiusLaplaceLandauLog x) * mobiusLaplaceLandauDensity a K d x =
      ‖(x : ℂ) ^ (((mobiusLaplaceLandauCenter - t : ℝ) : ℂ) - 1) *
        mobiusLaplaceComparisonCutoff a K d x‖ := by
  simp only [mobiusLaplaceLandauLog, mobiusLaplaceLandauDensity, norm_mul,
    norm_cpow_eq_rpow_re_of_pos hx, sub_re, ofReal_re, one_re]
  rw [Real.rpow_def_of_pos hx, Real.rpow_def_of_pos hx, ← mul_assoc, ← Real.exp_add]
  congr 2
  ring

/-- Every real exponential tilt remaining in the classical Mellin half-plane is integrable
against the Landau carrier measure. -/
theorem integrable_exp_mul_mobiusLaplaceLandauLog {a K d t : ℝ}
    (ha : a < 1) (hd : 0 < d) (ht : 1 < mobiusLaplaceLandauCenter - t) :
    Integrable (fun x => Real.exp (t * mobiusLaplaceLandauLog x))
      (mobiusLaplaceLandauMeasure a K d) := by
  have hdens := integrable_mobiusLaplaceLandauDensity (K := K) ha hd
  have hmeas : AEMeasurable
      (fun x => ENNReal.ofReal (mobiusLaplaceLandauDensity a K d x))
      (volume.restrict (Ioi 0)) :=
    hdens.aestronglyMeasurable.aemeasurable.ennreal_ofReal
  rw [mobiusLaplaceLandauMeasure,
    integrable_withDensity_iff_integrable_smul₀' hmeas
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  have hdensity0 (x : ℝ) : 0 ≤ mobiusLaplaceLandauDensity a K d x := norm_nonneg _
  simp_rw [ENNReal.toReal_ofReal (hdensity0 _), smul_eq_mul]
  have hconv :=
    (mellin_mobiusLaplaceComparisonCutoff (K := K) ha hd
      (s := ((mobiusLaplaceLandauCenter - t : ℝ) : ℂ)) (by simpa using ht)).1
  rw [MellinConvergent] at hconv
  have hnorm := hconv.norm
  refine hnorm.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact (exp_mul_mobiusLaplaceLandauDensity_eq_norm
    (a := a) (K := K) (d := d) (t := t) hx).symm.trans (mul_comm _ _)

/-- Zero lies in the interior of the exponential-integrability interval of the logarithmic
carrier. -/
theorem zero_mem_interior_integrableExpSet_mobiusLaplaceLandauLog {a K d : ℝ}
    (ha : a < 1) (hd : 0 < d) :
    0 ∈ interior (integrableExpSet mobiusLaplaceLandauLog
      (mobiusLaplaceLandauMeasure a K d)) := by
  rw [mem_interior_iff_mem_nhds]
  refine mem_of_superset (Ioo_mem_nhds (a := -(1 / 2 : ℝ)) (b := 1 / 2) (by norm_num)
    (by norm_num)) ?_
  intro t ht
  exact integrable_exp_mul_mobiusLaplaceLandauLog ha hd (by
    rw [mobiusLaplaceLandauCenter]
    linarith [ht.2])

/-- Positive real logarithms convert the exponential MGF phase to a complex power. -/
theorem complex_exp_mul_mobiusLaplaceLandauLog_eq_cpow {z : ℂ} {x : ℝ}
    (hx : 0 < x) :
    Complex.exp (z * (mobiusLaplaceLandauLog x : ℂ)) = (x : ℂ) ^ (-z) := by
  have hxne : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  have hlog : Complex.log (x : ℂ) = (Real.log x : ℂ) := by
    apply Complex.ext
    · simp [Complex.log_re, Real.norm_of_nonneg hx.le]
    · simp [Complex.log_im, Complex.arg_ofReal_of_nonneg hx.le]
  rw [Complex.cpow_def_of_ne_zero hxne, hlog]
  congr 1
  simp [mobiusLaplaceLandauLog]
  ring

/-- Under cutoff positivity, the absolute center density is the center Mellin integrand itself. -/
theorem ofReal_mobiusLaplaceLandauDensity_eq {a K d x : ℝ}
    (hnonneg : MobiusLaplaceComparisonCutoffNonnegative a K d) (hx : 0 < x) :
    (mobiusLaplaceLandauDensity a K d x : ℂ) =
      (x : ℂ) ^ ((mobiusLaplaceLandauCenter : ℂ) - 1) *
        mobiusLaplaceComparisonCutoff a K d x := by
  let q : ℝ := x ^ (mobiusLaplaceLandauCenter - 1)
  have hq0 : 0 ≤ q := (Real.rpow_pos_of_pos hx _).le
  have hpow : (x : ℂ) ^ ((mobiusLaplaceLandauCenter : ℂ) - 1) = (q : ℂ) := by
    rw [show (mobiusLaplaceLandauCenter : ℂ) - 1 =
      ((mobiusLaplaceLandauCenter - 1 : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cpow hx.le]
  let w : ℂ := (x : ℂ) ^ ((mobiusLaplaceLandauCenter : ℂ) - 1) *
    mobiusLaplaceComparisonCutoff a K d x
  have hwim : w.im = 0 := by
    dsimp [w]
    rw [hpow, mul_im, mobiusLaplaceComparisonCutoff_im_eq_zero hx]
    simp
  have hwre : 0 ≤ w.re := by
    dsimp [w]
    rw [hpow, mul_re]
    simp only [ofReal_re, ofReal_im, zero_mul, sub_zero]
    exact mul_nonneg hq0 (hnonneg x hx)
  have hwcast : w = (w.re : ℂ) := by
    apply Complex.ext
    · simp
    · rw [ofReal_im]
      exact hwim
  change ((‖w‖ : ℝ) : ℂ) = w
  rw [hwcast, Complex.norm_real, Real.norm_of_nonneg hwre]

/-- The complex MGF of the positive cutoff measure is the translated cutoff Mellin transform. -/
theorem complexMGF_mobiusLaplaceLandauLog_eq_mellin {a K d : ℝ}
    (ha : a < 1) (hd : 0 < d)
    (hnonneg : MobiusLaplaceComparisonCutoffNonnegative a K d) (z : ℂ) :
    complexMGF mobiusLaplaceLandauLog (mobiusLaplaceLandauMeasure a K d) z =
      mellin (mobiusLaplaceComparisonCutoff a K d)
        ((mobiusLaplaceLandauCenter : ℂ) - z) := by
  have hdens := integrable_mobiusLaplaceLandauDensity (K := K) ha hd
  have hmeas : AEMeasurable
      (fun x => ENNReal.ofReal (mobiusLaplaceLandauDensity a K d x))
      (volume.restrict (Ioi 0)) :=
    hdens.aestronglyMeasurable.aemeasurable.ennreal_ofReal
  rw [complexMGF, mobiusLaplaceLandauMeasure,
    integral_withDensity_eq_integral_toReal_smul₀ hmeas
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  rw [mellin]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hdensity0 : 0 ≤ mobiusLaplaceLandauDensity a K d x := norm_nonneg _
  rw [ENNReal.toReal_ofReal hdensity0, Complex.real_smul, smul_eq_mul,
    ofReal_mobiusLaplaceLandauDensity_eq hnonneg hx,
    complex_exp_mul_mobiusLaplaceLandauLog_eq_cpow hx]
  rw [mul_assoc, mul_comm (mobiusLaplaceComparisonCutoff a K d x), ← mul_assoc,
    ← Complex.cpow_add _ _ (ofReal_ne_zero.mpr hx.ne')]
  congr 2
  ring

/-- The translated continuation is holomorphic on every low-height closed ball whose left edge
stays to the right of the comparison pole. -/
theorem differentiableOn_mobiusLaplaceLandauContinuation_closedBall
    {a K d : ℝ} (ha : a < 1) (ha0 : 0 < a) (hd : 0 < d) {R : NNReal}
    (hleft : a < mobiusLaplaceLandauCenter - (R : ℝ))
    (hR4 : (R : ℝ) ≤ 4) :
    DifferentiableOn ℂ (mobiusLaplaceLandauContinuation a K d)
      (Metric.closedBall 0 (R : ℝ)) := by
  intro z hz
  have hnorm : ‖z‖ ≤ (R : ℝ) := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hz
  have hapos : a < ((mobiusLaplaceLandauCenter : ℂ) - z).re := by
    simp only [sub_re, ofReal_re]
    linarith [Complex.re_le_norm z]
  have hre : 0 < ((mobiusLaplaceLandauCenter : ℂ) - z).re :=
    ha0.trans hapos
  have him : |((mobiusLaplaceLandauCenter : ℂ) - z).im| ≤ 4 := by
    simp only [sub_im, ofReal_im, zero_sub, abs_neg]
    exact (Complex.abs_im_le_norm z).trans (hnorm.trans hR4)
  have houter := analyticAt_mobiusLaplaceComparisonCutoffContinuation
    (K := K) ha hd hapos hre him
  have haffine : AnalyticAt ℂ (fun w : ℂ => (mobiusLaplaceLandauCenter : ℂ) - w) z :=
    analyticAt_const.sub analyticAt_id
  have hcomp := houter.comp haffine
  exact (by
    simpa [mobiusLaplaceLandauContinuation, Function.comp_def] using
      hcomp.differentiableAt.differentiableWithinAt)

/-- At the MGF origin, the translated continuation and positive-measure MGF have the same germ. -/
theorem mobiusLaplaceLandauContinuation_eventuallyEq_complexMGF
    {a K d : ℝ} (ha : a < 1) (hd : 0 < d)
    (hnonneg : MobiusLaplaceComparisonCutoffNonnegative a K d) :
    mobiusLaplaceLandauContinuation a K d =ᶠ[𝓝 0]
      complexMGF mobiusLaplaceLandauLog (mobiusLaplaceLandauMeasure a K d) := by
  have hmap : Tendsto
      (fun z : ℂ => (mobiusLaplaceLandauCenter : ℂ) - z)
      (𝓝 0) (𝓝 (mobiusLaplaceLandauCenter : ℂ)) := by
    simpa using
      ((continuousAt_const.sub continuousAt_id : ContinuousAt
        (fun z : ℂ => (mobiusLaplaceLandauCenter : ℂ) - z) 0).tendsto)
  have hopen : {s : ℂ | 1 < s.re} ∈ 𝓝 (mobiusLaplaceLandauCenter : ℂ) :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by
      rw [mobiusLaplaceLandauCenter]
      norm_num)
  filter_upwards [hmap.eventually hopen] with z hz
  rw [mobiusLaplaceLandauContinuation,
    mobiusLaplaceComparisonCutoffContinuation_eq_mellin ha hd hz,
    complexMGF_mobiusLaplaceLandauLog_eq_mellin ha hd hnonneg]

/-- **Source-specialized continuous Landau transfer.**  A nonnegative subcritical cutoff forces
all logarithmic exponential moments strictly inside every admissible continuation ball. -/
theorem mobiusLaplaceLandau_integrable_transfer
    {a K d : ℝ} (ha : a < 1) (ha0 : 0 < a) (hd : 0 < d) (hd1 : d ≤ 1)
    (hnonneg : MobiusLaplaceComparisonCutoffNonnegative a K d)
    {R : NNReal} (hleft : a < mobiusLaplaceLandauCenter - (R : ℝ))
    (hR4 : (R : ℝ) ≤ 4) {rho : ℝ}
    (hrho0 : 0 ≤ rho) (hrhoR : rho < (R : ℝ)) :
    Integrable (fun x => Real.exp (rho * mobiusLaplaceLandauLog x))
      (mobiusLaplaceLandauMeasure a K d) := by
  exact landau_complexMGF_integrable_transfer
    (mobiusLaplaceLandauLog_nonneg_ae ha hd hd1)
    (zero_mem_interior_integrableExpSet_mobiusLaplaceLandauLog ha hd)
    (differentiableOn_mobiusLaplaceLandauContinuation_closedBall
      ha ha0 hd hleft hR4)
    (mobiusLaplaceLandauContinuation_eventuallyEq_complexMGF ha hd hnonneg)
    hrho0 hrhoR

/-- Landau transfer fills the whole real interval to the left of the continuation radius in the
interior exponential-integrability set. -/
theorem Iio_subset_interior_integrableExpSet_mobiusLaplaceLandauLog
    {a K d : ℝ} (ha : a < 1) (ha0 : 0 < a) (hd : 0 < d) (hd1 : d ≤ 1)
    (hnonneg : MobiusLaplaceComparisonCutoffNonnegative a K d)
    {R : NNReal} (hleft : a < mobiusLaplaceLandauCenter - (R : ℝ))
    (hR4 : (R : ℝ) ≤ 4) :
    Iio (R : ℝ) ⊆ interior (integrableExpSet mobiusLaplaceLandauLog
      (mobiusLaplaceLandauMeasure a K d)) := by
  have hset : Iio (R : ℝ) ⊆ integrableExpSet mobiusLaplaceLandauLog
      (mobiusLaplaceLandauMeasure a K d) := by
    intro t ht
    by_cases ht0 : 0 ≤ t
    · exact mobiusLaplaceLandau_integrable_transfer ha ha0 hd hd1 hnonneg
        hleft hR4 ht0 ht
    · exact integrable_exp_mul_mobiusLaplaceLandauLog ha hd (by
        rw [mobiusLaplaceLandauCenter]
        linarith)
  intro t ht
  rw [mem_interior_iff_mem_nhds]
  exact mem_of_superset (Iio_mem_nhds ht) hset

/-- The reconstructed Mellin transform is analytic to the right of every real edge reached by
Landau transfer. -/
theorem analyticOnNhd_mobiusLaplaceReconstructedMellin
    {a K d b R : ℝ} (ha : a < 1) (hd : 0 < d) (hba : a < b)
    (hcenter : R = mobiusLaplaceLandauCenter - b)
    (hinter : Iio R ⊆ interior (integrableExpSet mobiusLaplaceLandauLog
      (mobiusLaplaceLandauMeasure a K d))) :
    AnalyticOnNhd ℂ (mobiusLaplaceReconstructedMellin a K d) {s : ℂ | b < s.re} := by
  intro s hs
  change b < s.re at hs
  have hzmem : ((mobiusLaplaceLandauCenter : ℂ) - s).re ∈
      interior (integrableExpSet mobiusLaplaceLandauLog
        (mobiusLaplaceLandauMeasure a K d)) := by
    apply hinter
    simp only [mem_Iio, sub_re, ofReal_re]
    rw [hcenter]
    linarith
  have hmgf : AnalyticAt ℂ
      (fun w : ℂ => complexMGF mobiusLaplaceLandauLog
        (mobiusLaplaceLandauMeasure a K d)
          ((mobiusLaplaceLandauCenter : ℂ) - w)) s := by
    have houter := analyticOnNhd_complexMGF
      ((mobiusLaplaceLandauCenter : ℂ) - s) hzmem
    have haffine : AnalyticAt ℂ
        (fun w : ℂ => (mobiusLaplaceLandauCenter : ℂ) - w) s :=
      analyticAt_const.sub analyticAt_id
    simpa [Function.comp_def] using houter.comp haffine
  have htail : AnalyticAt ℂ (mellin (mobiusLaplaceComparisonTail a K d)) s :=
    mobiusLaplaceComparisonTail_mellin_analyticOnNhd ha hd s (mem_univ s)
  have hsa : s - (a : ℂ) ≠ 0 := by
    intro h
    have heq : s = (a : ℂ) := sub_eq_zero.mp h
    have hre := congrArg Complex.re heq
    simp at hre
    linarith
  have hpower : AnalyticAt ℂ (fun w : ℂ => (K : ℂ) / (w - a)) s :=
    analyticAt_const.div (analyticAt_id.sub analyticAt_const) hsa
  exact hmgf.add htail |>.sub hpower

/-- In the classical half-plane, reconstruction cancels the cutoff tail and comparison pole,
leaving `Gamma / zeta`. -/
theorem mobiusLaplaceReconstructedMellin_eq_gamma_div_zeta
    {a K d : ℝ} (ha : a < 1) (hd : 0 < d)
    (hnonneg : MobiusLaplaceComparisonCutoffNonnegative a K d)
    {s : ℂ} (hs : 1 < s.re) :
    mobiusLaplaceReconstructedMellin a K d s =
      Complex.Gamma s * (riemannZeta s)⁻¹ := by
  rw [mobiusLaplaceReconstructedMellin,
    complexMGF_mobiusLaplaceLandauLog_eq_mellin ha hd hnonneg]
  have harg : (mobiusLaplaceLandauCenter : ℂ) -
      ((mobiusLaplaceLandauCenter : ℂ) - s) = s := by ring
  rw [harg, (mellin_mobiusLaplaceComparisonCutoff ha hd hs).2]
  ring

/-- **Subcritical Landau oscillation obstruction.**  No cutoff comparison carrier with exponent
`0 < a < 1/2` can be nonnegative on the positive axis.  The proof is unconditional: Landau
transfer analytically reconstructs `Gamma/zeta` across a half-plane containing the critical
line, while unconditional Xi-zero existence supplies a pole there. -/
theorem not_mobiusLaplaceComparisonCutoffNonnegative
    {a K d : ℝ} (ha0 : 0 < a) (hahalf : a < 1 / 2)
    (hd : 0 < d) (hd1 : d ≤ 1) :
    ¬ MobiusLaplaceComparisonCutoffNonnegative a K d := by
  intro hnonneg
  have ha : a < 1 := hahalf.trans (by norm_num)
  let b : ℝ := (a + 1 / 2) / 2
  have hab : a < b := by
    dsimp [b]
    linarith
  have hbhalf : b < 1 / 2 := by
    dsimp [b]
    linarith
  have hb0 : 0 < b := ha0.trans hab
  have hR0 : 0 ≤ mobiusLaplaceLandauCenter - b := by
    rw [mobiusLaplaceLandauCenter]
    linarith
  let R : NNReal := ⟨mobiusLaplaceLandauCenter - b, hR0⟩
  have hleft : a < mobiusLaplaceLandauCenter - (R : ℝ) := by
    change a < mobiusLaplaceLandauCenter - (mobiusLaplaceLandauCenter - b)
    linarith
  have hR4 : (R : ℝ) ≤ 4 := by
    change mobiusLaplaceLandauCenter - b ≤ 4
    rw [mobiusLaplaceLandauCenter]
    linarith
  have hinter := Iio_subset_interior_integrableExpSet_mobiusLaplaceLandauLog
    ha ha0 hd hd1 hnonneg hleft hR4
  let U : Set ℂ := {s : ℂ | b < s.re}
  let H : ℂ → ℂ := mobiusLaplaceReconstructedMellin a K d
  have hH : AnalyticOnNhd ℂ H U := by
    simpa [H, U] using analyticOnNhd_mobiusLaplaceReconstructedMellin
      (a := a) (K := K) (d := d) (b := b) (R := (R : ℝ))
      ha hd hab rfl hinter
  have hleftAn : AnalyticOnNhd ℂ (fun s => H s * zetaResidueUnit s) U := by
    intro s hs
    exact (hH s hs).mul (RHTower.analyticAt_zetaResidueUnit s)
  have hrightAn : AnalyticOnNhd ℂ (fun s => Complex.Gamma s * (s - 1)) U := by
    intro s hs
    have hsre : b < s.re := hs
    exact (HTGeometry.analyticAt_Gamma_of_re_pos (hb0.trans hsre)).mul
      (analyticAt_id.sub analyticAt_const)
  have hevent : (fun s => H s * zetaResidueUnit s) =ᶠ[𝓝 (2 : ℂ)]
      (fun s => Complex.Gamma s * (s - 1)) := by
    have hgt : ∀ᶠ s : ℂ in 𝓝 (2 : ℂ), 1 < s.re :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    filter_upwards [hgt] with s hs
    have hs1 : s ≠ 1 := by
      intro h
      subst s
      norm_num at hs
    have hzeta : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs
    rw [show H s = Complex.Gamma s * (riemannZeta s)⁻¹ by
      simpa [H] using mobiusLaplaceReconstructedMellin_eq_gamma_div_zeta
        ha hd hnonneg hs]
    simp only [zetaResidueUnit, Function.update_of_ne hs1]
    field_simp [sub_ne_zero.mpr hs1]
  have h2 : (2 : ℂ) ∈ U := by
    change b < (2 : ℂ).re
    norm_num
    linarith
  have hidentity : Set.EqOn (fun s => H s * zetaResidueUnit s)
      (fun s => Complex.Gamma s * (s - 1)) U :=
    hleftAn.eqOn_of_preconnected_of_eventuallyEq hrightAn
      (convex_halfSpace_re_gt b).isPreconnected h2 hevent
  have hcontr (rho : ℂ) (hrho0 : xi rho = 0) (hrhore : 1 / 2 ≤ rho.re) : False := by
    have hrhoU : rho ∈ U := by
      change b < rho.re
      exact hbhalf.trans_le hrhore
    have hrhopos : 0 < rho.re := lt_of_lt_of_le (by norm_num) hrhore
    have hrho1 : rho ≠ 1 := by
      intro h
      subst rho
      rw [xi_one] at hrho0
      norm_num at hrho0
    have hzeta : riemannZeta rho = 0 := (xi_eq_zero_iff hrhopos hrho1).mp hrho0
    have hunit : zetaResidueUnit rho = 0 := by
      simp [zetaResidueUnit, hrho1, hzeta]
    have hid := hidentity hrhoU
    change H rho * zetaResidueUnit rho = Complex.Gamma rho * (rho - 1) at hid
    rw [hunit, mul_zero] at hid
    exact (mul_ne_zero (Complex.Gamma_ne_zero_of_re_pos hrhopos)
      (sub_ne_zero.mpr hrho1)) hid.symm
  obtain ⟨z, hz⟩ := xiDivisorSupport_infinite.nonempty
  let q : XiDivisorSupport := ⟨z, hz⟩
  have hz0 : xi z = 0 := by
    simpa [q] using xi_eq_zero_of_mem_divisor_support q
  by_cases hzright : 1 / 2 ≤ z.re
  · exact hcontr z hz0 hzright
  · apply hcontr (1 - z)
    · rw [xi_one_sub]
      exact hz0
    · simp only [sub_re, one_re]
      linarith

/-- No analytic function on a half-plane crossing the critical line can agree with
`Gamma(s)/zeta(s)` on `Re s > 1`.  This is the abstract zero-collision endpoint used by both
signs of the Landau argument. -/
theorem no_analytic_gamma_div_zeta_continuation_below_half
    {b : ℝ} (hb0 : 0 < b) (hbhalf : b < 1 / 2) {H : ℂ → ℂ}
    (hH : AnalyticOnNhd ℂ H {s : ℂ | b < s.re})
    (hclassical : ∀ s : ℂ, 1 < s.re →
      H s = Complex.Gamma s * (riemannZeta s)⁻¹) : False := by
  let U : Set ℂ := {s : ℂ | b < s.re}
  have hleftAn : AnalyticOnNhd ℂ (fun s => H s * zetaResidueUnit s) U := by
    intro s hs
    exact (hH s hs).mul (RHTower.analyticAt_zetaResidueUnit s)
  have hrightAn : AnalyticOnNhd ℂ (fun s => Complex.Gamma s * (s - 1)) U := by
    intro s hs
    have hsre : b < s.re := hs
    exact (HTGeometry.analyticAt_Gamma_of_re_pos (hb0.trans hsre)).mul
      (analyticAt_id.sub analyticAt_const)
  have hevent : (fun s => H s * zetaResidueUnit s) =ᶠ[𝓝 (2 : ℂ)]
      (fun s => Complex.Gamma s * (s - 1)) := by
    have hgt : ∀ᶠ s : ℂ in 𝓝 (2 : ℂ), 1 < s.re :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    filter_upwards [hgt] with s hs
    have hs1 : s ≠ 1 := by
      intro h
      subst s
      norm_num at hs
    have hzeta : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs
    rw [hclassical s hs]
    simp only [zetaResidueUnit, Function.update_of_ne hs1]
    field_simp [sub_ne_zero.mpr hs1]
  have h2 : (2 : ℂ) ∈ U := by
    change b < (2 : ℂ).re
    norm_num
    linarith
  have hidentity : Set.EqOn (fun s => H s * zetaResidueUnit s)
      (fun s => Complex.Gamma s * (s - 1)) U :=
    hleftAn.eqOn_of_preconnected_of_eventuallyEq hrightAn
      (convex_halfSpace_re_gt b).isPreconnected h2 hevent
  have hcontr (rho : ℂ) (hrho0 : xi rho = 0) (hrhore : 1 / 2 ≤ rho.re) : False := by
    have hrhoU : rho ∈ U := by
      change b < rho.re
      exact hbhalf.trans_le hrhore
    have hrhopos : 0 < rho.re := lt_of_lt_of_le (by norm_num) hrhore
    have hrho1 : rho ≠ 1 := by
      intro h
      subst rho
      rw [xi_one] at hrho0
      norm_num at hrho0
    have hzeta : riemannZeta rho = 0 := (xi_eq_zero_iff hrhopos hrho1).mp hrho0
    have hunit : zetaResidueUnit rho = 0 := by
      simp [zetaResidueUnit, hrho1, hzeta]
    have hid := hidentity hrhoU
    change H rho * zetaResidueUnit rho = Complex.Gamma rho * (rho - 1) at hid
    rw [hunit, mul_zero] at hid
    exact (mul_ne_zero (Complex.Gamma_ne_zero_of_re_pos hrhopos)
      (sub_ne_zero.mpr hrho1)) hid.symm
  obtain ⟨z, hz⟩ := xiDivisorSupport_infinite.nonempty
  let q : XiDivisorSupport := ⟨z, hz⟩
  have hz0 : xi z = 0 := by
    simpa [q] using xi_eq_zero_of_mem_divisor_support q
  by_cases hzright : 1 / 2 ≤ z.re
  · exact hcontr z hz0 hzright
  · apply hcontr (1 - z)
    · rw [xi_one_sub]
      exact hz0
    · simp only [sub_re, one_re]
      linarith

/-! ## Opposite sign -/

/-- Nonpositivity condition on the cutoff carrier. -/
def MobiusLaplaceComparisonCutoffNonpositive (a K d : ℝ) : Prop :=
  ∀ x : ℝ, 0 < x → (mobiusLaplaceComparisonCutoff a K d x).re ≤ 0

/-- Negated translated continuation for a nonpositive cutoff. -/
def mobiusLaplaceNegativeLandauContinuation (a K d : ℝ) (z : ℂ) : ℂ :=
  -mobiusLaplaceLandauContinuation a K d z

/-- Mellin reconstruction when the cutoff has the opposite sign. -/
def mobiusLaplaceNegativeReconstructedMellin (a K d : ℝ) (s : ℂ) : ℂ :=
  -complexMGF mobiusLaplaceLandauLog (mobiusLaplaceLandauMeasure a K d)
      ((mobiusLaplaceLandauCenter : ℂ) - s) +
    mellin (mobiusLaplaceComparisonTail a K d) s - K / (s - a)

/-- For a nonpositive cutoff, the absolute center density is the negative Mellin integrand. -/
theorem ofReal_mobiusLaplaceLandauDensity_eq_neg {a K d x : ℝ}
    (hnonpos : MobiusLaplaceComparisonCutoffNonpositive a K d) (hx : 0 < x) :
    (mobiusLaplaceLandauDensity a K d x : ℂ) =
      -((x : ℂ) ^ ((mobiusLaplaceLandauCenter : ℂ) - 1) *
        mobiusLaplaceComparisonCutoff a K d x) := by
  let q : ℝ := x ^ (mobiusLaplaceLandauCenter - 1)
  have hq0 : 0 ≤ q := (Real.rpow_pos_of_pos hx _).le
  have hpow : (x : ℂ) ^ ((mobiusLaplaceLandauCenter : ℂ) - 1) = (q : ℂ) := by
    rw [show (mobiusLaplaceLandauCenter : ℂ) - 1 =
      ((mobiusLaplaceLandauCenter - 1 : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cpow hx.le]
  let w : ℂ := (x : ℂ) ^ ((mobiusLaplaceLandauCenter : ℂ) - 1) *
    mobiusLaplaceComparisonCutoff a K d x
  have hwim : w.im = 0 := by
    dsimp [w]
    rw [hpow, mul_im, mobiusLaplaceComparisonCutoff_im_eq_zero hx]
    simp
  have hwre : w.re ≤ 0 := by
    dsimp [w]
    rw [hpow, mul_re]
    simp only [ofReal_re, ofReal_im, zero_mul, sub_zero]
    exact mul_nonpos_of_nonneg_of_nonpos hq0 (hnonpos x hx)
  have hwcast : w = (w.re : ℂ) := by
    apply Complex.ext
    · simp
    · rw [ofReal_im]
      exact hwim
  change ((‖w‖ : ℝ) : ℂ) = -w
  rw [hwcast, Complex.norm_real, Real.norm_of_nonpos hwre]
  simp

/-- The positive measure MGF is the negative translated cutoff Mellin transform. -/
theorem complexMGF_mobiusLaplaceLandauLog_eq_neg_mellin {a K d : ℝ}
    (ha : a < 1) (hd : 0 < d)
    (hnonpos : MobiusLaplaceComparisonCutoffNonpositive a K d) (z : ℂ) :
    complexMGF mobiusLaplaceLandauLog (mobiusLaplaceLandauMeasure a K d) z =
      -mellin (mobiusLaplaceComparisonCutoff a K d)
        ((mobiusLaplaceLandauCenter : ℂ) - z) := by
  have hdens := integrable_mobiusLaplaceLandauDensity (K := K) ha hd
  have hmeas : AEMeasurable
      (fun x => ENNReal.ofReal (mobiusLaplaceLandauDensity a K d x))
      (volume.restrict (Ioi 0)) :=
    hdens.aestronglyMeasurable.aemeasurable.ennreal_ofReal
  rw [complexMGF, mobiusLaplaceLandauMeasure,
    integral_withDensity_eq_integral_toReal_smul₀ hmeas
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  rw [mellin, ← integral_neg]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hdensity0 : 0 ≤ mobiusLaplaceLandauDensity a K d x := norm_nonneg _
  rw [ENNReal.toReal_ofReal hdensity0, Complex.real_smul, smul_eq_mul,
    ofReal_mobiusLaplaceLandauDensity_eq_neg hnonpos hx,
    complex_exp_mul_mobiusLaplaceLandauLog_eq_cpow hx]
  rw [neg_mul]
  congr 1
  rw [mul_assoc, mul_comm (mobiusLaplaceComparisonCutoff a K d x), ← mul_assoc,
    ← Complex.cpow_add _ _ (ofReal_ne_zero.mpr hx.ne')]
  congr 2
  ring

/-- The negated translated continuation is holomorphic on the same admissible balls. -/
theorem differentiableOn_mobiusLaplaceNegativeLandauContinuation_closedBall
    {a K d : ℝ} (ha : a < 1) (ha0 : 0 < a) (hd : 0 < d) {R : NNReal}
    (hleft : a < mobiusLaplaceLandauCenter - (R : ℝ))
    (hR4 : (R : ℝ) ≤ 4) :
    DifferentiableOn ℂ (mobiusLaplaceNegativeLandauContinuation a K d)
      (Metric.closedBall 0 (R : ℝ)) := by
  intro z hz
  exact (differentiableOn_mobiusLaplaceLandauContinuation_closedBall
    ha ha0 hd hleft hR4 z hz).neg

/-- For a nonpositive cutoff, negated continuation and positive-measure MGF have the same germ. -/
theorem mobiusLaplaceNegativeLandauContinuation_eventuallyEq_complexMGF
    {a K d : ℝ} (ha : a < 1) (hd : 0 < d)
    (hnonpos : MobiusLaplaceComparisonCutoffNonpositive a K d) :
    mobiusLaplaceNegativeLandauContinuation a K d =ᶠ[𝓝 0]
      complexMGF mobiusLaplaceLandauLog (mobiusLaplaceLandauMeasure a K d) := by
  have hmap : Tendsto
      (fun z : ℂ => (mobiusLaplaceLandauCenter : ℂ) - z)
      (𝓝 0) (𝓝 (mobiusLaplaceLandauCenter : ℂ)) := by
    simpa using
      ((continuousAt_const.sub continuousAt_id : ContinuousAt
        (fun z : ℂ => (mobiusLaplaceLandauCenter : ℂ) - z) 0).tendsto)
  have hopen : {s : ℂ | 1 < s.re} ∈ 𝓝 (mobiusLaplaceLandauCenter : ℂ) :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by
      rw [mobiusLaplaceLandauCenter]
      norm_num)
  filter_upwards [hmap.eventually hopen] with z hz
  rw [mobiusLaplaceNegativeLandauContinuation, mobiusLaplaceLandauContinuation,
    mobiusLaplaceComparisonCutoffContinuation_eq_mellin ha hd hz,
    complexMGF_mobiusLaplaceLandauLog_eq_neg_mellin ha hd hnonpos]

/-- Landau transfer for a nonpositive cutoff, after negating its continuation. -/
theorem mobiusLaplaceNegativeLandau_integrable_transfer
    {a K d : ℝ} (ha : a < 1) (ha0 : 0 < a) (hd : 0 < d) (hd1 : d ≤ 1)
    (hnonpos : MobiusLaplaceComparisonCutoffNonpositive a K d)
    {R : NNReal} (hleft : a < mobiusLaplaceLandauCenter - (R : ℝ))
    (hR4 : (R : ℝ) ≤ 4) {rho : ℝ}
    (hrho0 : 0 ≤ rho) (hrhoR : rho < (R : ℝ)) :
    Integrable (fun x => Real.exp (rho * mobiusLaplaceLandauLog x))
      (mobiusLaplaceLandauMeasure a K d) := by
  exact landau_complexMGF_integrable_transfer
    (mobiusLaplaceLandauLog_nonneg_ae ha hd hd1)
    (zero_mem_interior_integrableExpSet_mobiusLaplaceLandauLog ha hd)
    (differentiableOn_mobiusLaplaceNegativeLandauContinuation_closedBall
      ha ha0 hd hleft hR4)
    (mobiusLaplaceNegativeLandauContinuation_eventuallyEq_complexMGF ha hd hnonpos)
    hrho0 hrhoR

/-- Opposite-sign Landau transfer fills the same real MGF interval. -/
theorem Iio_subset_interior_integrableExpSet_mobiusLaplaceNegativeLandauLog
    {a K d : ℝ} (ha : a < 1) (ha0 : 0 < a) (hd : 0 < d) (hd1 : d ≤ 1)
    (hnonpos : MobiusLaplaceComparisonCutoffNonpositive a K d)
    {R : NNReal} (hleft : a < mobiusLaplaceLandauCenter - (R : ℝ))
    (hR4 : (R : ℝ) ≤ 4) :
    Iio (R : ℝ) ⊆ interior (integrableExpSet mobiusLaplaceLandauLog
      (mobiusLaplaceLandauMeasure a K d)) := by
  have hset : Iio (R : ℝ) ⊆ integrableExpSet mobiusLaplaceLandauLog
      (mobiusLaplaceLandauMeasure a K d) := by
    intro t ht
    by_cases ht0 : 0 ≤ t
    · exact mobiusLaplaceNegativeLandau_integrable_transfer ha ha0 hd hd1 hnonpos
        hleft hR4 ht0 ht
    · exact integrable_exp_mul_mobiusLaplaceLandauLog ha hd (by
        rw [mobiusLaplaceLandauCenter]
        linarith)
  intro t ht
  rw [mem_interior_iff_mem_nhds]
  exact mem_of_superset (Iio_mem_nhds ht) hset

/-- Negative-sign Mellin reconstruction is analytic on the Landau half-plane. -/
theorem analyticOnNhd_mobiusLaplaceNegativeReconstructedMellin
    {a K d b R : ℝ} (ha : a < 1) (hd : 0 < d) (hba : a < b)
    (hcenter : R = mobiusLaplaceLandauCenter - b)
    (hinter : Iio R ⊆ interior (integrableExpSet mobiusLaplaceLandauLog
      (mobiusLaplaceLandauMeasure a K d))) :
    AnalyticOnNhd ℂ (mobiusLaplaceNegativeReconstructedMellin a K d)
      {s : ℂ | b < s.re} := by
  intro s hs
  change b < s.re at hs
  have hzmem : ((mobiusLaplaceLandauCenter : ℂ) - s).re ∈
      interior (integrableExpSet mobiusLaplaceLandauLog
        (mobiusLaplaceLandauMeasure a K d)) := by
    apply hinter
    simp only [mem_Iio, sub_re, ofReal_re]
    rw [hcenter]
    linarith
  have hmgf : AnalyticAt ℂ
      (fun w : ℂ => complexMGF mobiusLaplaceLandauLog
        (mobiusLaplaceLandauMeasure a K d)
          ((mobiusLaplaceLandauCenter : ℂ) - w)) s := by
    have houter := analyticOnNhd_complexMGF
      ((mobiusLaplaceLandauCenter : ℂ) - s) hzmem
    have haffine : AnalyticAt ℂ
        (fun w : ℂ => (mobiusLaplaceLandauCenter : ℂ) - w) s :=
      analyticAt_const.sub analyticAt_id
    simpa [Function.comp_def] using houter.comp haffine
  have htail : AnalyticAt ℂ (mellin (mobiusLaplaceComparisonTail a K d)) s :=
    mobiusLaplaceComparisonTail_mellin_analyticOnNhd ha hd s (mem_univ s)
  have hsa : s - (a : ℂ) ≠ 0 := by
    intro h
    have heq : s = (a : ℂ) := sub_eq_zero.mp h
    have hre := congrArg Complex.re heq
    simp at hre
    linarith
  have hpower : AnalyticAt ℂ (fun w : ℂ => (K : ℂ) / (w - a)) s :=
    analyticAt_const.div (analyticAt_id.sub analyticAt_const) hsa
  exact hmgf.neg.add htail |>.sub hpower

/-- Classical identity for the negative-sign reconstruction. -/
theorem mobiusLaplaceNegativeReconstructedMellin_eq_gamma_div_zeta
    {a K d : ℝ} (ha : a < 1) (hd : 0 < d)
    (hnonpos : MobiusLaplaceComparisonCutoffNonpositive a K d)
    {s : ℂ} (hs : 1 < s.re) :
    mobiusLaplaceNegativeReconstructedMellin a K d s =
      Complex.Gamma s * (riemannZeta s)⁻¹ := by
  rw [mobiusLaplaceNegativeReconstructedMellin,
    complexMGF_mobiusLaplaceLandauLog_eq_neg_mellin ha hd hnonpos]
  have harg : (mobiusLaplaceLandauCenter : ℂ) -
      ((mobiusLaplaceLandauCenter : ℂ) - s) = s := by ring
  rw [harg, (mellin_mobiusLaplaceComparisonCutoff ha hd hs).2]
  ring

/-- A subcritical comparison cutoff cannot be nonpositive either. -/
theorem not_mobiusLaplaceComparisonCutoffNonpositive
    {a K d : ℝ} (ha0 : 0 < a) (hahalf : a < 1 / 2)
    (hd : 0 < d) (hd1 : d ≤ 1) :
    ¬ MobiusLaplaceComparisonCutoffNonpositive a K d := by
  intro hnonpos
  have ha : a < 1 := hahalf.trans (by norm_num)
  let b : ℝ := (a + 1 / 2) / 2
  have hab : a < b := by
    dsimp [b]
    linarith
  have hbhalf : b < 1 / 2 := by
    dsimp [b]
    linarith
  have hb0 : 0 < b := ha0.trans hab
  have hR0 : 0 ≤ mobiusLaplaceLandauCenter - b := by
    rw [mobiusLaplaceLandauCenter]
    linarith
  let R : NNReal := ⟨mobiusLaplaceLandauCenter - b, hR0⟩
  have hleft : a < mobiusLaplaceLandauCenter - (R : ℝ) := by
    change a < mobiusLaplaceLandauCenter - (mobiusLaplaceLandauCenter - b)
    linarith
  have hR4 : (R : ℝ) ≤ 4 := by
    change mobiusLaplaceLandauCenter - b ≤ 4
    rw [mobiusLaplaceLandauCenter]
    linarith
  have hinter := Iio_subset_interior_integrableExpSet_mobiusLaplaceNegativeLandauLog
    ha ha0 hd hd1 hnonpos hleft hR4
  have hH := analyticOnNhd_mobiusLaplaceNegativeReconstructedMellin
    (a := a) (K := K) (d := d) (b := b) (R := (R : ℝ))
    ha hd hab rfl hinter
  exact no_analytic_gamma_div_zeta_continuation_below_half hb0 hbhalf hH
    (fun s hs => mobiusLaplaceNegativeReconstructedMellin_eq_gamma_div_zeta
      ha hd hnonpos hs)

/-! ## Quantified excursions -/

/-- Real part of the comparison carrier on `(0,1]`. -/
theorem mobiusLaplaceComparisonCarrier_re_eq {a K x : ℝ}
    (hx : 0 < x) (hx1 : x ≤ 1) :
    (mobiusLaplaceComparisonCarrier a K x).re =
      (mobiusDiscreteLaplaceTransform x).re + K * x ^ (-a : ℝ) := by
  rw [mobiusLaplaceComparisonCarrier, add_re, mul_re,
    mobiusLaplacePowerKernel_eq_of_pos_le_one hx hx1]
  simp

/-- Every subcritical comparison carrier has a negative value below any admissible cutoff. -/
theorem exists_mobiusLaplaceComparisonCarrier_re_neg
    {a K d : ℝ} (ha0 : 0 < a) (hahalf : a < 1 / 2)
    (hd : 0 < d) (hd1 : d ≤ 1) :
    ∃ x : ℝ, 0 < x ∧ x ≤ d ∧ (mobiusLaplaceComparisonCarrier a K x).re < 0 := by
  have hnot := not_mobiusLaplaceComparisonCutoffNonnegative
    (K := K) ha0 hahalf hd hd1
  rw [MobiusLaplaceComparisonCutoffNonnegative] at hnot
  push Not at hnot
  obtain ⟨x, hx, hneg⟩ := hnot
  have hxd : x ≤ d := by
    by_contra h
    rw [mobiusLaplaceComparisonCutoff_eq_zero (lt_of_not_ge h)] at hneg
    simp at hneg
  rw [mobiusLaplaceComparisonCutoff_eq_carrier hxd] at hneg
  exact ⟨x, hx, hxd, hneg⟩

/-- Every subcritical comparison carrier also has a positive value below the cutoff. -/
theorem exists_mobiusLaplaceComparisonCarrier_re_pos
    {a K d : ℝ} (ha0 : 0 < a) (hahalf : a < 1 / 2)
    (hd : 0 < d) (hd1 : d ≤ 1) :
    ∃ x : ℝ, 0 < x ∧ x ≤ d ∧ 0 < (mobiusLaplaceComparisonCarrier a K x).re := by
  have hnot := not_mobiusLaplaceComparisonCutoffNonpositive
    (K := K) ha0 hahalf hd hd1
  rw [MobiusLaplaceComparisonCutoffNonpositive] at hnot
  push Not at hnot
  obtain ⟨x, hx, hpos⟩ := hnot
  have hxd : x ≤ d := by
    by_contra h
    rw [mobiusLaplaceComparisonCutoff_eq_zero (lt_of_not_ge h)] at hpos
    simp at hpos
  rw [mobiusLaplaceComparisonCutoff_eq_carrier hxd] at hpos
  exact ⟨x, hx, hxd, hpos⟩

/-- Arbitrarily near zero, the Möbius--Laplace transform exceeds every real multiple of a
subcritical power barrier. -/
theorem exists_mobiusDiscreteLaplaceTransform_re_gt_subcritical
    {epsilon A delta : ℝ} (hepsilon0 : 0 < epsilon) (hepsilonHalf : epsilon < 1 / 2)
    (hdelta : 0 < delta) :
    ∃ x : ℝ, 0 < x ∧ x < delta ∧
      A * x ^ (-(1 / 2 - epsilon) : ℝ) <
        (mobiusDiscreteLaplaceTransform x).re := by
  let a : ℝ := 1 / 2 - epsilon
  let d : ℝ := min (delta / 2) 1
  have ha0 : 0 < a := by dsimp [a]; linarith
  have hahalf : a < 1 / 2 := by dsimp [a]; linarith
  have hd : 0 < d := lt_min (half_pos hdelta) zero_lt_one
  have hd1 : d ≤ 1 := min_le_right _ _
  obtain ⟨x, hx, hxd, hpos⟩ :=
    exists_mobiusLaplaceComparisonCarrier_re_pos
      (a := a) (K := -A) ha0 hahalf hd hd1
  have hx1 : x ≤ 1 := hxd.trans hd1
  have hxdlt : x < delta := by
    have := hxd.trans (min_le_left (delta / 2) 1)
    linarith
  rw [mobiusLaplaceComparisonCarrier_re_eq hx hx1] at hpos
  dsimp [a] at hpos ⊢
  exact ⟨x, hx, hxdlt, by linarith⟩

/-- Arbitrarily near zero, the Möbius--Laplace transform falls below the negative of every real
multiple of a subcritical power barrier. -/
theorem exists_mobiusDiscreteLaplaceTransform_re_lt_neg_subcritical
    {epsilon A delta : ℝ} (hepsilon0 : 0 < epsilon) (hepsilonHalf : epsilon < 1 / 2)
    (hdelta : 0 < delta) :
    ∃ x : ℝ, 0 < x ∧ x < delta ∧
      (mobiusDiscreteLaplaceTransform x).re <
        -A * x ^ (-(1 / 2 - epsilon) : ℝ) := by
  let a : ℝ := 1 / 2 - epsilon
  let d : ℝ := min (delta / 2) 1
  have ha0 : 0 < a := by dsimp [a]; linarith
  have hahalf : a < 1 / 2 := by dsimp [a]; linarith
  have hd : 0 < d := lt_min (half_pos hdelta) zero_lt_one
  have hd1 : d ≤ 1 := min_le_right _ _
  obtain ⟨x, hx, hxd, hneg⟩ :=
    exists_mobiusLaplaceComparisonCarrier_re_neg
      (a := a) (K := A) ha0 hahalf hd hd1
  have hx1 : x ≤ 1 := hxd.trans hd1
  have hxdlt : x < delta := by
    have := hxd.trans (min_le_left (delta / 2) 1)
    linarith
  rw [mobiusLaplaceComparisonCarrier_re_eq hx hx1] at hneg
  dsimp [a] at hneg ⊢
  exact ⟨x, hx, hxdlt, by linarith⟩

/-- **Two-sided subcritical oscillation law.**  Both signed excursions hold for every real
amplitude arbitrarily close to zero. -/
theorem exists_twoSided_mobiusDiscreteLaplaceTransform_subcritical_excursions
    {epsilon A delta : ℝ} (hepsilon0 : 0 < epsilon) (hepsilonHalf : epsilon < 1 / 2)
    (hdelta : 0 < delta) :
    (∃ x : ℝ, 0 < x ∧ x < delta ∧
      A * x ^ (-(1 / 2 - epsilon) : ℝ) <
        (mobiusDiscreteLaplaceTransform x).re) ∧
    (∃ x : ℝ, 0 < x ∧ x < delta ∧
      (mobiusDiscreteLaplaceTransform x).re <
        -A * x ^ (-(1 / 2 - epsilon) : ℝ)) :=
  ⟨exists_mobiusDiscreteLaplaceTransform_re_gt_subcritical
      hepsilon0 hepsilonHalf hdelta,
    exists_mobiusDiscreteLaplaceTransform_re_lt_neg_subcritical
      hepsilon0 hepsilonHalf hdelta⟩

/-- Positive zeros of the concrete Möbius--Laplace transform accumulate at the origin. -/
theorem exists_mobiusDiscreteLaplaceTransform_zero_below
    {delta : ℝ} (hdelta : 0 < delta) :
    ∃ c : ℝ, 0 < c ∧ c < delta ∧ mobiusDiscreteLaplaceTransform c = 0 := by
  obtain ⟨xp, hxp0, hxpdelta, hxppos⟩ :=
    exists_mobiusDiscreteLaplaceTransform_re_gt_subcritical
      (epsilon := 1 / 4) (A := 1) (by norm_num) (by norm_num) hdelta
  obtain ⟨xn, hxn0, hxndelta, hxnneg⟩ :=
    exists_mobiusDiscreteLaplaceTransform_re_lt_neg_subcritical
      (epsilon := 1 / 4) (A := 1) (by norm_num) (by norm_num) hdelta
  have hpos : 0 < (mobiusDiscreteLaplaceTransform xp).re := by
    have hpow : 0 < xp ^ (-(1 / 2 - (1 / 4 : ℝ)) : ℝ) :=
      Real.rpow_pos_of_pos hxp0 _
    linarith
  have hneg : (mobiusDiscreteLaplaceTransform xn).re < 0 := by
    have hpow : 0 < xn ^ (-(1 / 2 - (1 / 4 : ℝ)) : ℝ) :=
      Real.rpow_pos_of_pos hxn0 _
    linarith
  have hsub : [[xp, xn]] ⊆ Ioi (0 : ℝ) := by
    intro y hy
    rw [mem_uIcc] at hy
    rcases hy with ⟨hxy, _⟩ | ⟨hny, _⟩
    · exact hxp0.trans_le hxy
    · exact hxn0.trans_le hny
  have hcont : ContinuousOn
      (fun y : ℝ => (mobiusDiscreteLaplaceTransform y).re) [[xp, xn]] :=
    Complex.continuous_re.comp_continuousOn
      (continuousOn_mobiusDiscreteLaplaceTransform.mono hsub)
  have hzeroMem : (0 : ℝ) ∈
      [[(mobiusDiscreteLaplaceTransform xp).re,
        (mobiusDiscreteLaplaceTransform xn).re]] := by
    rw [mem_uIcc]
    exact Or.inr ⟨hneg.le, hpos.le⟩
  obtain ⟨c, hc, hczeroRe⟩ := intermediate_value_uIcc hcont hzeroMem
  have hcpos : 0 < c := by
    rw [mem_uIcc] at hc
    rcases hc with hc | hc <;> linarith
  have hcdelta : c < delta := by
    rw [mem_uIcc] at hc
    rcases hc with hc | hc <;> linarith
  have hczeroIm := mobiusDiscreteLaplaceTransform_im_eq_zero hcpos
  refine ⟨c, hcpos, hcdelta, ?_⟩
  apply Complex.ext
  · simpa using hczeroRe
  · simpa using hczeroIm

end RHTower
