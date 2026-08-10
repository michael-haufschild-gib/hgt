import GaloisForLFunctions.HTGeometry.ClosedHyperplaneInverse
import GaloisForLFunctions.RHTower.HedenmalmThetaCompactDivisorEigenmode
import GaloisForLFunctions.RHTower.HedenmalmFredholmRangeDivisor
import GaloisForLFunctions.RHTower.HedenmalmWeightedAdjointCore
import Mathlib.Analysis.Normed.Lp.SmoothApprox

/-!
# Closed weighted Hedenmalm derivative

This file constructs the closure of `-i d/dx` on compactly supported smooth vectors in
`H_k = L²(ℝ,k⁻¹ dx)`.  We work in the canonically unitarily equivalent quantile space
`L²(0,1)`.  The compact source inverse, restricted to the mean-zero hyperplane, is injective and
has dense range; its graph inverse is therefore the required closed derivative.
-/

open Complex Function MeasureTheory Set Filter Topology Module
open scoped ENNReal

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

namespace HedenmalmClosedWeightedDerivative

open HedenmalmQuantile HedenmalmHilbertSchmidt HedenmalmThetaSource

private abbrev H := Lp ℂ 2 unitIntervalMeasure

local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩

/-- Mean-zero hyperplane in the quantile realization of `H_k`. -/
def thetaCentered : Submodule ℂ H := (ℂ ∙ pinnedOne)ᗮ

theorem mem_thetaCentered_iff (f : H) :
    f ∈ thetaCentered ↔ pinnedMean f = 0 := by
  rw [thetaCentered, Submodule.mem_orthogonal_singleton_iff_inner_right]
  have hinner : inner ℂ pinnedOne f = pinnedMean f := by
    rw [inner_lp_eq, pinnedMean]
    apply integral_congr_ae
    filter_upwards [pinnedOne_coeFn] with t ht
    rw [ht]
    simp
  rw [hinner]

/-- The compact source inverse restricted to the mean-zero hyperplane. -/
def thetaCenteredSourceInverse : thetaCentered →L[ℂ] H :=
  thetaCompactSourceInverse.comp thetaCentered.subtypeL

theorem pinnedVolterra_eq_zero_of_kernelOperator_eq_zero
    {f : H} (hf : thetaCompactSourceInverse f = 0) :
    pinnedVolterra f = 0 := by
  apply Lp.ext
  have hzero : ((0 : H) : ℝ → ℂ) =ᵐ[unitIntervalMeasure] fun _ => 0 :=
    Lp.coeFn_zero ℂ (2 : ENNReal) unitIntervalMeasure
  have hBzero : ((thetaCompactSourceInverse f : H) : ℝ → ℂ)
      =ᵐ[unitIntervalMeasure] fun _ => 0 := by
    rw [hf]
    exact hzero
  filter_upwards
      [pinnedKernelOperator_ae thetaSource hasFiniteKernelEnergy_thetaSource f,
        hBzero, pinnedVolterra_coeFn f,
        ae_unitIntervalMeasure_mem_Ioo, hzero]
    with t hB hBzero hC ht h0
  change ((thetaCompactSourceInverse f : H) : ℝ → ℂ) t = _ at hB
  change (pinnedVolterra f : ℝ → ℂ) t = (0 : H) t
  rw [hC, h0]
  have hq : ((quantileSpeed thetaSource t : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (quantileSpeed_pos thetaSource t).ne'
  have hI : (Complex.I : ℂ) ≠ 0 := Complex.I_ne_zero
  rw [hBzero] at hB
  rw [pinnedKernelField_apply_eq_pinnedVolterraFun] at hB
  exact (mul_eq_zero.mp hB.symm).resolve_left (mul_ne_zero hI hq)

/-- The pinned primitive has no kernel on the mean-zero hyperplane. -/
theorem eq_zero_of_pinnedMean_eq_zero_of_pinnedVolterra_eq_zero
    (f : H) (hmean : pinnedMean f = 0) (hC : pinnedVolterra f = 0) : f = 0 := by
  have hCfun : pinnedVolterraFun f =ᵐ[unitIntervalMeasure] fun _ : ℝ => (0 : ℂ) := by
    have hcoe : (fun t => (pinnedVolterra f) t) =ᵐ[unitIntervalMeasure]
        fun _ : ℝ => (0 : ℂ) := by
      rw [hC]
      simp
    exact (pinnedVolterra_coeFn f).symm.trans hcoe
  have hprefix : pinnedPrefix f =ᵐ[unitIntervalMeasure] fun _ : ℝ => (0 : ℂ) := by
    filter_upwards [hCfun] with t ht
    rw [pinnedVolterraFun, hmean, mul_zero, sub_zero] at ht
    exact ht
  let F : ℝ → ℂ := fun t => ∫ u in (0 : ℝ)..t, f u
  have hIntOn : IntegrableOn (fun t => f t) (Icc (0 : ℝ) 1) volume := by
    change Integrable (fun t => f t) (volume.restrict (Icc (0 : ℝ) 1))
    simpa only [unitIntervalMeasure] using integrable_coe f
  have hIntOnU : IntegrableOn (fun t => f t) (uIcc (0 : ℝ) 1) volume := by
    simpa only [uIcc_of_le zero_le_one] using hIntOn
  have hFcontinuous : ContinuousOn F (Icc (0 : ℝ) 1) := by
    have h := intervalIntegral.continuousOn_primitive_interval hIntOnU
    simpa only [uIcc_of_le zero_le_one, F] using h
  have hFae : F =ᵐ[volume.restrict (Icc (0 : ℝ) 1)] fun _ : ℝ => (0 : ℂ) := by
    rw [← unitIntervalMeasure]
    filter_upwards [hprefix, ae_restrict_mem measurableSet_Icc] with t htzero ht
    rw [pinnedPrefix_eq_intervalIntegral f ht] at htzero
    exact htzero
  have hclosure : Icc (0 : ℝ) 1 ⊆ closure (interior (Icc (0 : ℝ) 1)) := by
    rw [interior_Icc, closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
  have hFzero : Set.EqOn F (fun _ : ℝ => (0 : ℂ)) (Icc (0 : ℝ) 1) :=
    (volume : Measure ℝ).eqOn_of_ae_eq hFae hFcontinuous continuousOn_const hclosure
  have hldt := hIntOnU.intervalIntegrable.ae_hasDerivAt_integral
  have hldtRestrict :
      ∀ᵐ x ∂unitIntervalMeasure,
        x ∈ uIcc (0 : ℝ) 1 → ∀ c ∈ uIcc (0 : ℝ) 1,
          HasDerivAt (fun y => ∫ t in c..y, f t) (f x) x := by
    change ∀ᵐ x ∂volume.restrict (Icc (0 : ℝ) 1),
      x ∈ uIcc (0 : ℝ) 1 → ∀ c ∈ uIcc (0 : ℝ) 1,
        HasDerivAt (fun y => ∫ t in c..y, f t) (f x) x
    exact ae_restrict_of_ae hldt
  have hfzero : (fun t => f t) =ᵐ[unitIntervalMeasure] fun _ : ℝ => (0 : ℂ) := by
    filter_upwards [hldtRestrict, unitIntervalMeasure.ae_ne 0,
      unitIntervalMeasure.ae_ne 1, ae_restrict_mem measurableSet_Icc]
        with x hxderiv hx0 hx1 hx
    have hxoo : x ∈ Ioo (0 : ℝ) 1 :=
      ⟨lt_of_le_of_ne hx.1 (Ne.symm hx0), lt_of_le_of_ne hx.2 hx1⟩
    have hFderiv : HasDerivAt F (f x) x := by
      exact hxderiv (by simpa only [uIcc_of_le zero_le_one] using hx) 0 (by simp)
    have hlocal : Filter.EventuallyEq (nhds x) F (fun _ : ℝ => (0 : ℂ)) := by
      filter_upwards [Ioo_mem_nhds hxoo.1 hxoo.2] with y hy
      exact hFzero (Ioo_subset_Icc_self hy)
    have hzeroDeriv : HasDerivAt F 0 x :=
      (hasDerivAt_const x (0 : ℂ)).congr_of_eventuallyEq hlocal
    exact hFderiv.unique hzeroDeriv
  apply Lp.ext
  filter_upwards [hfzero, Lp.coeFn_zero ℂ (2 : ENNReal) unitIntervalMeasure] with t ht h0
  exact ht.trans h0.symm

theorem thetaCenteredSourceInverse_injective :
    Function.Injective thetaCenteredSourceInverse := by
  intro f g hfg
  apply sub_eq_zero.mp
  apply Subtype.ext
  apply eq_zero_of_pinnedMean_eq_zero_of_pinnedVolterra_eq_zero ((f - g : thetaCentered) : H)
  · exact (mem_thetaCentered_iff _).mp (f - g).property
  · apply pinnedVolterra_eq_zero_of_kernelOperator_eq_zero
    change thetaCenteredSourceInverse (f - g) = 0
    rw [map_sub, hfg, sub_self]

/-! ### Compactly supported smooth source core -/

theorem integral_sourceD_eq_zero {g : ℝ → ℂ}
    (hg : ContDiff ℝ ⊤ g) (hgs : HasCompactSupport g) :
    ∫ x, sourceD g x = 0 := by
  have hg1 : ContDiff ℝ 1 g := hg.of_le (by simp)
  have hderivIntegrable : Integrable (deriv g) :=
    hg1.continuous_deriv le_rfl |>.integrable_of_hasCompactSupport hgs.deriv
  have hsplit := HedenmalmFredholmRange.setIntegral_Iic_add_Ioi hderivIntegrable 0
  rw [hgs.integral_Iic_deriv_eq hg1 0, hgs.integral_Ioi_deriv_eq hg1 0] at hsplit
  have hderiv : ∫ x, deriv g x = 0 := by simpa using hsplit.symm
  change ∫ x, -Complex.I * deriv g x = 0
  rw [MeasureTheory.integral_const_mul, hderiv, mul_zero]

theorem sourceInverse_sourceD {g : ℝ → ℂ}
    (hg : ContDiff ℝ ⊤ g) (hgs : HasCompactSupport g) (x : ℝ) :
    sourceInverse thetaSource (sourceD g) x = g x := by
  have hg1 : ContDiff ℝ 1 g := hg.of_le (by simp)
  rw [sourceInverse, integral_sourceD_eq_zero hg hgs]
  simp only [zero_div, zero_mul, sub_zero]
  change Complex.I * ∫ y in Iic x, -Complex.I * deriv g y = g x
  rw [MeasureTheory.integral_const_mul,
    hgs.integral_Iic_deriv_eq hg1 x]
  ring_nf

end HedenmalmClosedWeightedDerivative

end

end RHTower
