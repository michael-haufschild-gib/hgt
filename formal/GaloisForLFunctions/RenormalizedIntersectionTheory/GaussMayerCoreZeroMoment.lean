import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerZeroMellinStrip
import GaloisForLFunctions.RHTower.CompletedBornReflectionNoGo
import GaloisForLFunctions.RHTower.ReflectedBiHeatExactFinitePartWeld
import GaloisForLFunctions.RHTower.ArchimedeanGammaModule

/-!
# Derivative moments of the scattering core

At a critical-strip zeta zero, both endpoint Mellin moments are ordinary
absolutely convergent integrals. Their value is the derivative of zeta.
-/

open Complex Set Filter MeasureTheory
open scoped Topology
open GaloisForLFunctions.RenormalizedIntersectionTheory
open MayerScatteringCore MayerZeroMellinStrip
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerCoreZeroMoment

private theorem ofReal_right_tendsto_punctured :
    Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝[≠] (0 : ℂ)) := by
  rw [tendsto_nhdsWithin_iff]
  constructor
  · exact Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with x hx
    simpa only [mem_compl_iff,mem_singleton_iff,Complex.ofReal_eq_zero] using hx.ne'

/-- The ordinary Mellin transform is holomorphic throughout the enlarged zero strip. -/
theorem core_zero_mellin_differentiableAt {w u : ℂ} (hw : 0 < w.re) (hw1 : w.re < 1)
    (him : 0 < w.im) (hz : riemannZeta w=0) (hu : w.re-1 < u.re) (hu1 : u.re < 1) :
    DifferentiableAt ℂ (mellin (fieldCore w)) u :=
  mellin_differentiableAt_of_isBigO_rpow (core_locallyIntegrable hw hw1 him)
    (core_zero_isBigO_top hw him hz) hu1 (core_zero_isBigO_zero hw him hz) hu

private theorem spectrum_tendsto_derivative {w : ℂ} (hw : 0 < w.re) (hw1 : w.re < 1)
    (him : 0 < w.im) (hz : riemannZeta w=0) :
    Tendsto (fun x : ℝ => mellin (fieldCore w) (x : ℂ)) (𝓝[>] (0 : ℝ))
      (𝓝 (deriv riemannZeta w)) := by
  have hwne1 : w ≠ 1 := by intro he; simp only [he,Complex.one_im,lt_self_iff_false] at him
  have hdw : HasDerivAt riemannZeta (deriv riemannZeta w) (w-0) := by
    simpa only [sub_zero] using (differentiableAt_riemannZeta hwne1).hasDerivAt
  have hd : HasDerivAt (fun z : ℂ => riemannZeta (w-z)) (-deriv riemannZeta w) 0 := by
    simpa only [mul_neg_one] using! hdw.comp 0 ((hasDerivAt_id (0 : ℂ)).const_sub w)
  have hquot : Tendsto (fun x : ℝ => riemannZeta (w-(x : ℂ))/(x : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 (-deriv riemannZeta w)) := by
    simpa only [sub_zero,hz] using _root_.RHTower.hasDerivAt_tendsto_ofReal_slope_zero_right hd
  have hres := _root_.RHTower.tendsto_mul_completedRiemannZeta_zero.comp ofReal_right_tendsto_punctured
  have hG := Complex.Gammaℝ_ne_zero_of_re_pos hw
  have hgw : ContinuousAt Gammaℝ (w-0) := by
    simpa only [sub_zero] using (GaloisForLFunctions.differentiableAt_Gammaℝ hw).continuousAt
  have hgc : ContinuousAt (fun z : ℂ => Gammaℝ (w-z)/Gammaℝ w) 0 :=
    (hgw.comp (show ContinuousAt (fun z : ℂ => w-z) 0 from by fun_prop)).div_const _
  have hgam : Tendsto (fun x : ℝ => Gammaℝ (w-(x : ℂ))/Gammaℝ w)
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    simpa only [Function.comp_def,sub_zero,div_self hG] using
      hgc.tendsto.comp (ofReal_right_tendsto_punctured.mono_right nhdsWithin_le_nhds)
  have h := (hres.mul hquot).mul hgam
  simp only [neg_mul_neg,one_mul,mul_one,Function.comp_def] at h
  apply h.congr'
  filter_upwards [eventually_mem_nhdsWithin,
    (eventually_lt_nhds hw).filter_mono nhdsWithin_le_nhds] with x hx hxw
  change 0 < x at hx
  have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hxG : Gammaℝ (x : ℂ) ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos hx
  have he : completedRiemannZeta (x : ℂ)=Gammaℝ (x : ℂ)*riemannZeta (x : ℂ) := by
    rw [riemannZeta_def_of_ne_zero hxC]
    field_simp
  have hwu0 : 0 < (w-(x : ℂ)).re := by simp only [Complex.sub_re,Complex.ofReal_re]; linarith only [hxw]
  have hwu1 : (w-(x : ℂ)).re < 1 := by simp only [Complex.sub_re,Complex.ofReal_re]; linarith only [hw1,hx]
  have hm := MayerCoreMellin.core_hasMellin_gammaR (u := (x : ℂ)) hx (hxw.trans hw1) hwu0 hwu1 him
  rw [hm.2,he]
  field_simp

/-- The convergent multiplicative moment of the actual field at a zeta zero equals `ζ′(w)`. -/
theorem core_zero_hasMellin_zero {w : ℂ} (hw : 0 < w.re) (hw1 : w.re < 1)
    (him : 0 < w.im) (hz : riemannZeta w=0) :
    HasMellin (fieldCore w) 0 (deriv riemannZeta w) := by
  have hu : w.re-1 < (0 : ℂ).re := by simp only [Complex.zero_re]; linarith only [hw1]
  have hu1 : (0 : ℂ).re < 1 := by norm_num
  refine ⟨core_zero_mellinConvergent hw hw1 him hz hu hu1,?_⟩
  have hc := (core_zero_mellin_differentiableAt hw hw1 him hz hu hu1).continuousAt
  have ht : Tendsto (fun x : ℝ => mellin (fieldCore w) (x : ℂ)) (𝓝[>] (0 : ℝ))
      (𝓝 (mellin (fieldCore w) 0)) :=
    hc.tendsto.comp (ofReal_right_tendsto_punctured.mono_right nhdsWithin_le_nhds)
  exact tendsto_nhds_unique ht (spectrum_tendsto_derivative hw hw1 him hz)

/-- Reciprocity gives the same derivative moment at the opposite spectral endpoint. -/
theorem core_zero_hasMellin_parameter {w : ℂ} (hw : 0 < w.re) (hw1 : w.re < 1)
    (him : 0 < w.im) (hz : riemannZeta w=0) :
    HasMellin (fieldCore w) w (deriv riemannZeta w) := by
  have h := core_zero_hasMellin_zero hw hw1 him hz
  constructor
  · simpa only [sub_zero] using (core_mellinConvergent_reflection hw him).mp h.1
  · rw [core_mellin_reflection hw him,sub_self]
    exact h.2

#print axioms core_zero_mellin_differentiableAt
#print axioms core_zero_hasMellin_zero
#print axioms core_zero_hasMellin_parameter

end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerCoreZeroMoment
