import GaloisForLFunctions.RHTower.Suzuki.SuzukiGroundEnergyContinuity
import GaloisForLFunctions.RHTower.Suzuki.SuzukiScaledFormBridge

/-!
# Suzuki's eventual small-aperture positivity

This module proves the positivity clause of Suzuki (2026), Theorem 1.4 for the actual lowest
eigenvalue.  The missing step after fixed-interval coercivity is surjectivity of scaling: every
literal strict CCM source on `(-a,a)` is the rescaling of a unit-interval test.  We prove that
bridge at the exact source-form and physical-mass levels, transfer the uniform coefficient to the
smooth Rayleigh core, then use the exact Rayleigh-infimum theorem and aperture monotonicity.

No Riemann-hypothesis assumption, comparison-form premise, added axiom, or numerical computation
is used.
-/

open Complex MeasureTheory Set Filter Topology intervalIntegral
open scoped ENNReal InnerProduct FourierTransform
open GaloisForLFunctions.RHTower
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

/-- Pull a strict source on `(-a,a)` forward to the fixed interval `(-1,1)`. -/
def ccmComplexSmoothInteriorSourceUnitPullback
    (a : SuzukiPrimeFreeSmallAperture)
    (u : CCMComplexSmoothInteriorSource ⟨a.val, a.pos⟩) :
    SuzukiRestrictedWeilComplexTest 1 where
  toFun x := u (a.val * x)
  contDiff' := u.smooth.comp (contDiff_const.mul contDiff_id)
  hasCompactSupport' := by
    change HasCompactSupport
      (u.toFun ∘ (Homeomorph.mulLeft₀ a.val a.pos.ne'))
    exact u.hasCompactSupport.comp_homeomorph
      (Homeomorph.mulLeft₀ a.val a.pos.ne')
  tsupport_subset' := by
    have hsupport :
        tsupport (fun x : ℝ => u (a.val * x)) =
          (Homeomorph.mulLeft₀ a.val a.pos.ne') ⁻¹' tsupport u.toFun := by
      rw [show (fun x : ℝ => u (a.val * x)) =
        u.toFun ∘ (Homeomorph.mulLeft₀ a.val a.pos.ne') by rfl,
        tsupport_comp_eq_preimage]
    rw [hsupport]
    intro x hx
    have hax := u.tsupport_subset hx
    change -a.val < a.val * x ∧ a.val * x < a.val at hax
    change -1 < x ∧ x < 1
    constructor <;> nlinarith

@[simp] theorem ccmComplexSmoothInteriorSourceUnitPullback_apply
    (a : SuzukiPrimeFreeSmallAperture)
    (u : CCMComplexSmoothInteriorSource ⟨a.val, a.pos⟩) (x : ℝ) :
    ccmComplexSmoothInteriorSourceUnitPullback a u x = u (a.val * x) := rfl

theorem suzukiRescaledCore_unitPullback_real_eq
    (a : SuzukiPrimeFreeSmallAperture)
    (u : CCMComplexSmoothInteriorSource ⟨a.val, a.pos⟩) :
    (suzukiRescaledCore a
      (suzukiRestrictedWeilRealTestToCore suzukiUnitAperture
        (ccmComplexSmoothInteriorSourceUnitPullback a u).realPart) : ℝ → ℝ) =
      u.realCore := by
  funext x
  change (u (a.val * (x / a.val))).re = (u x).re
  rw [mul_div_cancel₀ x a.pos.ne']

theorem suzukiRescaledCore_unitPullback_imag_eq
    (a : SuzukiPrimeFreeSmallAperture)
    (u : CCMComplexSmoothInteriorSource ⟨a.val, a.pos⟩) :
    (suzukiRescaledCore a
      (suzukiRestrictedWeilRealTestToCore suzukiUnitAperture
        (ccmComplexSmoothInteriorSourceUnitPullback a u).imagPart) : ℝ → ℝ) =
      u.imagCore := by
  funext x
  change (u (a.val * (x / a.val))).im = (u x).im
  rw [mul_div_cancel₀ x a.pos.ne']

/-- Exact complex diagonal bridge on every strict smooth source. -/
theorem ccmRestrictedWeilSourceQuadratic_complexSmooth_eq
    (a : SuzukiPositiveAperture) (u : CCMComplexSmoothInteriorSource a) :
    ccmRestrictedWeilSourceQuadratic a u.toCCMFormVector =
      suzukiRestrictedWeilComplexQuadraticForm a
        u.toRestrictedWeilComplexTest := by
  let qr := suzukiRestrictedWeilCoreCCMFormVector a u.realCore
  let qi := suzukiRestrictedWeilCoreCCMFormVector a u.imagCore
  have hri : (ccmRestrictedWeilForm a qr qi).im = 0 :=
    ccmRestrictedWeilForm_realCore_mixed_im_eq_zero a u.realCore u.imagCore
  have hir : (ccmRestrictedWeilForm a qi qr).im = 0 :=
    ccmRestrictedWeilForm_realCore_mixed_im_eq_zero a u.imagCore u.realCore
  have hrr := ccmRestrictedWeilForm_suzukiCore_eq_restrictedWeilForm a u.realCore
  have hii := ccmRestrictedWeilForm_suzukiCore_eq_restrictedWeilForm a u.imagCore
  rw [← ccmRestrictedWeilForm_self_re_eq_source,
    u.toCCMFormVector_eq_real_add_I_imag,
    ccmRestrictedWeilForm_realImag_expansion]
  change (ccmRestrictedWeilForm a qr qr + I * ccmRestrictedWeilForm a qr qi -
      I * ccmRestrictedWeilForm a qi qr + ccmRestrictedWeilForm a qi qi).re = _
  rw [hrr, hii]
  unfold suzukiRestrictedWeilComplexQuadraticForm
  simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.I_re,
    Complex.I_im, Complex.ofReal_re, zero_mul, one_mul,
    sub_zero, hri, hir]
  simp [CCMComplexSmoothInteriorSource.realCore,
    CCMComplexSmoothInteriorSource.imagCore]

/-- Exact source form of an arbitrary strict source after inverse scaling. -/
theorem ccmRestrictedWeilSourceQuadratic_eq_rescaledComplexSourceForm
    (a : SuzukiPrimeFreeSmallAperture)
    (u : CCMComplexSmoothInteriorSource ⟨a.val, a.pos⟩) :
    ccmRestrictedWeilSourceQuadratic ⟨a.val, a.pos⟩ u.toCCMFormVector =
      suzukiRescaledComplexSourceForm a
        (ccmComplexSmoothInteriorSourceUnitPullback a u) := by
  let v := ccmComplexSmoothInteriorSourceUnitPullback a u
  let ur := suzukiRestrictedWeilRealTestToCore suzukiUnitAperture v.realPart
  let ui := suzukiRestrictedWeilRealTestToCore suzukiUnitAperture v.imagPart
  rw [ccmRestrictedWeilSourceQuadratic_complexSmooth_eq]
  unfold suzukiRestrictedWeilComplexQuadraticForm
  unfold suzukiRescaledComplexSourceForm
  change suzukiRestrictedWeilForm a.val u.realCore u.realCore +
      suzukiRestrictedWeilForm a.val u.imagCore u.imagCore =
    suzukiRestrictedWeilForm a.val (suzukiRescaledCore a ur)
        (suzukiRescaledCore a ur) +
      suzukiRestrictedWeilForm a.val (suzukiRescaledCore a ui)
        (suzukiRescaledCore a ui)
  have hr : (suzukiRescaledCore a ur : ℝ → ℝ) = u.realCore := by
    simpa only [ur, v] using suzukiRescaledCore_unitPullback_real_eq a u
  have hi : (suzukiRescaledCore a ui : ℝ → ℝ) = u.imagCore := by
    simpa only [ui, v] using suzukiRescaledCore_unitPullback_imag_eq a u
  rw [hr, hi]

/-- Physical interval energy scales exactly under the unit pullback. -/
theorem suzukiRestrictedWeilComplexIntervalEnergy_unitPullback
    (a : SuzukiPrimeFreeSmallAperture)
    (u : CCMComplexSmoothInteriorSource ⟨a.val, a.pos⟩) :
    suzukiRestrictedWeilComplexIntervalEnergy ⟨a.val, a.pos⟩
        u.toRestrictedWeilComplexTest =
      a.val * suzukiRestrictedWeilComplexIntervalEnergy suzukiUnitAperture
        (ccmComplexSmoothInteriorSourceUnitPullback a u) := by
  let v := ccmComplexSmoothInteriorSourceUnitPullback a u
  let ur := suzukiRestrictedWeilRealTestToCore suzukiUnitAperture v.realPart
  let ui := suzukiRestrictedWeilRealTestToCore suzukiUnitAperture v.imagPart
  have hr := suzukiRescaledCore_intervalEnergy a ur
  have hi := suzukiRescaledCore_intervalEnergy a ui
  have hrfun : (suzukiRescaledCore a ur : ℝ → ℝ) = u.realCore := by
    simpa only [ur, v] using suzukiRescaledCore_unitPullback_real_eq a u
  have hifun : (suzukiRescaledCore a ui : ℝ → ℝ) = u.imagCore := by
    simpa only [ui, v] using suzukiRescaledCore_unitPullback_imag_eq a u
  rw [hrfun] at hr
  rw [hifun] at hi
  rw [suzukiRestrictedWeilComplexIntervalEnergy_eq,
    suzukiRestrictedWeilComplexIntervalEnergy_eq]
  change (∫ x in (-a.val)..a.val, u.realCore x ^ 2) +
      (∫ x in (-a.val)..a.val, u.imagCore x ^ 2) =
    a.val * ((∫ x in (-1 : ℝ)..1, ur x ^ 2) +
      ∫ x in (-1 : ℝ)..1, ui x ^ 2)
  rw [hr, hi]
  ring

/-- On a strict smooth source, completed form mass is literal physical interval energy. -/
theorem suzukiWeilIntervalFormMass_complexSmooth_eq
    (a : SuzukiPositiveAperture) (u : CCMComplexSmoothInteriorSource a) :
    suzukiWeilIntervalFormMass a u.toCCMFormVector =
      suzukiRestrictedWeilComplexIntervalEnergy a
        u.toRestrictedWeilComplexTest := by
  unfold suzukiWeilIntervalFormMass
  rw [norm_suzukiWeilIntervalFormEmbedding_eq_physical]
  change ‖((ccmArchimedeanFormToAperture a u.toCCMFormVector :
    suzukiApertureHilbert a) : SoninL2)‖ ^ 2 = _
  rw [norm_sq_eq_integral]
  calc
    (∫ x : ℝ,
        ‖((ccmArchimedeanFormToAperture a u.toCCMFormVector : SoninL2) :
          ℝ → ℂ) x‖ ^ 2) =
        ∫ x : ℝ, ‖u x‖ ^ 2 := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards [u.toCCMFormVector_physical_coeFn] with x hx
      rw [hx]
    _ = ∫ x in (-a.1)..a.1, ‖u x‖ ^ 2 := by
      symm
      apply intervalIntegral.integral_eq_integral_of_support_subset
      intro x hx
      have hux : u x ≠ 0 := by
        intro hzero
        exact hx (by simp [hzero])
      have hmem := u.support_subset hux
      exact ⟨hmem.1, hmem.2.le⟩
    _ = suzukiRestrictedWeilComplexIntervalEnergy a
        u.toRestrictedWeilComplexTest := rfl

/-- Uniform small-aperture coercivity on every literal strict CCM source. -/
theorem suzukiSmallScaleCoercivityCoefficient_mul_formMass_le_source
    (a : SuzukiPrimeFreeSmallAperture)
    (u : CCMComplexSmoothInteriorSource ⟨a.val, a.pos⟩) :
    suzukiSmallScaleCoercivityCoefficient a.val *
        suzukiWeilIntervalFormMass ⟨a.val, a.pos⟩ u.toCCMFormVector ≤
      ccmRestrictedWeilSourceQuadratic ⟨a.val, a.pos⟩ u.toCCMFormVector := by
  let v := ccmComplexSmoothInteriorSourceUnitPullback a u
  have hcoerce := suzukiRescaledComplexSourceForm_coercive a v
  rw [suzukiWeilIntervalFormMass_complexSmooth_eq,
    ccmRestrictedWeilSourceQuadratic_eq_rescaledComplexSourceForm,
    suzukiRestrictedWeilComplexIntervalEnergy_unitPullback]
  calc
    suzukiSmallScaleCoercivityCoefficient a.val *
          (a.val * suzukiRestrictedWeilComplexIntervalEnergy suzukiUnitAperture v) =
        a.val * (suzukiSmallScaleCoercivityCoefficient a.val *
          suzukiRestrictedWeilComplexIntervalEnergy suzukiUnitAperture v) := by ring
    _ ≤ a.val * ((1 / a.val) * suzukiRescaledComplexSourceForm a v) :=
      mul_le_mul_of_nonneg_left hcoerce a.pos.le
    _ = suzukiRescaledComplexSourceForm a v := by
      field_simp [a.pos.ne']

/-- Quantitative lower bound for the actual lowest interval eigenvalue. -/
theorem suzukiSmallScaleCoercivityCoefficient_le_intervalGroundEnergy
    (a : SuzukiPrimeFreeSmallAperture) :
    suzukiSmallScaleCoercivityCoefficient a.val ≤
      suzukiWeilIntervalGroundEnergy ⟨a.val, a.pos⟩ := by
  apply (isGLB_suzukiSmoothInteriorRayleighSet_groundEnergy
    ⟨a.val, a.pos⟩).2
  rintro r ⟨u, hu, rfl⟩
  have hmass : 0 < suzukiWeilIntervalFormMass ⟨a.val, a.pos⟩
      u.toCCMFormVector := by
    unfold suzukiWeilIntervalFormMass
    exact pow_pos (norm_pos_iff.mpr hu) 2
  rw [suzukiWeilIntervalFormRayleigh, le_div_iff₀ hmass]
  exact suzukiSmallScaleCoercivityCoefficient_mul_formMass_le_source a u

/-- Same quantitative bound for the exact CCM/Friedrichs ground energy. -/
theorem suzukiSmallScaleCoercivityCoefficient_le_ccmGroundEnergy
    (a : SuzukiPrimeFreeSmallAperture) :
    suzukiSmallScaleCoercivityCoefficient a.val ≤
      ccmRestrictedWeilGroundEnergy ⟨a.val, a.pos⟩ := by
  rw [← suzukiWeilIntervalGroundEnergy_eq_ccmRestrictedWeilGroundEnergy]
  exact suzukiSmallScaleCoercivityCoefficient_le_intervalGroundEnergy a

/-- Exact eventual positivity clause of Suzuki 2026, Theorem 1.4. -/
theorem exists_suzukiSmallAperture_ccmGroundEnergy_pos :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ a : SuzukiPositiveAperture, a.1 < delta →
        0 < ccmRestrictedWeilGroundEnergy a := by
  obtain ⟨a0, hcoefficient⟩ := exists_suzukiCoercivePrimeFreeSmallAperture
  let A0 : SuzukiPositiveAperture := ⟨a0.val, a0.pos⟩
  have hground0 : 0 < ccmRestrictedWeilGroundEnergy A0 :=
    hcoefficient.trans_le
      (suzukiSmallScaleCoercivityCoefficient_le_ccmGroundEnergy a0)
  refine ⟨a0.val, a0.pos, fun a ha => ?_⟩
  have haa0 : a ≤ A0 := by
    exact ha.le
  exact hground0.trans_le (antitone_ccmRestrictedWeilGroundEnergy haa0)

/-- Paper notation version: the actual interval lowest eigenvalue is eventually positive. -/
theorem exists_suzukiSmallAperture_intervalGroundEnergy_pos :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ a : SuzukiPositiveAperture, a.1 < delta →
        0 < suzukiWeilIntervalGroundEnergy a := by
  obtain ⟨delta, hdelta, hpos⟩ :=
    exists_suzukiSmallAperture_ccmGroundEnergy_pos
  refine ⟨delta, hdelta, fun a ha => ?_⟩
  rw [suzukiWeilIntervalGroundEnergy_eq_ccmRestrictedWeilGroundEnergy]
  exact hpos a ha

end RHTower
