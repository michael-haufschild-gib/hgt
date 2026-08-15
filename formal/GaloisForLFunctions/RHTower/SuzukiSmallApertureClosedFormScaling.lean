import GaloisForLFunctions.RHTower.SuzukiSmallApertureFormScaling
import GaloisForLFunctions.RHTower.SuzukiLimitingLogGroundIdentification

open Complex MeasureTheory Set Filter Topology
open scoped ENNReal InnerProduct

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.RHTower

theorem ccmArchimedeanUnitSmallFormEquiv_complexCore
    (a : SuzukiPrimeFreeSmallAperture)
    (u : SuzukiRestrictedWeilComplexTest 1) :
    ccmArchimedeanUnitSmallFormEquiv a
        (suzukiLimitingComplexCoreFormVector u) =
      ((Real.sqrt a.val)⁻¹ : ℂ) •
        (ccmComplexSmoothInteriorSourceOfUnitRescale a u).toCCMFormVector := by
  apply ccmArchimedeanFormToAperture_injective _
  rw [← ccmArchimedeanUnitSmallFormEquiv_embedding]
  rw [map_smul]
  apply Subtype.ext
  change dilation a.val⁻¹ (inv_pos.mpr a.pos)
      (ccmArchimedeanFormToAperture suzukiLimitingUnitAperture
        (suzukiLimitingComplexCoreFormVector u)).1 =
    ((Real.sqrt a.val : ℂ)⁻¹) •
      (ccmArchimedeanFormToAperture ⟨a.val, a.pos⟩
        (ccmComplexSmoothInteriorSourceOfUnitRescale a u).toCCMFormVector).1
  apply MeasureTheory.Lp.ext
  have hunit :=
    (suzukiComplexTestInteriorSource u).toCCMFormVector_physical_coeFn
  have hunit' :
      (((ccmArchimedeanFormToAperture suzukiLimitingUnitAperture
          (suzukiLimitingComplexCoreFormVector u) :
            suzukiApertureHilbert suzukiLimitingUnitAperture) : SoninL2) : ℝ → ℂ)
        =ᵐ[volume] (suzukiComplexTestInteriorSource u).toFun := by
    simpa only [suzukiLimitingComplexCoreFormVector] using hunit
  have hsmall :=
    (ccmComplexSmoothInteriorSourceOfUnitRescale a u).toCCMFormVector_physical_coeFn
  have hdil := dilation_ae a.val⁻¹ (inv_pos.mpr a.pos)
    (ccmArchimedeanFormToAperture suzukiLimitingUnitAperture
      (suzukiLimitingComplexCoreFormVector u)).1
  have hunitAt := hunit'.comp_tendsto
    (realMul_quasiMeasurePreserving a.val⁻¹ (inv_ne_zero a.pos.ne')).tendsto_ae
  have hsmul := MeasureTheory.Lp.coeFn_smul ((Real.sqrt a.val : ℂ)⁻¹)
    ((ccmArchimedeanFormToAperture ⟨a.val, a.pos⟩
      (ccmComplexSmoothInteriorSourceOfUnitRescale a u).toCCMFormVector :
        suzukiApertureHilbert ⟨a.val, a.pos⟩) : SoninL2)
  filter_upwards [hdil, hunitAt, hsmall, hsmul] with x hdx hux hsx hsmx
  rw [hdx, hsmx]
  simp only [Function.comp_apply] at hux
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hux, hsx]
  change (Real.sqrt a.val⁻¹ : ℂ) * u (a.val⁻¹ * x) =
    ((Real.sqrt a.val : ℂ)⁻¹) * u (a.val⁻¹ * x)
  rw [Real.sqrt_inv]
  push_cast
  rfl

/-- Actual finite-aperture closed energy, pulled back unitarily to the fixed unit form domain. -/
def suzukiSmallScaledClosedEnergy
    (a : SuzukiPrimeFreeSmallAperture)
    (q : CCMArchimedeanFormDomain suzukiLimitingUnitAperture) : ℝ :=
  ccmRestrictedWeilSourceQuadratic ⟨a.val, a.pos⟩
    (ccmArchimedeanUnitSmallFormEquiv a q)

theorem suzukiSmallScaledClosedEnergy_complexCore
    (a : SuzukiPrimeFreeSmallAperture)
    (u : SuzukiRestrictedWeilComplexTest 1) :
    suzukiSmallScaledClosedEnergy a (suzukiLimitingComplexCoreFormVector u) =
      suzukiPrimeFreeScaledForm a u := by
  rw [suzukiSmallScaledClosedEnergy,
    ccmArchimedeanUnitSmallFormEquiv_complexCore,
    ccmRestrictedWeilSourceQuadratic_smul,
    ccmRestrictedWeilSourceQuadratic_ofUnitRescale_eq,
    ← suzukiRescaledComplexSourceForm_eq]
  congr 1
  rw [norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), inv_pow]
  rw [Real.sq_sqrt a.pos.le]
  field_simp [a.pos.ne']

end RHTower
