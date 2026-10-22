import GaloisForLFunctions.RHTower.Suzuki.SuzukiApertureBoundedCoordinate
import GaloisForLFunctions.HTGeometry.LpBoundedSmulMultiplier

/-!
# Bounded position operator on Suzuki's aperture

The literal coordinate `x` on `L²([-a,a])` is a bounded self-adjoint multiplier.  Its zero
extension is exactly multiplication by the whole-line coordinate on the physical aperture.
-/

open Complex MeasureTheory Set

noncomputable section
namespace RHTower

attribute [local instance] Measure.Subtype.measureSpace

/-- Bounded position multiplication on Suzuki's literal aperture interval. -/
def suzukiAperturePosition (a : SuzukiPositiveAperture) :
    SuzukiApertureIntervalL2 a.1 →L[ℂ] SuzukiApertureIntervalL2 a.1 :=
  lpBoundedSmulCLM (p := 2) (μ := volume) (H := ℂ)
    (Complex.measurable_ofReal.comp measurable_subtype_coe)
    a.2.le
    (fun x => by
      simp only [Function.comp_apply]
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact abs_le.mpr x.2)

theorem suzukiAperturePosition_ae (a : SuzukiPositiveAperture)
    (f : SuzukiApertureIntervalL2 a.1) :
    (suzukiAperturePosition a f : SuzukiApertureInterval a.1 → ℂ) =ᵐ[volume]
      fun x => (x.1 : ℂ) * (f : SuzukiApertureInterval a.1 → ℂ) x := by
  simpa [suzukiAperturePosition, smul_eq_mul] using
    lpBoundedSmulCLM_coeFn (p := 2) (μ := volume) (H := ℂ)
      (Complex.measurable_ofReal.comp measurable_subtype_coe)
      a.2.le
      (fun x : SuzukiApertureInterval a.1 => by
        simp only [Function.comp_apply]
        rw [Complex.norm_real, Real.norm_eq_abs]
        exact abs_le.mpr x.2)
      f

theorem norm_suzukiAperturePosition_le (a : SuzukiPositiveAperture) :
    ‖suzukiAperturePosition a‖ ≤ a.1 := by
  exact norm_lpBoundedSmulCLM_le (p := 2) (μ := volume) (H := ℂ)
    (Complex.measurable_ofReal.comp measurable_subtype_coe)
    a.2.le
    (fun x : SuzukiApertureInterval a.1 => by
      simp only [Function.comp_apply]
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact abs_le.mpr x.2)

theorem suzukiAperturePosition_isSelfAdjoint (a : SuzukiPositiveAperture) :
    IsSelfAdjoint (suzukiAperturePosition a) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff']
  apply ContinuousLinearMap.ext
  intro f
  apply ext_inner_right ℂ
  intro g
  rw [(suzukiAperturePosition a).adjoint_inner_left]
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [suzukiAperturePosition_ae a g,
    suzukiAperturePosition_ae a f] with x hg hf
  rw [hg, hf]
  simp only [RCLike.inner_apply, map_mul, Complex.conj_ofReal]
  ring

theorem suzukiApertureZeroExtend_ae_position (a : SuzukiPositiveAperture)
    (f : SuzukiApertureIntervalL2 a.1) :
    suzukiApertureZeroExtend (suzukiAperturePosition a f) =ᵐ[volume]
      fun x : ℝ => (x : ℂ) * suzukiApertureZeroExtend f x := by
  apply ae_of_ae_restrict_of_ae_restrict_compl (Icc (-a.1) a.1)
  · rw [ae_restrict_iff_subtype measurableSet_Icc]
    filter_upwards [suzukiApertureRepresentative_ae (suzukiAperturePosition a f),
      suzukiApertureRepresentative_ae f,
      suzukiAperturePosition_ae a f] with x hX hf hpos
    rw [suzukiApertureZeroExtend_apply]
    rw [suzukiApertureZeroExtend_apply, hX, hf, hpos]
  · filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Icc.compl] with x hx
    have hx' : x ∉ Icc (-a.1) a.1 := hx
    rw [suzukiApertureZeroExtend_eq_zero_of_notMem _ hx',
      suzukiApertureZeroExtend_eq_zero_of_notMem f hx', mul_zero]

theorem suzukiApertureZeroExtendL2_position_ae (a : SuzukiPositiveAperture)
    (f : SuzukiApertureIntervalL2 a.1) :
    (suzukiApertureZeroExtendL2 (suzukiAperturePosition a f) : ℝ → ℂ) =ᵐ[volume]
      fun x : ℝ => (x : ℂ) * (suzukiApertureZeroExtendL2 f : ℝ → ℂ) x := by
  filter_upwards [suzukiApertureZeroExtendL2_coeFn (suzukiAperturePosition a f),
    suzukiApertureZeroExtend_ae_position a f,
    suzukiApertureZeroExtendL2_coeFn f] with x hX hpos hf
  rw [hX, hpos, hf]

end RHTower
end
