import GaloisForLFunctions.goldbach.LiLiu.ModelConvolution
import GaloisForLFunctions.goldbach.LiLiu.DensityEuler
import GaloisForLFunctions.goldbach.LiLiu.SingularDensity
import GaloisForLFunctions.RHTower.BoundedExponentPoissonNonlanding
import Mathlib.Analysis.Complex.RemovableSingularity

/-! # The removable pole in the single model contour

The signed profile has Mellin value zero at one. Dividing this transform
by w−1 using the derivative at one gives the holomorphic continuation of
its product with the density series across the pole.
-/

namespace GaloisForLFunctions.Goldbach.LiLiu
open _root_.Complex MeasureTheory Set Filter Asymptotics
open scoped Topology
noncomputable section

def profileMellin (φ : TestWeight) : ℂ → ℂ := mellin (fun t => (signedProfile φ t : ℂ))

private theorem signedProfile_continuous (φ : TestWeight) : Continuous (signedProfile φ) := by
  have hc := (sumProfile_smooth φ).continuous
  exact (continuous_const.mul (hc.comp (continuous_const.sub continuous_id))).sub hc

private theorem profileMellin_bounds (φ : TestWeight) (w : ℂ) :
    (fun t => (signedProfile φ t : ℂ)) =O[atTop] (fun t : ℝ => t ^ (-(w.re+1))) ∧
    (fun t => (signedProfile φ t : ℂ)) =O[𝓝[>] 0] (fun t : ℝ => t ^ (-(0 : ℝ))) := by
  have ht : (fun t => (signedProfile φ t : ℂ)) =ᶠ[atTop] fun _ => 0 := by
    filter_upwards [eventually_gt_atTop (2 : ℝ)] with t ht
    simp only [signedProfile, sumProfile_zero φ (show 1-t ∉ Icc (2/3:ℝ) (4/3) from
      fun h => by linarith only [h.1,ht]), sumProfile_zero φ (show t ∉ Icc (2/3:ℝ) (4/3) from
      fun h => by linarith only [h.2,ht]), mul_zero, sub_zero, Complex.ofReal_zero]
  have hc : Continuous (fun t => (signedProfile φ t : ℂ)) := continuous_ofReal.comp (signedProfile_continuous φ)
  exact ⟨ht.isBigO.trans (isBigO_zero _ _), by
    simpa only [neg_zero, Real.rpow_zero] using
      (hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).isBigO_one ℝ⟩

theorem profileMellin_differentiableAt (φ : TestWeight) {w : ℂ} (hw : 0 < w.re) :
    DifferentiableAt ℂ (profileMellin φ) w := by
  have hb := profileMellin_bounds φ w
  have hc := continuous_ofReal.comp (signedProfile_continuous φ)
  exact mellin_differentiableAt_of_isBigO_rpow (hc.continuousOn.locallyIntegrableOn measurableSet_Ioi)
    hb.1 (by linarith) hb.2 hw

theorem profileMellin_one (φ : TestWeight) : profileMellin φ 1 = 0 := by
  simp only [profileMellin, mellin, sub_self, Complex.cpow_zero, one_smul,
    integral_complex_ofReal, integral_signedProfile_Ioi, Complex.ofReal_zero]

/-- The continued single-contour integrand in the model evaluation. -/
def continuedProfileDensity (N : ℕ) (φ : TestWeight) (w : ℂ) : ℂ :=
  (singularSeries N : ℂ) * densityEuler N w * _root_.RHTower.zetaEntire w * dslope (profileMellin φ) 1 w

theorem continuedProfileDensity_eq {w : ℂ} (hw : w ≠ 1) (N : ℕ) (φ : TestWeight) :
    continuedProfileDensity N φ w =
      (singularSeries N : ℂ) * riemannZeta w * densityEuler N w * profileMellin φ w := by
  rw [continuedProfileDensity, _root_.RHTower.zetaEntire_eq hw, dslope_of_ne _ hw, slope_def_field,
    profileMellin_one, sub_zero]
  field_simp [sub_ne_zero.mpr hw]

theorem continuedProfileDensity_differentiableAt (N : ℕ) (φ : TestWeight) {w : ℂ} (hw : 0 < w.re) :
    DifferentiableAt ℂ (continuedProfileDensity N φ) w := by
  let U := {z : ℂ | 0 < z.re}
  have ho : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hs : DifferentiableOn ℂ (dslope (profileMellin φ) 1) U :=
    (Complex.differentiableOn_dslope (ho.mem_nhds (by norm_num [U]))).mpr
      fun z hz => (profileMellin_differentiableAt φ hz).differentiableWithinAt
  exact (((differentiableAt_const _).mul (densityEuler_differentiableAt N hw)).mul
    (_root_.RHTower.differentiable_zetaEntire w)).mul (hs.differentiableAt (ho.mem_nhds hw))

#print axioms profileMellin_one
#print axioms continuedProfileDensity_differentiableAt
end
end GaloisForLFunctions.Goldbach.LiLiu
