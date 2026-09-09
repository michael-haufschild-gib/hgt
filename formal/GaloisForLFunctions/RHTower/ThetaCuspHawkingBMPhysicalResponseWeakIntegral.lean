import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMPhysicalResponseEndpoint
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCompleteAngularSourceContinuity

/-! Literal integral testing of the original physical response retains its complete source. -/
open Complex Set Filter MeasureTheory
open scoped ComplexConjugate SchwartzMap
namespace RHTower.D4BMJointWave
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- Conjugation preserves the original smooth compact radial domain. -/
def RadialCore.conjugate (f : RadialCore) : RadialCore where
  field t := conj (f.field t)
  smooth := Complex.conjCLE.contDiff.comp f.smooth
  compact := f.compact.mono (by intro t ht he; exact ht (by simp [he]))
  support := (closure_mono (by intro t ht he; exact ht (by simp [he]))).trans f.support

/-- An actual radial Hilbert pairing equals the integral against any admitted representative. -/
theorem radial_inner_representative (v u : RadialSpace) (φ f : ℝ → ℂ)
    (hv : v =ᵐ[radialMeasure] φ) (hu : u =ᵐ[radialMeasure] f) :
    inner ℂ v u = ∫ t in Iio (0:ℝ), conj (φ t)*f t := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hv,hu] with t ht hs
  rw [ht,hs]
  change f t*conj (φ t) = _
  ring

/-- Compact original radial tests pair integrably with every representative of an original L² vector. -/
theorem radial_test_representative_integrable (f : RadialCore) (u : RadialSpace) (g : ℝ → ℂ)
    (hu : u =ᵐ[radialMeasure] g) : Integrable (fun t => f.field t*g t) := by
  have hi : Integrable (fun t => f.field t*g t) radialMeasure := by
    apply (L2.integrable_inner (𝕜 := ℂ) (radialValue f.conjugate) u).congr
    filter_upwards [radialValue_ae f.conjugate,hu] with t ht hs
    rw [ht,hs]
    change g t*conj (conj (f.field t)) = _
    simp only [starRingEnd_self_apply,mul_comm]
  apply (integrableOn_iff_integrable_of_support_subset (s := Iio (0:ℝ)) ?_).mp hi
  intro t ht
  apply f.support
  apply subset_tsupport f.field
  intro hz
  exact ht (by simp only [hz,zero_mul])

end
end RHTower.D4BMJointWave

namespace RHTower.D4BMJointSource
open D4BMJointWave GaloisForLFunctions.HTGeometry
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- The original physical profile solves its complete radial equation against literal unconjugated tests. -/
theorem physicalCuspProfile_weak_equation (q r : XiZeroCopy) (branch : Bool) (w a : ℂ)
    (hw : 0 < w.re) (hd : 3/2 < w.re) (hwi : w.im ≠ 0) (hwr : |w.re| < 2) (f : RadialCore) :
    (∫ t in Iio (0:ℝ), deriv (deriv f.field) t*physicalCuspProfile q r branch w a hw hd hwi hwr t)+
      (physicalAngularParameter r^2-1/4)*(∫ t in Iio (0:ℝ),
        f.field t*(angularWeight t^2*physicalCuspProfile q r branch w a hw hd hwi hwr t))-
      w^2*(∫ t in Iio (0:ℝ), f.field t*physicalCuspProfile q r branch w a hw hd hwi hwr t) =
      -(∫ t in Iio (0:ℝ), f.field t*continuedAngularSourceProjection q branch (physicalAngularParameter r) a w t) := by
  have h := physicalCuspResponse_radial_equation q r branch w a hw hd hwi hwr f.conjugate
  have hp := (physicalCuspProfile_ae q r branch w a hw hd hwi hwr).symm
  have h₂ : radialDerivative f.conjugate.differentiate =ᵐ[radialMeasure]
      fun t => conj (deriv (deriv f.field) t) := by
    apply (radialDerivative_ae _).trans
    filter_upwards with t
    change deriv (deriv (fun t => star (f.field t))) t = star (deriv (deriv f.field) t)
    simp only [deriv.star']
  rw [radial_inner_representative _ _ _ _ h₂ hp,
    radial_inner_representative _ _ _ _ (RadialCore.angularWeighted_twice_ae _) hp,
    radial_inner_representative _ _ _ _ (radialValue_ae _) hp,
    radial_inner_representative _ _ _ _ (radialValue_ae _)
      (continuedAngularSourceL2_ae q branch _ a w hwi hwr)] at h
  simpa only [RadialCore.conjugate,map_mul,map_pow,angularWeight,Complex.conj_ofReal,
    starRingEnd_self_apply,mul_assoc,mul_left_comm,mul_comm] using h

end
end RHTower.D4BMJointSource
