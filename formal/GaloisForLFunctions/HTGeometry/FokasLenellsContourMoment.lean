import GaloisForLFunctions.HTGeometry.FokasLenellsRawFifthScaling
import GaloisForLFunctions.HTGeometry.FokasLenellsContourScattering

/-!
# Compatibility covariance on the full nonlocal Fokas--Lenells contour

The actual imaginary-ray source is I times the reflected initial profile.
Reflection reverses the cubic coupling while multiplication by I reverses
its relative scaling sign. Together they multiply the compatibility moment
by I, preserving its zero locus on every spectral ray.
-/

open Complex Matrix MeasureTheory Filter Topology
namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section

/-- The actual imaginary-ray twist preserves compatibility, with its exact complex phase. -/
theorem compatibilityMoment_twistedPotential (q : SchwartzMap ℝ ℂ) :
    compatibilityMoment (twistedPotential q) = I*compatibilityMoment q := by
  have hm : (∫ x : ℝ, RHTower.negSchwartz' q x) = ∫ x : ℝ, q x := by
    change (∫ x : ℝ, q (-x)) = _
    exact integral_neg_eq_self (q : ℝ → ℂ) volume
  rw [twistedPotential,compatibilityMoment_smul,parityCoupling_reflection,hm,
    compatibilityMoment_parity_decomposition]
  ring_nf
  simp only [I_sq,I_pow_four]
  ring

theorem compatibilityMoment_twistedPotential_zero_iff (q : SchwartzMap ℝ ℂ) :
    compatibilityMoment (twistedPotential q) = 0 ↔ compatibilityMoment q = 0 := by
  rw [compatibilityMoment_twistedPotential]
  exact mul_eq_zero.trans (or_iff_right I_ne_zero)

theorem compatibilityMoment_contourSource (q : SchwartzMap ℝ ℂ) (vertical : Bool) :
    compatibilityMoment (contourSource q vertical) = (if vertical then I else 1)*compatibilityMoment q := by
  cases vertical <;> simp [contourSource,compatibilityMoment_twistedPotential]

theorem compatibilityMoment_contourSource_zero_iff (q : SchwartzMap ℝ ℂ) (vertical : Bool) :
    compatibilityMoment (contourSource q vertical) = 0 ↔ compatibilityMoment q = 0 := by
  cases vertical <;> simp [contourSource,compatibilityMoment_twistedPotential_zero_iff]

/-- Dividing by the actual cubic spectral parameter cancels both ray signs. -/
theorem contourReflection_cubic_quotient_eq (q : SchwartzMap ℝ ℂ)
    (vertical negative : Bool) (κ : ℝ) :
    contourReflectionAmplitude q vertical negative κ/(contourParameter vertical negative κ)^(3 : ℕ) =
      (if vertical then -I else 1)*
        (reflectionAmplitude (contourSource q vertical) κ/(Real.exp κ : ℂ)^(3 : ℕ)) := by
  have hi : (-I)^(3 : ℕ) = I := by
    ring_nf
    simp only [I_pow_three,neg_neg]
  cases vertical <;> cases negative <;>
    simp [contourReflectionAmplitude_eq,contourParameter,mul_pow,div_eq_mul_inv,inv_I,I_pow_three] <;> ring_nf
  simp [inv_I,hi]

/-- Every actual contour ray has the same evaluated cubic reflection coefficient. -/
theorem contourReflection_cubic_quotient_tendsto (q : SchwartzMap ℝ ℂ)
    (vertical negative : Bool) :
    Tendsto (fun κ : ℝ => contourReflectionAmplitude q vertical negative κ/
      (contourParameter vertical negative κ)^(3 : ℕ)) atBot (𝓝 (2*compatibilityMoment q)) := by
  have hh := (reflectionAmplitude_cubic_quotient_tendsto (contourSource q vertical)).const_mul
    (if vertical then -I else 1)
  have he : (if vertical then -I else 1)*(2*compatibilityMoment (contourSource q vertical)) =
      2*compatibilityMoment q := by
    rw [compatibilityMoment_contourSource]
    cases vertical
    · simp
    · simp only [↓reduceIte]
      ring_nf
      simp only [I_sq]
      ring
  have hfun : (fun κ : ℝ => contourReflectionAmplitude q vertical negative κ/
      (contourParameter vertical negative κ)^(3 : ℕ)) = fun κ =>
      (if vertical then -I else 1)*(reflectionAmplitude (contourSource q vertical) κ/(Real.exp κ : ℂ)^(3 : ℕ)) := by
    funext κ
    exact contourReflection_cubic_quotient_eq q vertical negative κ
  rw [hfun]
  simpa only [he] using hh

/-- The reverse channel has the opposite cubic coefficient on every actual ray. -/
theorem contourReverseReflection_cubic_quotient_tendsto (q : SchwartzMap ℝ ℂ)
    (vertical negative : Bool) :
    Tendsto (fun κ : ℝ => contourReverseReflectionAmplitude q vertical negative κ/
      (contourParameter vertical negative κ)^(3 : ℕ)) atBot (𝓝 (-2*compatibilityMoment q)) := by
  have he : (fun κ : ℝ => contourReverseReflectionAmplitude q vertical negative κ/
      (contourParameter vertical negative κ)^(3 : ℕ)) =
      fun κ => -(contourReflectionAmplitude q vertical negative κ/(contourParameter vertical negative κ)^(3 : ℕ)) := by
    funext κ
    rw [contourReverseReflectionAmplitude_eq_neg,neg_div]
  rw [he]
  simpa only [neg_mul] using (contourReflection_cubic_quotient_tendsto q vertical negative).neg

end
end GaloisForLFunctions.HTGeometry.FokasLenells
