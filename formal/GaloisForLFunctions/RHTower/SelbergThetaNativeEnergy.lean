import GaloisForLFunctions.RHTower.SelbergThetaNativeSource

/-!
# Exact native theta source energy

The complete source disk controls the weighted native energy. Unfolded means
identify its constant contribution exactly; the remaining energy is the weighted
square of the actual mean-zero source. No spectral occurrence is assumed.
-/

open Complex Set Filter Topology MeasureTheory UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry
namespace RHTower.SelbergThetaNativeEnergy
open D4BMModularCore D4BMJointSource D4BMGlobalAngularResponse SelbergThetaNativeSource
noncomputable section

private def b (q : XiZeroCopy) : ℝ := (xiSpectralPoint q).re
private def h (q : XiZeroCopy) : ℂ := xiSpectralPoint q-Complex.I

private theorem b_ne_zero (q : XiZeroCopy) : b q ≠ 0 := by
  simpa [b, xiSpectralPoint, Complex.mul_re, Complex.mul_im] using xi_divisor_support_im_ne_zero q.1

private theorem h_ne_zero (q : XiZeroCopy) : h q ≠ 0 := by
  intro hz
  have hr := congrArg Complex.re hz
  apply b_ne_zero q
  simpa [b,h] using hr

private theorem P_integrable : Integrable positiveSource angularMeasure :=
  MemLp.integrable (by norm_num) positiveSource_memLp

private theorem W_integrable (q : XiZeroCopy) : Integrable (modeSource q) angularMeasure :=
  MemLp.integrable (by norm_num) (modeSource_memLp q)

/-- Complete native weighted energy density, with every primitive-row cross term retained. -/
def energyDensity (q : XiZeroCopy) (z : UpperHalfPlane) : ℝ :=
  ‖modeSource q z‖^(2 : ℕ)/positiveSource z

/-- Actual integrated native energy in the positive theta weight. -/
def nativeEnergy (q : XiZeroCopy) : ℝ := ∫ z, energyDensity q z ∂angularMeasure

private theorem density_nonneg (q : XiZeroCopy) (z : UpperHalfPlane) : 0 ≤ energyDensity q z :=
  div_nonneg (sq_nonneg _) (positiveSource_pos z).le

private def diskDefect (q : XiZeroCopy) (z : UpperHalfPlane) : ℝ :=
  -(2/b q)*(modeSource q z).re-energyDensity q z

private theorem diskDefect_pos (q : XiZeroCopy) (z : UpperHalfPlane) : 0 < diskDefect q z := by
  have hd := modeSource_strict_disk q z
  have he : ‖(positiveSource z:ℂ)+(b q:ℂ)*modeSource q z‖^(2 : ℕ) =
      (positiveSource z)^(2 : ℕ)+(b q)^(2 : ℕ)*‖modeSource q z‖^(2 : ℕ)+
        2*b q*positiveSource z*(modeSource q z).re := by
    simp [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
    ring
  have hs : ‖(positiveSource z:ℂ)+(b q:ℂ)*modeSource q z‖^(2 : ℕ) < (positiveSource z)^(2 : ℕ) := by
    change ‖(positiveSource z:ℂ)+(b q:ℂ)*modeSource q z‖ < positiveSource z at hd
    nlinarith [norm_nonneg ((positiveSource z:ℂ)+(b q:ℂ)*modeSource q z), positiveSource_pos z]
  rw [he] at hs
  have hprod : ((b q)^(2 : ℕ)*positiveSource z)*diskDefect q z > 0 := by
    have heq : ((b q)^(2 : ℕ)*positiveSource z)*diskDefect q z =
        -((b q)^(2 : ℕ)*‖modeSource q z‖^(2 : ℕ)+2*b q*positiveSource z*(modeSource q z).re) := by
      unfold diskDefect energyDensity
      field_simp [b_ne_zero q, (positiveSource_pos z).ne']
      ring
    rw [heq]
    linarith
  by_contra hn
  exact (not_le_of_gt hprod) (mul_nonpos_of_nonneg_of_nonpos
    (mul_pos (sq_pos_of_ne_zero (b_ne_zero q)) (positiveSource_pos z)).le (le_of_not_gt hn))

/-- The complete weighted energy is absolutely integrable in the original native measure. -/
theorem energyDensity_integrable (q : XiZeroCopy) : Integrable (energyDensity q) angularMeasure := by
  have hm : Measurable (energyDensity q) :=
    ((modeSource_measurable q).norm.pow_const 2).div positiveSource_measurable
  apply ((W_integrable q).re.const_mul (-(2/b q))).mono' hm.aestronglyMeasurable
  filter_upwards with z
  rw [Real.norm_eq_abs, abs_of_nonneg (density_nonneg q z)]
  change energyDensity q z ≤ -(2/b q)*(modeSource q z).re
  have hd := diskDefect_pos q z
  unfold diskDefect at hd
  linarith

private theorem diskDefect_integrable (q : XiZeroCopy) : Integrable (diskDefect q) angularMeasure :=
  ((W_integrable q).re.const_mul (-(2/b q))).sub (energyDensity_integrable q)

private theorem integral_diskDefect_pos (q : XiZeroCopy) :
    0 < ∫ z, diskDefect q z ∂angularMeasure := by
  apply (integral_pos_iff_support_of_nonneg (fun z => (diskDefect_pos q z).le)
    (diskDefect_integrable q)).2
  have hp : 0 < ∫ z, positiveSource z ∂angularMeasure := by
    rw [positiveSource_integral]
    exact sourceMass_pos
  have hs := (integral_pos_iff_support_of_nonneg (fun z => (positiveSource_pos z).le) P_integrable).mp hp
  exact hs.trans_le (measure_mono (fun z _ => (diskDefect_pos q z).ne'))

private theorem real_mode_integral (q : XiZeroCopy) :
    (∫ z, (modeSource q z).re ∂angularMeasure) = -sourceMass*b q/‖h q‖^(2 : ℕ) := by
  have hr := integral_re (𝕜 := ℂ) (W_integrable q)
  change (∫ z, (modeSource q z).re ∂angularMeasure) = (∫ z, modeSource q z ∂angularMeasure).re at hr
  rw [hr, modeSource_integral]
  change (-(sourceMass:ℂ)/h q).re = _
  have hh : (h q).re = b q := by simp [h,b]
  simp only [Complex.div_re, Complex.neg_re, Complex.ofReal_re, Complex.neg_im, Complex.ofReal_im,
    neg_zero, zero_mul, zero_div, add_zero, hh, Complex.normSq_eq_norm_sq]

private theorem integral_diskDefect (q : XiZeroCopy) :
    (∫ z, diskDefect q z ∂angularMeasure) = 2*sourceMass/‖h q‖^(2 : ℕ)-nativeEnergy q := by
  have hs : (∫ z, diskDefect q z ∂angularMeasure) =
      (∫ z, -(2/b q)*(modeSource q z).re ∂angularMeasure)-
        (∫ z, energyDensity q z ∂angularMeasure) := by
    simpa only [diskDefect] using! integral_sub
      ((W_integrable q).re.const_mul (-(2/b q))) (energyDensity_integrable q)
  rw [hs, integral_const_mul, real_mode_integral]
  change -(2/b q)*(-sourceMass*b q/‖h q‖^(2 : ℕ))-nativeEnergy q = _
  field_simp [b_ne_zero q]

/-- Strict source disk transfer gives a quantitative native upper energy bound. -/
theorem nativeEnergy_upper (q : XiZeroCopy) :
    nativeEnergy q < 2*sourceMass/‖xiSpectralPoint q-Complex.I‖^(2 : ℕ) := by
  have hp := integral_diskDefect_pos q
  rw [integral_diskDefect] at hp
  change nativeEnergy q < 2*sourceMass/‖h q‖^(2 : ℕ)
  linarith

/-- The mean-zero source uses the original theta comparison and its exact spectral denominator. -/
def centeredSource (q : XiZeroCopy) (z : UpperHalfPlane) : ℂ :=
  modeSource q z+(positiveSource z:ℂ)/(xiSpectralPoint q-Complex.I)

private def centeredDensity (q : XiZeroCopy) (z : UpperHalfPlane) : ℝ :=
  ‖centeredSource q z‖^(2 : ℕ)/positiveSource z

private theorem centeredDensity_split (q : XiZeroCopy) (z : UpperHalfPlane) :
    centeredDensity q z = energyDensity q z+
      2*(modeSource q z*star ((h q)⁻¹)).re+positiveSource z*‖(h q)⁻¹‖^(2 : ℕ) := by
  change ‖modeSource q z+(positiveSource z:ℂ)*(h q)⁻¹‖^(2 : ℕ)/positiveSource z = _
  unfold energyDensity
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.star_def, Complex.conj_re, Complex.conj_im, zero_mul, add_zero, sub_zero]
  field_simp [(positiveSource_pos z).ne']
  ring

private theorem centeredDensity_integrable (q : XiZeroCopy) : Integrable (centeredDensity q) angularMeasure := by
  have hi := ((energyDensity_integrable q).add
    (((W_integrable q).mul_const (star ((h q)⁻¹))).re.const_mul 2)).add
      (P_integrable.mul_const (‖(h q)⁻¹‖^(2 : ℕ)))
  apply hi.congr
  filter_upwards with z
  exact (centeredDensity_split q z).symm

private theorem centeredDensity_integral (q : XiZeroCopy) :
    (∫ z, centeredDensity q z ∂angularMeasure) = nativeEnergy q-sourceMass/‖h q‖^(2 : ℕ) := by
  have hi := ((W_integrable q).mul_const (star ((h q)⁻¹))).re.const_mul 2
  have hs : (∫ z, centeredDensity q z ∂angularMeasure) =
      (∫ z, energyDensity q z+2*(modeSource q z*star ((h q)⁻¹)).re ∂angularMeasure)+
        (∫ z, positiveSource z*‖(h q)⁻¹‖^(2 : ℕ) ∂angularMeasure) := by
    simpa only [centeredDensity_split] using! integral_add ((energyDensity_integrable q).add hi)
      (P_integrable.mul_const (‖(h q)⁻¹‖^(2 : ℕ)))
  have ht : (∫ z, energyDensity q z+2*(modeSource q z*star ((h q)⁻¹)).re ∂angularMeasure) =
      nativeEnergy q+(∫ z, 2*(modeSource q z*star ((h q)⁻¹)).re ∂angularMeasure) := by
    simpa only [nativeEnergy] using! integral_add (energyDensity_integrable q) hi
  have hr := integral_re (𝕜 := ℂ) ((W_integrable q).mul_const (star ((h q)⁻¹)))
  change (∫ z, (modeSource q z*star ((h q)⁻¹)).re ∂angularMeasure) =
    (∫ z, modeSource q z*star ((h q)⁻¹) ∂angularMeasure).re at hr
  rw [hs, ht, integral_const_mul, hr, integral_mul_const, integral_mul_const,
    positiveSource_integral, modeSource_integral]
  change nativeEnergy q+2*((-(sourceMass:ℂ)/h q)*star ((h q)⁻¹)).re+
    sourceMass*‖(h q)⁻¹‖^(2 : ℕ) = _
  have he : ((-(sourceMass:ℂ)/h q)*star ((h q)⁻¹)).re = -sourceMass*‖(h q)⁻¹‖^(2 : ℕ) := by
    rw [div_eq_mul_inv, mul_assoc, Complex.star_def, Complex.mul_conj]
    simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.neg_im,
      Complex.ofReal_im, mul_zero, sub_zero, Complex.normSq_eq_norm_sq]
  rw [he, norm_inv, inv_pow]
  simp only [div_eq_mul_inv]
  ring

/-- The native energy cannot lose its exact mean contribution under complete periodization. -/
theorem nativeEnergy_lower (q : XiZeroCopy) :
    sourceMass/‖xiSpectralPoint q-Complex.I‖^(2 : ℕ) ≤ nativeEnergy q := by
  have hp : 0 ≤ ∫ z, centeredDensity q z ∂angularMeasure :=
    integral_nonneg (fun z => div_nonneg (sq_nonneg _) (positiveSource_pos z).le)
  rw [centeredDensity_integral] at hp
  change sourceMass/‖h q‖^(2 : ℕ) ≤ nativeEnergy q
  linarith

/-- Exact native centering has zero mean, with no component silently discarded. -/
theorem centeredSource_integral (q : XiZeroCopy) :
    (∫ z, centeredSource q z ∂angularMeasure) = 0 := by
  have hp := P_integrable.ofReal.div_const (h q)
  have hs : (∫ z, centeredSource q z ∂angularMeasure) =
      (∫ z, modeSource q z ∂angularMeasure)+
        (∫ z, (positiveSource z:ℂ)/h q ∂angularMeasure) := by
    simpa only [centeredSource,h] using! integral_add (W_integrable q) hp
  rw [hs, integral_div, integral_complex_ofReal, positiveSource_integral, modeSource_integral]
  dsimp [h]
  ring

/-- The actual centered source remains in the original native Hilbert space. -/
theorem centeredSource_memLp (q : XiZeroCopy) : MemLp (centeredSource q) 2 angularMeasure := by
  simpa only [centeredSource, div_eq_mul_inv, Pi.add_apply] using!
    (modeSource_memLp q).add (positiveSource_memLp.ofReal.mul_const ((xiSpectralPoint q-Complex.I)⁻¹))

/-- Native weighted mass of the exact mean-zero theta source. -/
def centeredEnergy (q : XiZeroCopy) : ℝ :=
  ∫ z, ‖centeredSource q z‖^(2 : ℕ)/positiveSource z ∂angularMeasure

/-- Exact variance decomposition after complete modular periodization. -/
theorem centeredEnergy_eq (q : XiZeroCopy) :
    centeredEnergy q = nativeEnergy q-sourceMass/‖xiSpectralPoint q-Complex.I‖^(2 : ℕ) :=
  centeredDensity_integral q

/-- Both native source energy and the surviving centered energy are finite and controlled. -/
theorem centeredEnergy_bounds (q : XiZeroCopy) :
    0 ≤ centeredEnergy q ∧ centeredEnergy q < sourceMass/‖xiSpectralPoint q-Complex.I‖^(2 : ℕ) := by
  rw [centeredEnergy_eq]
  constructor
  · linarith [nativeEnergy_lower q]
  · have hu := nativeEnergy_upper q
    rw [mul_div_assoc] at hu
    linarith

end
end RHTower.SelbergThetaNativeEnergy
