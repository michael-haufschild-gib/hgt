import GaloisForLFunctions.HTGeometry.ParabolicOuterOrbitLimit
import GaloisForLFunctions.HTGeometry.CauchyTransformHalfPlane

/-!
# The parabolic disc automorphisms and the bounded outer carrier

The Cayley pair identifies the open unit disc with the open upper half plane, and the parabolic
automorphism of the disc is by definition the half-plane translation read through that pair.  The
outer carrier of a measure is the exponential of the Cayley transform of its Cauchy transform, so
its parabolic orbit is exactly the translated object of the previous module.

Because the Cayley transform of a point of the open upper half plane has modulus strictly below
one, the carrier and its powers are trapped between `exp (-N)` and `exp N` in modulus: the orbit
can never approach a nonzero constant of smaller modulus, which is the quantitative source of the
failure of universality.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Filter Set

open scoped Topology

noncomputable section

/-- The Cayley map from the open upper half plane onto the open unit disc. -/
def cayleyToDisc (z : ℂ) : ℂ := (z - Complex.I) / (z + Complex.I)

theorem add_I_ne_zero_of_im_pos {z : ℂ} (hz : 0 < z.im) : z + Complex.I ≠ 0 := by
  intro h
  have him : (z + Complex.I).im = z.im + 1 := by simp
  rw [h] at him
  simp only [Complex.zero_im] at him
  linarith

/-- Above the real axis the Cayley map is a strict contraction into the unit disc. -/
theorem norm_cayleyToDisc_lt_one {z : ℂ} (hz : 0 < z.im) : ‖cayleyToDisc z‖ < 1 := by
  have hzi : z + Complex.I ≠ 0 := add_I_ne_zero_of_im_pos hz
  have hsq : Complex.normSq (z - Complex.I) < Complex.normSq (z + Complex.I) := by
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.add_re,
      Complex.add_im, Complex.I_re, Complex.I_im]
    nlinarith [hz]
  have hnorm : ‖z - Complex.I‖ < ‖z + Complex.I‖ := by
    have h1 : ‖z - Complex.I‖ ^ 2 < ‖z + Complex.I‖ ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
      exact hsq
    nlinarith [norm_nonneg (z - Complex.I), norm_nonneg (z + Complex.I)]
  rw [cayleyToDisc, norm_div, div_lt_one (by positivity)]
  · exact hnorm

/-- The Cayley pair is a left inverse above the real axis. -/
theorem cayleyToUpper_cayleyToDisc {z : ℂ} (hz : 0 < z.im) :
    cayleyToUpper (cayleyToDisc z) = z := by
  have hzi : z + Complex.I ≠ 0 := add_I_ne_zero_of_im_pos hz
  have hone : (1 : ℂ) - cayleyToDisc z = 2 * Complex.I / (z + Complex.I) := by
    rw [cayleyToDisc]
    field_simp
    ring
  have hne1 : (1 : ℂ) - cayleyToDisc z ≠ 0 := by
    rw [hone]
    exact div_ne_zero (by simp [Complex.I_ne_zero]) hzi
  rw [cayleyToUpper, div_eq_iff hne1, cayleyToDisc]
  field_simp
  ring

/-- The parabolic automorphism of the disc: the half-plane translation read on the disc. -/
def parabolicAut (t : ℝ) (w : ℂ) : ℂ := cayleyToDisc (cayleyToUpper w + (t : ℂ))

theorem im_cayleyToUpper_add_pos {t : ℝ} {w : ℂ} (hw : ‖w‖ < 1) :
    0 < (cayleyToUpper w + (t : ℂ)).im := by
  have h : (cayleyToUpper w + (t : ℂ)).im = (cayleyToUpper w).im := by simp
  rw [h]
  exact im_cayleyToUpper_pos hw

theorem norm_parabolicAut_lt_one {t : ℝ} {w : ℂ} (hw : ‖w‖ < 1) : ‖parabolicAut t w‖ < 1 :=
  norm_cayleyToDisc_lt_one (im_cayleyToUpper_add_pos hw)

/-- **The parabolic automorphism translates the half-plane coordinate.** -/
theorem cayleyToUpper_parabolicAut {t : ℝ} {w : ℂ} (hw : ‖w‖ < 1) :
    cayleyToUpper (parabolicAut t w) = cayleyToUpper w + (t : ℂ) :=
  cayleyToUpper_cayleyToDisc (im_cayleyToUpper_add_pos hw)

/-- The bounded outer carrier of a measure, read on the disc. -/
def outerCarrier (ν : Measure ℝ) (w : ℂ) : ℂ :=
  Complex.exp (cayleyToDisc (cauchyTransform ν (cayleyToUpper w)))

theorem discExponent_eq_cayleyToDisc (ν : Measure ℝ) (t : ℝ) (w : ℂ) :
    discExponent ν t w = cayleyToDisc (cauchyTransform ν (cayleyToUpper w + (t : ℂ))) := rfl

/-- **The translated object is the parabolic orbit of the carrier.** -/
theorem parabolicOuterOrbit_eq_outerCarrier_pow (ν : Measure ℝ) (N : ℕ) (t : ℝ) {w : ℂ}
    (hw : ‖w‖ < 1) :
    parabolicOuterOrbit ν N t w = (outerCarrier ν (parabolicAut t w)) ^ N := by
  rw [parabolicOuterOrbit, outerCarrier, cayleyToUpper_parabolicAut hw,
    discExponent_eq_cayleyToDisc, ← Complex.exp_nat_mul]

/-- The Cauchy transform of a nonzero finite positive measure has strictly positive imaginary part
above the real axis. -/
theorem im_cauchyTransform_pos_of_ne_zero (ν : Measure ℝ) [IsFiniteMeasure ν] (hν : ν ≠ 0)
    {z : ℂ} (hz : 0 < z.im) : 0 < (cauchyTransform ν z).im := by
  obtain ⟨P, hP, hdecomp⟩ := exists_mass_probability_decomposition ν hν
  have hmass : (0 : ℝ) < (ν Set.univ).toReal := by
    have hne : ν Set.univ ≠ 0 := Measure.measure_univ_ne_zero.mpr hν
    have htop : ν Set.univ ≠ ⊤ := measure_ne_top ν Set.univ
    exact ENNReal.toReal_pos hne htop
  have hval : cauchyTransform ν z = ((ν Set.univ).toReal : ℂ) * cauchyTransform P z := by
    conv_lhs => rw [hdecomp]
    exact cauchyTransform_smul _ P z
  rw [hval, Complex.mul_im]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
  exact mul_pos hmass (im_cauchyTransform_pos P hz)

/-- The Cayley exponent of a nonzero finite measure has modulus strictly below one. -/
theorem norm_discExponent_lt_one (ν : Measure ℝ) [IsFiniteMeasure ν] (hν : ν ≠ 0) (t : ℝ)
    {w : ℂ} (hw : ‖w‖ < 1) : ‖discExponent ν t w‖ < 1 := by
  rw [discExponent_eq_cayleyToDisc]
  exact norm_cayleyToDisc_lt_one
    (im_cauchyTransform_pos_of_ne_zero ν hν (im_cayleyToUpper_add_pos hw))

/-- **Two-sided modulus trap.**  Every point of every power of the parabolic orbit has modulus
strictly between `exp (-N)` and `exp N`. -/
theorem norm_parabolicOuterOrbit_bounds (ν : Measure ℝ) [IsFiniteMeasure ν] (hν : ν ≠ 0)
    (N : ℕ) (t : ℝ) {w : ℂ} (hw : ‖w‖ < 1) (hN : 0 < N) :
    Real.exp (-(N : ℝ)) < ‖parabolicOuterOrbit ν N t w‖ ∧
      ‖parabolicOuterOrbit ν N t w‖ < Real.exp (N : ℝ) := by
  have hlt : ‖discExponent ν t w‖ < 1 := norm_discExponent_lt_one ν hν t hw
  have hre : |(discExponent ν t w).re| < 1 :=
    lt_of_le_of_lt (Complex.abs_re_le_norm _) hlt
  have hnorm : ‖parabolicOuterOrbit ν N t w‖
      = Real.exp ((N : ℝ) * (discExponent ν t w).re) := by
    rw [parabolicOuterOrbit, Complex.norm_exp, Complex.mul_re]
    simp
  rw [hnorm]
  have hN' : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  constructor
  · refine Real.exp_lt_exp.mpr ?_
    have := abs_lt.mp hre
    nlinarith [this.1]
  · refine Real.exp_lt_exp.mpr ?_
    have := abs_lt.mp hre
    nlinarith [this.2]

end

end GaloisForLFunctions.HTGeometry
