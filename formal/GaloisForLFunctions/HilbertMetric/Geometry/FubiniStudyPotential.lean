import GaloisForLFunctions.HTGeometry.ComplexAnalysis.RadialAntiholomorphicDerivative
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# The affine Fubini–Study potential and its Levi form

The logarithmic squared-radius potential has an explicit real differential
and Hessian. Its Levi form is strictly positive in every complex Hilbert
dimension, with two-sided norm bounds. The antiholomorphic differential
has sharp norm one half on the unit sphere and vanishes only at the origin.
The real radial Hessian exhibits the distinct radial sign change.
-/

noncomputable section
namespace GaloisForLFunctions.HilbertMetric.FubiniStudy
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
local instance : InnerProductSpace ℝ E := InnerProductSpace.rclikeToReal ℂ E

def denominator (z : E) : ℝ := 1 + ‖z‖ ^ 2

def potential (z : E) : ℝ := Real.log (denominator z)

def complexPotential (z : E) : ℂ := (potential z : ℂ)

omit [InnerProductSpace ℂ E] in
theorem denominator_pos (z : E) : 0 < denominator z := by
  unfold denominator
  positivity

private theorem log_profile_deriv (s : NNReal) :
    HasDerivAt (fun t : ℝ => Real.log (1 + t)) (1 / (1 + s)) s := by
  convert ((hasDerivAt_id (s : ℝ)).const_add 1).log
    (by change 1 + (s : ℝ) ≠ 0; positivity) using 1 <;> simp

/-- The antiholomorphic gradient of the affine Fubini–Study potential. -/
theorem dbar_potential (z : E) :
    HTGeometry.dbarDifferential complexPotential z =
      ((1 / denominator z : ℝ) : ℂ) • HTGeometry.conjugateInnerFunctional z := by
  exact HTGeometry.dbarDifferential_radial_sq (log_profile_deriv ⟨‖z‖ ^ 2, sq_nonneg _⟩)

/-- Exact operator norm of the antiholomorphic differential. -/
theorem norm_dbar_potential (z : E) :
    ‖HTGeometry.dbarDifferential complexPotential z‖ = ‖z‖ / denominator z := by
  have h := HTGeometry.norm_dbarDifferential_radial_sq
    (log_profile_deriv ⟨‖z‖ ^ 2, sq_nonneg _⟩)
  change ‖HTGeometry.dbarDifferential complexPotential z‖ =
    |1 / denominator z| * ‖z‖ at h
  rw [h, abs_of_pos (div_pos zero_lt_one (denominator_pos z))]
  ring

/-- The antiholomorphic gradient is globally bounded by one half. -/
theorem norm_dbar_potential_le_half (z : E) :
    ‖HTGeometry.dbarDifferential complexPotential z‖ ≤ 1 / 2 := by
  rw [norm_dbar_potential, div_le_iff₀ (denominator_pos z)]
  unfold denominator
  nlinarith only [sq_nonneg (‖z‖ - 1)]

/-- The sharp gradient bound is attained precisely on the unit sphere. -/
theorem norm_dbar_potential_eq_half_iff (z : E) :
    ‖HTGeometry.dbarDifferential complexPotential z‖ = 1 / 2 ↔ ‖z‖ = 1 := by
  rw [norm_dbar_potential, div_eq_iff (denominator_pos z).ne']
  unfold denominator
  constructor
  · intro h
    have hs : (‖z‖ - 1) ^ 2 = 0 := by nlinarith only [h]
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hs)
  · intro h
    rw [h]
    norm_num

/-- The potential is antiholomorphically stationary only at the origin. -/
theorem dbar_potential_eq_zero_iff (z : E) :
    HTGeometry.dbarDifferential complexPotential z = 0 ↔ z = 0 := by
  rw [← norm_eq_zero, norm_dbar_potential, div_eq_zero_iff]
  simp only [(denominator_pos z).ne', or_false, norm_eq_zero]



/-- The real differential of the squared-radius denominator. -/
theorem hasFDerivAt_denominator (z : E) :
    HasFDerivAt denominator ((2 : ℝ) • innerSL ℝ z) z := by
  have h : HasFDerivAt (fun w : E => ‖w‖ ^ 2) ((2 : ℝ) • innerSL ℝ z) z := by
    simpa only [two_nsmul, two_smul ℝ] using (hasStrictFDerivAt_norm_sq z).hasFDerivAt
  exact h.const_add 1

/-- The real differential of the logarithmic projective potential. -/
theorem hasFDerivAt_potential (z : E) :
    HasFDerivAt potential ((2 / denominator z) • innerSL ℝ z) z := by
  have h := (hasFDerivAt_denominator z).log (denominator_pos z).ne'
  change HasFDerivAt potential ((denominator z)⁻¹ • ((2 : ℝ) • innerSL ℝ z)) z at h
  rw [smul_smul] at h
  convert h using 1
  congr 1
  ring

/-- First directional derivative, valid at every affine coordinate. -/
theorem fderiv_potential_apply (z v : E) :
    fderiv ℝ potential z v = 2 * inner ℝ z v / denominator z := by
  rw [(hasFDerivAt_potential z).fderiv]
  change (2 / denominator z) * inner ℝ z v = _
  ring

/-- The complexified real potential is complex differentiable only at the origin. -/
theorem differentiableAt_complexPotential_iff (z : E) :
    DifferentiableAt ℂ complexPotential z ↔ z = 0 := by
  constructor
  · intro h
    exact (dbar_potential_eq_zero_iff z).mp (HTGeometry.dbarDifferential_eq_zero h)
  · rintro rfl
    have hr := Complex.ofRealCLM.hasFDerivAt.comp (0 : E) (hasFDerivAt_potential (0 : E))
    have hz : HasFDerivAt complexPotential (0 : E →L[ℝ] ℂ) (0 : E) := by
      have he : Complex.ofRealCLM.comp ((2 / denominator (0 : E)) • innerSL ℝ (0 : E)) = 0 := by
        ext v
        change ((2 / denominator (0 : E) * inner ℝ (0 : E) v : ℝ) : ℂ) = 0
        simp only [inner_zero_left, mul_zero, Complex.ofReal_zero]
      change HasFDerivAt complexPotential _ (0 : E) at hr
      rw [he] at hr
      exact hr
    exact (hasFDerivAt_of_restrictScalars ℝ hz (by rfl :
      (0 : E →L[ℂ] ℂ).restrictScalars ℝ = 0)).differentiableAt

/-- The actual second directional derivative of the potential. -/
def hessian (z x y : E) : ℝ :=
  fderiv ℝ (fun w : E => fderiv ℝ potential w x) z y

/-- The Hessian separates a radial rank-one correction from the ambient metric. -/
theorem hessian_formula (z x y : E) :
    hessian z x y = 2 * inner ℝ x y / denominator z -
      4 * inner ℝ z x * inner ℝ z y / denominator z ^ 2 := by
  have hi : HasDerivAt (fun t : ℝ => t⁻¹) (-1 / denominator z ^ 2) (denominator z) := by
    convert (hasDerivAt_id (denominator z)).inv (denominator_pos z).ne' using 1 <;> rfl
  have hr := hi.comp_hasFDerivAt z (hasFDerivAt_denominator z)
  have hn : HasFDerivAt (fun w : E => 2 * inner ℝ w x) ((2 : ℝ) • innerSL ℝ x) z := by
    have h := (innerSL ℝ x).hasFDerivAt.const_mul (2 : ℝ) (x := z)
    convert h using 1 <;> try rfl
    funext w
    exact congrArg (fun t : ℝ => 2 * t) (real_inner_comm x w)
  have h := hn.mul hr
  change HasFDerivAt (fun w : E => 2 * inner ℝ w x * (denominator w)⁻¹)
    ((2 * inner ℝ z x) • ((-1 / denominator z ^ 2) • ((2 : ℝ) • innerSL ℝ z)) +
      (denominator z)⁻¹ • ((2 : ℝ) • innerSL ℝ x)) z at h
  unfold hessian
  simp_rw [fderiv_potential_apply, div_eq_mul_inv]
  rw [h.fderiv]
  change (2 * inner ℝ z x) * ((-1 / denominator z ^ 2) * (2 * inner ℝ z y)) +
    (denominator z)⁻¹ * (2 * inner ℝ x y) = _
  ring



/-- The Levi quadratic form, extracted from the actual real Hessian. -/
def levi (z v : E) : ℝ :=
  (hessian z v v + hessian z (Complex.I • v) (Complex.I • v)) / 4

private theorem real_inner_I (z v : E) :
    inner ℝ z (Complex.I • v) = -(inner ℂ z v).im := by
  rw [real_inner_eq_re_inner ℂ, inner_smul_right]
  change (Complex.I * inner ℂ z v).re = _
  simp only [Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub]

/-- The Levi form is the ambient norm minus its projective radial correction. -/
theorem levi_formula (z v : E) :
    levi z v = ‖v‖ ^ 2 / denominator z - ‖inner ℂ z v‖ ^ 2 / denominator z ^ 2 := by
  have hi : ‖Complex.I • v‖ = ‖v‖ := by rw [norm_smul, Complex.norm_I, one_mul]
  rw [levi, hessian_formula, hessian_formula, real_inner_self_eq_norm_sq,
    real_inner_self_eq_norm_sq, hi, real_inner_I, real_inner_eq_re_inner ℂ]
  change (2 * ‖v‖ ^ 2 / denominator z -
    4 * (inner ℂ z v).re * (inner ℂ z v).re / denominator z ^ 2 +
    (2 * ‖v‖ ^ 2 / denominator z -
    4 * (-(inner ℂ z v).im) * (-(inner ℂ z v).im) / denominator z ^ 2)) / 4 = _
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  ring

/-- The Levi form has an explicit positive lower bound in every Hilbert dimension. -/
theorem levi_lower_bound (z v : E) :
    ‖v‖ ^ 2 / denominator z ^ 2 ≤ levi z v := by
  have hd := denominator_pos z
  have hc : ‖inner ℂ z v‖ ^ 2 ≤ ‖z‖ ^ 2 * ‖v‖ ^ 2 := by
    have h := (sq_le_sq₀ (norm_nonneg (inner ℂ z v))
      (mul_nonneg (norm_nonneg z) (norm_nonneg v))).mpr (norm_inner_le_norm z v)
    simpa only [mul_pow] using h
  rw [levi_formula]
  apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hd)).mp
  field_simp [hd.ne']
  unfold denominator
  nlinarith only [hc]

/-- The radial correction can only decrease the ambient Hermitian form. -/
theorem levi_upper_bound (z v : E) : levi z v ≤ ‖v‖ ^ 2 / denominator z := by
  rw [levi_formula]
  exact sub_le_self _ (div_nonneg (sq_nonneg _) (sq_nonneg _))

/-- Strict Levi positivity is equivalent to a nonzero tangent vector. -/
theorem levi_pos_iff (z v : E) : 0 < levi z v ↔ v ≠ 0 := by
  constructor
  · intro h hv
    subst v
    simp only [levi_formula, norm_zero, inner_zero_right, zero_pow (by decide : 2 ≠ 0),
      zero_div, sub_zero, lt_self_iff_false] at h
  · intro hv
    exact lt_of_lt_of_le (div_pos (sq_pos_of_pos (norm_pos_iff.mpr hv))
      (sq_pos_of_pos (denominator_pos z))) (levi_lower_bound z v)

/-- The real radial Hessian changes sign at the unit sphere. -/
theorem radial_hessian (z : E) :
    hessian z z z = 2 * ‖z‖ ^ 2 * (1 - ‖z‖ ^ 2) / denominator z ^ 2 := by
  rw [hessian_formula, real_inner_self_eq_norm_sq]
  have hd := (denominator_pos z).ne'
  field_simp [hd]
  unfold denominator
  ring

#print axioms dbar_potential
#print axioms norm_dbar_potential
#print axioms norm_dbar_potential_le_half
#print axioms norm_dbar_potential_eq_half_iff
#print axioms dbar_potential_eq_zero_iff
#print axioms hasFDerivAt_potential
#print axioms differentiableAt_complexPotential_iff
#print axioms hessian_formula
#print axioms levi_formula
#print axioms levi_lower_bound
#print axioms levi_upper_bound
#print axioms levi_pos_iff
#print axioms radial_hessian

end GaloisForLFunctions.HilbertMetric.FubiniStudy
