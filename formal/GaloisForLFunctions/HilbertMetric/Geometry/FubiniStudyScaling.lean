import GaloisForLFunctions.HilbertMetric.Geometry.FubiniStudyPotential

/-!
# Scalar pullbacks of the differentiated projective metric

The chain rule transports the first derivative, Hessian, and Levi form of
the logarithmic projective potential under real dilation. Nonzero dilation
preserves strict Levi positivity. These identities provide actual
derivatives for the radial Kähler–Einstein family.
-/

noncomputable section
namespace GaloisForLFunctions.HilbertMetric.FubiniStudy
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
local instance : InnerProductSpace ℝ E := InnerProductSpace.rclikeToReal ℂ E

/-- The first directional differential is itself differentiable everywhere. -/
theorem hasFDerivAt_potential_direction (z x : E) :
    HasFDerivAt (fun w : E => fderiv ℝ potential w x)
      ((-4 * inner ℝ z x / denominator z ^ 2) • innerSL ℝ z +
        (2 / denominator z) • innerSL ℝ x) z := by
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
  have he : (fun w : E => fderiv ℝ potential w x) =
      (fun w : E => 2 * inner ℝ w x * (denominator w)⁻¹) := by
    funext w
    rw [fderiv_potential_apply, div_eq_mul_inv]
  rw [he]
  convert h using 1
  ext y
  change (-4 * inner ℝ z x / denominator z ^ 2) * inner ℝ z y +
    (2 / denominator z) * inner ℝ x y =
    (2 * inner ℝ z x) * ((-1 / denominator z ^ 2) * (2 * inner ℝ z y)) +
      (denominator z)⁻¹ * (2 * inner ℝ x y)
  ring

/-- Pullback of the projective potential by a real scalar dilation. -/
def dilatedPotential (r : ℝ) (z : E) : ℝ := potential (r • z)

private def dilation (r : ℝ) : E →L[ℝ] E := r • 1

theorem hasFDerivAt_dilatedPotential (r : ℝ) (z : E) :
    HasFDerivAt (dilatedPotential r)
      (((2 / denominator (r • z)) • innerSL ℝ (r • z)).comp (dilation r)) z :=
  (hasFDerivAt_potential (r • z)).comp z (dilation r).hasFDerivAt

/-- First derivatives of the pullback act on the dilated tangent vector. -/
theorem fderiv_dilatedPotential_apply (r : ℝ) (z v : E) :
    fderiv ℝ (dilatedPotential r) z v = fderiv ℝ potential (r • z) (r • v) := by
  rw [(hasFDerivAt_dilatedPotential r z).fderiv, (hasFDerivAt_potential (r • z)).fderiv]
  rfl

/-- Differentiability of the first directional derivative survives scalar pullback. -/
theorem differentiableAt_dilatedPotential_direction (r : ℝ) (z x : E) :
    DifferentiableAt ℝ (fun w : E => fderiv ℝ (dilatedPotential r) w x) z := by
  simp_rw [fderiv_dilatedPotential_apply]
  exact ((hasFDerivAt_potential_direction (r • z) (r • x)).comp z
    (dilation r).hasFDerivAt).differentiableAt

/-- The actual second derivative of a dilated projective potential. -/
def dilatedHessian (r : ℝ) (z x y : E) : ℝ :=
  fderiv ℝ (fun w : E => fderiv ℝ (dilatedPotential r) w x) z y

/-- Scalar pullback transports the actual Hessian, including both tangent slots. -/
theorem dilatedHessian_eq (r : ℝ) (z x y : E) :
    dilatedHessian r z x y = hessian (r • z) (r • x) (r • y) := by
  have h := (hasFDerivAt_potential_direction (r • z) (r • x)).comp z
    (dilation r).hasFDerivAt
  unfold dilatedHessian
  simp_rw [fderiv_dilatedPotential_apply]
  rw [h.fderiv, hessian_formula]
  change (-4 * inner ℝ (r • z) (r • x) / denominator (r • z) ^ 2) *
      inner ℝ (r • z) (r • y) +
    (2 / denominator (r • z)) * inner ℝ (r • x) (r • y) = _
  ring

/-- Levi energy extracted from the differentiated pullback. -/
def dilatedLevi (r : ℝ) (z v : E) : ℝ :=
  (dilatedHessian r z v v +
    dilatedHessian r z (Complex.I • v) (Complex.I • v)) / 4

/-- The Levi pullback is the projective Levi form evaluated on the dilated tangent. -/
theorem dilatedLevi_eq (r : ℝ) (z v : E) :
    dilatedLevi r z v = levi (r • z) (r • v) := by
  rw [dilatedLevi, dilatedHessian_eq, dilatedHessian_eq, levi]
  rw [smul_comm r Complex.I v]

/-- Dilation scales the Levi metric by the square of its real scale. -/
theorem dilatedLevi_scale (r : ℝ) (z v : E) :
    dilatedLevi r z v = r ^ 2 * levi (r • z) v := by
  rw [dilatedLevi_eq, levi_formula, levi_formula, inner_smul_right_eq_smul]
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  ring

/-- Every nonzero dilation preserves strict plurisubharmonicity. -/
theorem dilatedLevi_pos_iff (r : ℝ) (z v : E) :
    0 < dilatedLevi r z v ↔ r ≠ 0 ∧ v ≠ 0 := by
  rw [dilatedLevi_eq, levi_pos_iff]
  simp only [ne_eq, smul_eq_zero, not_or]

#print axioms hasFDerivAt_potential_direction
#print axioms fderiv_dilatedPotential_apply
#print axioms dilatedHessian_eq
#print axioms dilatedLevi_eq
#print axioms dilatedLevi_scale
#print axioms dilatedLevi_pos_iff
end GaloisForLFunctions.HilbertMetric.FubiniStudy
