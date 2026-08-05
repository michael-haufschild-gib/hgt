import GaloisForLFunctions.HTGeometry.MultipleEllipticGammaPeriodRankDichotomy

/-!
# Period families on a rational ray exist

The rank dichotomy sorts period families by whether they lie on one rational ray through an
upper-half-plane direction.  That side of the dichotomy is inhabited: any rational multiple family
of a fixed upper-half-plane direction lies on its ray, and the constant family of the imaginary
unit is the simplest instance.  A rational ray is in particular a rational affine line, with zero
affine part, once the rational coefficients are positive.
-/

open Complex

namespace GaloisForLFunctions

noncomputable section

variable {ι : Type}

/-- **Every rational multiple family lies on a rational ray.** -/
theorem multipleEllipticGammaLiesOnRationalRay_ratSmul (c : ι → ℚ) {ω : ℂ} (hω : 0 < ω.im) :
    MultipleEllipticGammaLiesOnRationalRay (fun i => (c i : ℂ) * ω) :=
  ⟨ω, hω, c, fun _ => rfl⟩

/-- The constant family of the imaginary unit lies on a rational ray. -/
theorem multipleEllipticGammaLiesOnRationalRay_const_I :
    MultipleEllipticGammaLiesOnRationalRay (fun _ : ι => Complex.I) := by
  refine ⟨Complex.I, by simp, fun _ => (1 : ℚ), fun i => ?_⟩
  simp

/-- The rational-ray condition is inhabited for every index type. -/
theorem exists_multipleEllipticGammaLiesOnRationalRay :
    ∃ τ : ι → ℂ, MultipleEllipticGammaLiesOnRationalRay τ :=
  ⟨fun _ => Complex.I, multipleEllipticGammaLiesOnRationalRay_const_I⟩

/-- A rational ray with positive coefficients is a rational affine line with zero affine part. -/
theorem multipleEllipticGammaLiesOnRationalAffineLine_of_ratSmul
    (c : ι → ℚ) (hc : ∀ i, 0 < c i) {ω : ℂ} (hω : 0 < ω.im) :
    MultipleEllipticGammaLiesOnRationalAffineLine (fun i => (c i : ℂ) * ω) := by
  refine ⟨ω, hω, fun _ => 0, c, hc, fun i => ?_⟩
  simp

end

end GaloisForLFunctions
