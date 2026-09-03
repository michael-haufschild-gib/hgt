import GaloisForLFunctions.HTGeometry.AlgebraSpectrumBaseChange

/-!
# Smooth paths in affine complex-point spaces

An affine complex algebraic set is embedded in the product of one copy of `ℂ` for every regular
function.  A path is smooth exactly when every regular-function evaluation along it is smooth.
This definition is presentation-independent: it uses the whole coordinate algebra rather than a
chosen generating family.

This file proves that the canonical scalar-extension homeomorphism from
`AlgebraSpectrumBaseChange` also preserves and reflects these smooth paths.  Thus the affine
complex-point comparison respects both topology and smooth structure.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped TensorProduct

noncomputable section

universe u v

namespace AlgSpec

variable {B : Type v} [CommRing B] [Algebra ℂ B]

/-- A path through complex points of an affine complex algebra is smooth when evaluation of every
regular function along the path is smooth. -/
def IsSmoothPath (γ : ℝ → AlgSpec B) : Prop :=
  ∀ b : B, ContDiff ℝ ⊤ fun t => γ t b

/-- Every smooth affine complex-point path is continuous for pointwise-convergence topology. -/
theorem IsSmoothPath.continuous {γ : ℝ → AlgSpec B} (hγ : IsSmoothPath γ) : Continuous γ := by
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro b
  exact (hγ b).continuous

end AlgSpec

namespace RelativeAlgSpec

variable (k : Type u) (B : Type v) [CommSemiring k] [CommSemiring B]
  [Algebra k ℂ] [Algebra k B]

/-- A path through complex-valued points of a `k`-algebra is smooth when every regular-function
evaluation along it is smooth. -/
def IsSmoothPath (γ : ℝ → RelativeAlgSpec k B) : Prop :=
  ∀ b : B, ContDiff ℝ ⊤ fun t => γ t b

/-- Every smooth relative complex-point path is continuous for pointwise-convergence topology. -/
theorem IsSmoothPath.continuous {γ : ℝ → RelativeAlgSpec k B}
    (hγ : IsSmoothPath k B γ) : Continuous γ := by
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro b
  exact (hγ b).continuous

/-- Scalar extension preserves and reflects smooth paths.  This is the smooth counterpart of
`baseChangeHomeomorph`. -/
theorem isSmoothPath_scalarExtend_iff (γ : ℝ → RelativeAlgSpec k B) :
    AlgSpec.IsSmoothPath (fun t => scalarExtend k B (γ t)) ↔ IsSmoothPath k B γ := by
  rw [AlgSpec.IsSmoothPath, IsSmoothPath]
  constructor
  · intro h b
    convert h (Algebra.TensorProduct.includeRight b) using 1
    funext t
    symm
    change (restrict k B (scalarExtend k B (γ t))) b = (γ t) b
    exact congrArg
      (fun ψ : RelativeAlgSpec k B => ψ b)
      (restrict_scalarExtend k B (γ t))
  · intro h z
    induction z using TensorProduct.induction_on with
    | zero =>
        change ContDiff ℝ ⊤ fun _ : ℝ => (0 : ℂ)
        exact contDiff_const
    | tmul a b =>
        change ContDiff ℝ ⊤ fun t : ℝ => a * γ t b
        exact contDiff_const.mul (h b)
    | add x y hx hy =>
        rw [show (fun t : ℝ =>
            (scalarExtend k B (γ t) : (ℂ ⊗[k] B) →ₐ[ℂ] ℂ) (x + y)) =
          (fun t =>
            (scalarExtend k B (γ t) : (ℂ ⊗[k] B) →ₐ[ℂ] ℂ) x +
            (scalarExtend k B (γ t) : (ℂ ⊗[k] B) →ₐ[ℂ] ℂ) y) by
              funext t
              exact map_add _ _ _]
        exact hx.add hy

end RelativeAlgSpec

end

end GaloisForLFunctions.HTGeometry
