import GaloisForLFunctions.HTGeometry.AlgebraSpectrumTopology

/-!
# Complex points and scalar extension

For a commutative `k`-algebra `B` equipped with an embedding of `k` into `ℂ`, the `k`-algebra
maps `B → ℂ` are canonically the complex points of the scalar extension `ℂ ⊗[k] B`.  Both spaces
carry pointwise-convergence topology.  This file proves that the algebraic scalar-extension
bijection is a homeomorphism, providing the affine complex-point chart used by later
scheme-analytification comparisons.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped TensorProduct

noncomputable section

universe u v

/-- Complex-valued points of a `k`-algebra, topologized by pointwise convergence. -/
def RelativeAlgSpec (k : Type u) (B : Type v) [CommSemiring k] [CommSemiring B]
    [Algebra k ℂ] [Algebra k B] :=
  B →ₐ[k] ℂ

namespace RelativeAlgSpec

variable (k : Type u) (B : Type v) [CommSemiring k] [CommSemiring B]
  [Algebra k ℂ] [Algebra k B]

instance : FunLike (RelativeAlgSpec k B) B ℂ :=
  inferInstanceAs (FunLike (B →ₐ[k] ℂ) B ℂ)

instance : AlgHomClass (RelativeAlgSpec k B) k B ℂ :=
  inferInstanceAs (AlgHomClass (B →ₐ[k] ℂ) k B ℂ)

instance : TopologicalSpace (RelativeAlgSpec k B) :=
  TopologicalSpace.induced (fun χ : RelativeAlgSpec k B => (χ : B → ℂ)) inferInstance

/-- Evaluation at one algebra element is continuous on the relative complex-point space. -/
theorem continuous_eval (b : B) : Continuous fun χ : RelativeAlgSpec k B => χ b := by
  refine Continuous.comp (continuous_apply b) ?_
  exact continuous_induced_dom

/-- Extend a `k`-point uniquely across scalar extension to a complex-algebra point. -/
def scalarExtend (χ : RelativeAlgSpec k B) : AlgSpec (ℂ ⊗[k] B) :=
  Algebra.TensorProduct.lift (AlgHom.id ℂ ℂ) χ fun _ _ => mul_comm _ _

/-- Restrict a point of the scalar extension to the original `k`-algebra. -/
def restrict (χ : AlgSpec (ℂ ⊗[k] B)) : RelativeAlgSpec k B :=
  (χ.restrictScalars k).comp Algebra.TensorProduct.includeRight

/-- Restriction after scalar extension returns the original relative point. -/
theorem restrict_scalarExtend (χ : RelativeAlgSpec k B) :
    restrict k B (scalarExtend k B χ) = χ := by
  apply AlgHom.ext
  intro b
  simp [restrict, scalarExtend]

/-- Scalar extension after restriction returns the original complex point. -/
theorem scalarExtend_restrict (χ : AlgSpec (ℂ ⊗[k] B)) :
    scalarExtend k B (restrict k B χ) = χ := by
  apply AlgHom.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
      simp only [scalarExtend, restrict, Algebra.TensorProduct.lift_tmul,
        AlgHom.coe_restrictScalars', AlgHom.coe_comp, Function.comp_apply, AlgHom.coe_id,
        id_eq]
      change a * (χ : (ℂ ⊗[k] B) →ₐ[ℂ] ℂ)
          (Algebra.TensorProduct.includeRight b) =
        (χ : (ℂ ⊗[k] B) →ₐ[ℂ] ℂ) (a ⊗ₜ[k] b)
      have ha : (χ : (ℂ ⊗[k] B) →ₐ[ℂ] ℂ) (a ⊗ₜ[k] 1) = a := by
        change (χ : (ℂ ⊗[k] B) →ₐ[ℂ] ℂ) (algebraMap ℂ (ℂ ⊗[k] B) a) = a
        exact (χ : (ℂ ⊗[k] B) →ₐ[ℂ] ℂ).commutes a
      calc
        a * (χ : (ℂ ⊗[k] B) →ₐ[ℂ] ℂ)
              (Algebra.TensorProduct.includeRight b) =
            (χ : (ℂ ⊗[k] B) →ₐ[ℂ] ℂ) (a ⊗ₜ[k] 1) *
              (χ : (ℂ ⊗[k] B) →ₐ[ℂ] ℂ)
                (Algebra.TensorProduct.includeRight b) := by rw [ha]
        _ = (χ : (ℂ ⊗[k] B) →ₐ[ℂ] ℂ)
              ((a ⊗ₜ[k] 1) * Algebra.TensorProduct.includeRight b) := by
            rw [map_mul]
        _ = (χ : (ℂ ⊗[k] B) →ₐ[ℂ] ℂ) (a ⊗ₜ[k] b) := by simp
  | add x y hx hy => simp [hx, hy]

/-- Scalar extension is continuous for pointwise-convergence topologies. -/
theorem continuous_scalarExtend : Continuous (scalarExtend k B) := by
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro z
  induction z using TensorProduct.induction_on with
  | zero =>
      change Continuous fun _ : RelativeAlgSpec k B => (0 : ℂ)
      exact continuous_const
  | tmul a b =>
      change Continuous fun χ : RelativeAlgSpec k B => a * χ b
      exact continuous_const.mul (continuous_eval k B b)
  | add x y hx hy =>
      change Continuous fun χ : RelativeAlgSpec k B =>
        (scalarExtend k B χ : (ℂ ⊗[k] B) →ₐ[ℂ] ℂ) (x + y)
      rw [show (fun χ : RelativeAlgSpec k B =>
          (scalarExtend k B χ : (ℂ ⊗[k] B) →ₐ[ℂ] ℂ) (x + y)) =
        (fun χ =>
          (scalarExtend k B χ : (ℂ ⊗[k] B) →ₐ[ℂ] ℂ) x +
          (scalarExtend k B χ : (ℂ ⊗[k] B) →ₐ[ℂ] ℂ) y) by
            funext χ
            exact map_add _ _ _]
      exact hx.add hy

/-- Restriction from the scalar extension is continuous for pointwise-convergence topologies. -/
theorem continuous_restrict : Continuous (restrict k B) := by
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro b
  change Continuous fun χ : AlgSpec (ℂ ⊗[k] B) =>
    χ (Algebra.TensorProduct.includeRight b)
  exact AlgSpec.continuous_eval _

/-- Relative complex points are canonically homeomorphic to complex points after scalar
extension. -/
def baseChangeHomeomorph : RelativeAlgSpec k B ≃ₜ AlgSpec (ℂ ⊗[k] B) where
  toFun := scalarExtend k B
  invFun := restrict k B
  left_inv := restrict_scalarExtend k B
  right_inv := scalarExtend_restrict k B
  continuous_toFun := continuous_scalarExtend k B
  continuous_invFun := continuous_restrict k B

end RelativeAlgSpec

end

end GaloisForLFunctions.HTGeometry
