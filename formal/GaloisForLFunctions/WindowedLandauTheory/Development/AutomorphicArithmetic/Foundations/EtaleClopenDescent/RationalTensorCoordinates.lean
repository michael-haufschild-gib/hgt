import GaloisForLFunctions.HTGeometry.ABHN.AzumayaTensorProduct
import Mathlib.RingTheory.TensorProduct.Basic

/-! Tensor scalar actions and contraction against a rational
coordinate functional. -/

noncomputable section

open scoped TensorProduct

namespace GlobalTheory.PD

variable {k F V W : Type*} [Field k] [Field F] [Algebra k F]
  [AddCommGroup V] [Module k V] [Module F V] [IsScalarTower k F V]
  [AddCommGroup W] [Module k W] [Module F W] [IsScalarTower k F W]

/-- Each factor acts by scalar multiplication on its tensor factor. -/
def tensorScalarAction : F ⊗[k] F →ₐ[k] Module.End k (V ⊗[k] W) :=
  GaloisForLFunctions.HTGeometry.ABHN.tensorProductEndAlgHom.comp
    (Algebra.TensorProduct.map (Algebra.lsmul k k V) (Algebra.lsmul k k W))

theorem tensorScalarAction_tmul (a b : F) (v : V) (w : W) :
    tensorScalarAction (a ⊗ₜ[k] b) (v ⊗ₜ[k] w) = (a • v) ⊗ₜ[k] (b • w) := by
  simp only [tensorScalarAction, AlgHom.comp_apply, Algebra.TensorProduct.map_tmul,
    GaloisForLFunctions.HTGeometry.ABHN.tensorProductEndAlgHom_tmul, TensorProduct.map_tmul]
  rfl

/-- Test both tensor factors by rational coordinate functionals. -/
def tensorCoordinates (φ : V →ₗ[F] F) (ψ : W →ₗ[F] F) : V ⊗[k] W →ₗ[k] F ⊗[k] F :=
  TensorProduct.map (φ.restrictScalars k) (ψ.restrictScalars k)

theorem tensorCoordinates_tmul (φ : V →ₗ[F] F) (ψ : W →ₗ[F] F) (v : V) (w : W) :
    tensorCoordinates (k := k) φ ψ (v ⊗ₜ[k] w) = φ v ⊗ₜ[k] ψ w :=
  TensorProduct.map_tmul _ _ _ _

theorem tensorCoordinates_action (φ : V →ₗ[F] F) (ψ : W →ₗ[F] F)
    (s : F ⊗[k] F) (t : V ⊗[k] W) :
    tensorCoordinates φ ψ (tensorScalarAction s t) = s * tensorCoordinates φ ψ t := by
  induction s using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, LinearMap.add_apply, add_mul, ha, hb]
  | tmul a b =>
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add v w hv hw => simp only [map_add, mul_add, hv, hw]
    | tmul v w =>
      simp only [tensorScalarAction_tmul, tensorCoordinates_tmul, map_smul, smul_eq_mul,
        Algebra.TensorProduct.tmul_mul_tmul]

/-- Contract the first tensor factor by a coordinate functional over
the projective coordinate field. -/
def tensorContraction (φ : V →ₗ[F] F) : V ⊗[k] W →ₗ[k] W :=
  TensorProduct.lift ((Algebra.lsmul k k W).toLinearMap.comp (φ.restrictScalars k))

theorem tensorContraction_tmul (φ : V →ₗ[F] F) (v : V) (w : W) :
    tensorContraction φ (v ⊗ₜ[k] w) = φ v • w := by
  rw [tensorContraction, TensorProduct.lift.tmul]
  rfl

/-- Contracting a scalar multiple restricts the scalar tensor to the diagonal. -/
theorem tensorContraction_action (φ : V →ₗ[F] F) (s : F ⊗[k] F) (t : V ⊗[k] W) :
    tensorContraction φ (tensorScalarAction s t) =
      Algebra.TensorProduct.lmul' k s • tensorContraction φ t := by
  induction s using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, LinearMap.add_apply, add_smul, ha, hb]
  | tmul a b =>
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add v w hv hw => simp only [map_add, smul_add, hv, hw]
    | tmul v w =>
      simp only [tensorScalarAction_tmul, tensorContraction_tmul, Algebra.TensorProduct.lmul'_apply_tmul,
        map_smul, smul_eq_mul, smul_smul]
      congr 1
      ac_rfl

theorem tensorCoordinates_lmul (φ : V →ₗ[F] F) (ψ : W →ₗ[F] F) (t : V ⊗[k] W) :
    Algebra.TensorProduct.lmul' k (tensorCoordinates φ ψ t) = ψ (tensorContraction φ t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add v w hv hw => simp only [map_add, hv, hw]
  | tmul v w =>
    rw [tensorCoordinates_tmul, tensorContraction_tmul, Algebra.TensorProduct.lmul'_apply_tmul,
      map_smul, smul_eq_mul]

end GlobalTheory.PD
