import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.RationalTensorCoordinates
import Mathlib.Algebra.Module.Submodule.Bilinear

/-! Integral dual families give integral coordinates for the tensor
lattice, and their reconstruction formula holds over the tensor ring. -/

noncomputable section

open scoped TensorProduct

namespace GlobalTheory.PD

variable {k F V W : Type*} [Field k] [Field F] [Algebra k F]
  [AddCommGroup V] [Module k V] [Module F V] [IsScalarTower k F V]
  [AddCommGroup W] [Module k W] [Module F W] [IsScalarTower k F W]
  {A B : Subalgebra k F} {P : Submodule k V} {Q : Submodule k W}

/-- The tensor ring of the two chart algebras inside the ambient tensor algebra. -/
def tensorChartRing (A B : Subalgebra k F) : Subalgebra k (F ⊗[k] F) :=
  (Algebra.TensorProduct.map A.val B.val).range

/-- The lattice spanned by tensors of regular forms on the two charts. -/
def tensorChartLattice (P : Submodule k V) (Q : Submodule k W) : Submodule k (V ⊗[k] W) :=
  Submodule.map₂ (TensorProduct.mk k V W) P Q

theorem tensorCoordinates_mem_chartRing {φ : V →ₗ[F] F} {ψ : W →ₗ[F] F}
    (hφ : ∀ v ∈ P, φ v ∈ A) (hψ : ∀ w ∈ Q, ψ w ∈ B)
    {t : V ⊗[k] W} (ht : t ∈ tensorChartLattice P Q) :
    tensorCoordinates φ ψ t ∈ tensorChartRing A B := by
  have hle : tensorChartLattice P Q ≤
      (tensorChartRing A B).toSubmodule.comap (tensorCoordinates φ ψ) :=
    Submodule.map₂_le.mpr fun v hv w hw => by
      change tensorCoordinates φ ψ (v ⊗ₜ[k] w) ∈ (Algebra.TensorProduct.map A.val B.val).range
      let a : A := ⟨φ v, hφ v hv⟩
      let b : B := ⟨ψ w, hψ w hw⟩
      refine ⟨a ⊗ₜ[k] b, ?_⟩
      change Algebra.TensorProduct.map A.val B.val (a ⊗ₜ[k] b) =
        tensorCoordinates φ ψ (v ⊗ₜ[k] w)
      rw [Algebra.TensorProduct.map_tmul, tensorCoordinates_tmul]
      rfl
  exact hle ht

theorem tensorScalarAction_mem_chartLattice
    (hP : ∀ a ∈ A, ∀ v ∈ P, a • v ∈ P) (hQ : ∀ b ∈ B, ∀ w ∈ Q, b • w ∈ Q)
    {s : F ⊗[k] F} (hs : s ∈ tensorChartRing A B) {t : V ⊗[k] W}
    (ht : t ∈ tensorChartLattice P Q) :
    tensorScalarAction s t ∈ tensorChartLattice P Q := by
  obtain ⟨c, rfl⟩ := hs
  induction c using TensorProduct.induction_on with
  | zero =>
    rw [map_zero, map_zero, LinearMap.zero_apply]
    exact zero_mem _
  | add a b ha hb =>
    rw [map_add, map_add, LinearMap.add_apply]
    exact add_mem ha hb
  | tmul a b =>
    let f : Module.End k (V ⊗[k] W) :=
      tensorScalarAction (Algebra.TensorProduct.map A.val B.val (a ⊗ₜ[k] b))
    have hle : tensorChartLattice P Q ≤ (tensorChartLattice P Q).comap f := by
      refine Submodule.map₂_le.mpr fun v hv w hw => ?_
      change tensorScalarAction (Algebra.TensorProduct.map A.val B.val (a ⊗ₜ[k] b)) (v ⊗ₜ[k] w) ∈
        tensorChartLattice P Q
      rw [Algebra.TensorProduct.map_tmul, tensorScalarAction_tmul]
      exact Submodule.apply_mem_map₂ _ (hP _ a.property _ hv) (hQ _ b.property _ hw)
    exact hle ht

/-- The tensor of two dual families reconstructs every rational tensor. -/
theorem tensorCoordinates_sum {ι κ : Type*} [Fintype ι] [Fintype κ]
    (v : ι → V) (w : κ → W) (φ : ι → V →ₗ[F] F) (ψ : κ → W →ₗ[F] F)
    (hv : ∀ a, a = ∑ i, φ i a • v i) (hw : ∀ b, b = ∑ j, ψ j b • w j)
    (t : V ⊗[k] W) :
    t = ∑ i, ∑ j, tensorScalarAction (tensorCoordinates (φ i) (ψ j) t) (v i ⊗ₜ[k] w j) := by
  let L : V ⊗[k] W →ₗ[k] V ⊗[k] W :=
    ∑ i, ∑ j, (LinearMap.applyₗ (v i ⊗ₜ[k] w j)) ∘ₗ
      tensorScalarAction.toLinearMap ∘ₗ tensorCoordinates (φ i) (ψ j)
  have happly (u : V ⊗[k] W) (f : Module.End k (V ⊗[k] W)) :
      LinearMap.applyₗ u f = f u := rfl
  have hL : LinearMap.id = L := by
    refine TensorProduct.ext' fun a b => ?_
    simp only [L, LinearMap.id_apply, LinearMap.sum_apply, LinearMap.comp_apply,
      happly, AlgHom.toLinearMap_apply, tensorCoordinates_tmul, tensorScalarAction_tmul]
    conv_lhs => rw [hv a, hw b]
    rw [TensorProduct.sum_tmul]
    simp only [TensorProduct.tmul_sum]
  simpa only [L, LinearMap.id_apply, LinearMap.sum_apply, LinearMap.comp_apply,
    happly, AlgHom.toLinearMap_apply] using LinearMap.congr_fun hL t

end GlobalTheory.PD
