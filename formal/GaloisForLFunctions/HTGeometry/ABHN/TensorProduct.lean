import GaloisForLFunctions.HTGeometry.ABHN.BrauerFoundations
import Mathlib.Algebra.Algebra.Subalgebra.Centralizer
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.MatrixAlgebra
import Mathlib.RingTheory.SimpleRing.Congr
import Mathlib.RingTheory.TensorProduct.Finite

/-!
# Tensor products of central simple algebras

Tensor-product addition on the Brauer group starts with `A ⊗[K] B`.  This file proves the two
elementary closed parts of that construction: finite dimensionality and centrality.  The remaining
property, simplicity of the tensor product, is the central-simple tensor-product theorem; it is
the algebraic core still absent from Mathlib.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped TensorProduct

universe u v w

/-- The raw tensor-product algebra underlying the future product of two Brauer classes. -/
noncomputable def tensorProductAlg {K : Type u} [Field K] (A : CSA.{u, v} K)
    (B : CSA.{u, w} K) : AlgCat K :=
  AlgCat.of K (A.carrier ⊗[K] B.carrier)

/-- Tensor products of finite-dimensional central simple algebras are finite-dimensional. -/
theorem tensorProductAlg_finiteDimensional {K : Type u} [Field K] (A : CSA.{u, v} K)
    (B : CSA.{u, w} K) : FiniteDimensional K (A.carrier ⊗[K] B.carrier) := by
  infer_instance

/-- Tensor products of central algebras over a field are central. -/
theorem tensorProductAlg_isCentral {K : Type u} [Field K] (A : CSA.{u, v} K)
    (B : CSA.{u, w} K) : Algebra.IsCentral K (A.carrier ⊗[K] B.carrier) := by
  constructor
  intro z hz
  rw [Subalgebra.mem_center_iff] at hz
  rw [Algebra.mem_bot]
  have hz' : z ∈ Subalgebra.centralizer K
      (↑(Algebra.TensorProduct.includeRight : B.carrier →ₐ[K] A.carrier ⊗[K] B.carrier).range) := by
    rw [Subalgebra.mem_centralizer_iff]
    rintro g ⟨b, rfl⟩
    exact hz _
  rw [Subalgebra.centralizer_range_includeRight_eq_center_tensorProduct K A.carrier B.carrier] at hz'
  rcases hz' with ⟨x, hx⟩
  have map_centerRight_eq_includeLeft : ∀ x : A.carrier ⊗[K] Subalgebra.center K B.carrier,
      ∃ a : A.carrier,
        Algebra.TensorProduct.map (AlgHom.id K A.carrier) (Subalgebra.center K B.carrier).val x =
          (Algebra.TensorProduct.includeLeft : A.carrier →ₐ[K] A.carrier ⊗[K] B.carrier) a := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul a b =>
        obtain ⟨k, hk⟩ := (Algebra.IsCentral.mem_center_iff K).mp b.prop
        refine ⟨algebraMap K A.carrier k * a, ?_⟩
        simpa [Algebra.TensorProduct.map_tmul, hk, Algebra.smul_def] using
          (TensorProduct.smul_tmul (R := K) (R' := K) k a (1 : B.carrier)).symm
    | add x y hx hy =>
        obtain ⟨ax, hx⟩ := hx
        obtain ⟨ay, hy⟩ := hy
        refine ⟨ax + ay, ?_⟩
        rw [map_add, hx, hy, map_add]
  obtain ⟨a, ha⟩ := map_centerRight_eq_includeLeft x
  have hcentral : ∀ b : A.carrier ⊗[K] B.carrier,
      b * Algebra.TensorProduct.map (AlgHom.id K A.carrier) (Subalgebra.center K B.carrier).val x =
        Algebra.TensorProduct.map (AlgHom.id K A.carrier) (Subalgebra.center K B.carrier).val x * b := by
    intro b
    change b * (Algebra.TensorProduct.map (AlgHom.id K A.carrier)
      (Subalgebra.center K B.carrier).val).toRingHom x =
      (Algebra.TensorProduct.map (AlgHom.id K A.carrier)
        (Subalgebra.center K B.carrier).val).toRingHom x * b
    rw [hx]
    exact hz b
  have ha' : a ∈ Subalgebra.center K A.carrier := by
    rw [Subalgebra.mem_center_iff]
    intro a'
    apply Algebra.TensorProduct.includeLeft_injective (S := K) (A := A.carrier) (B := B.carrier)
      (FaithfulSMul.algebraMap_injective K B.carrier)
    change (a' * a) ⊗ₜ[K] (1 : B.carrier) = (a * a') ⊗ₜ[K] (1 : B.carrier)
    simpa [ha] using hcentral
      ((Algebra.TensorProduct.includeLeft : A.carrier →ₐ[K] A.carrier ⊗[K] B.carrier) a')
  obtain ⟨k, hk⟩ := (Algebra.IsCentral.mem_center_iff K).mp ha'
  refine ⟨k, ?_⟩
  calc
    algebraMap K (A.carrier ⊗[K] B.carrier) k =
        (Algebra.TensorProduct.includeLeft : A.carrier →ₐ[K] A.carrier ⊗[K] B.carrier)
          (algebraMap K A.carrier k) := by simp
    _ = (Algebra.TensorProduct.includeLeft : A.carrier →ₐ[K] A.carrier ⊗[K] B.carrier) a :=
      congrArg _ hk.symm
    _ = Algebra.TensorProduct.map (AlgHom.id K A.carrier) (Subalgebra.center K B.carrier).val x :=
      ha.symm
    _ = z := hx

/-- Tensoring a central simple algebra with a split matrix algebra is simple. -/
theorem tensorProduct_rightMatrix_isSimple {K : Type u} [Field K] (A : CSA.{u, u} K)
    (n : Type) [Fintype n] [Nonempty n] [DecidableEq n] :
    IsSimpleRing (A.carrier ⊗[K] Matrix n n K) := by
  exact IsSimpleRing.of_ringEquiv (matrixEquivTensor n K A.carrier).toRingEquiv
    (inferInstance : IsSimpleRing (Matrix n n A.carrier))

/-- Tensoring with a split finite matrix algebra remains a central simple algebra. -/
noncomputable def tensorProductRightMatrixFinCSA {K : Type u} [Field K] (A : CSA.{u, u} K)
    (n : ℕ) [NeZero n] : CSA.{u, u} K where
  carrier := A.carrier ⊗[K] Matrix (Fin n) (Fin n) K
  isCentral := tensorProductAlg_isCentral A (matrixFinCSA (scalarCSA K) n)
  isSimple := tensorProduct_rightMatrix_isSimple A (Fin n)
  fin_dim := by
    letI : Module.Finite K (A.carrier ⊗[K] Matrix (Fin n) (Fin n) K) :=
      Module.Finite.tensorProduct K A.carrier (Matrix (Fin n) (Fin n) K)
    exact (show Module.Finite K (A.carrier ⊗[K] Matrix (Fin n) (Fin n) K) from inferInstance)

/-- Tensoring by a split matrix representative preserves a Brauer class.  This is the
identity-law component required by tensor-product addition. -/
theorem brauerClass_tensorProductRightMatrixFinCSA_eq {K : Type u} [Field K]
    (A : CSA.{u, u} K) (n : ℕ) [NeZero n] :
    brauerClass (tensorProductRightMatrixFinCSA A n) = brauerClass A := by
  calc
    brauerClass (tensorProductRightMatrixFinCSA A n) = brauerClass (matrixFinCSA A n) :=
      brauerClass_eq_of_algEquiv _ _ (matrixEquivTensor (Fin n) K A.carrier).symm
    _ = brauerClass A := brauerClass_matrixFinCSA_eq A n

end GaloisForLFunctions.HTGeometry.ABHN
