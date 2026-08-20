import GaloisForLFunctions.HTGeometry.ABHN.BrauerFoundations
import Mathlib.Algebra.Algebra.Subalgebra.Centralizer
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.MatrixAlgebra
import Mathlib.RingTheory.SimpleRing.Congr
import Mathlib.RingTheory.TensorProduct.Finite

/-!
# Scalar extension for Albert--Brauer--Hasse--Noether

For `A` central simple over `K` and a field extension `L/K`, the local Brauer map must be induced
by `L ⊗[K] A`.  Mathlib already constructs this algebra and proves finite dimensionality.  This
file proves its centrality, as well as the full central-simple upgrade for split matrix algebras.
The only remaining upgrade for arbitrary `A` is the central-simple tensor-product theorem.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped TensorProduct

universe u v w

/-- The raw `L`-algebra underlying scalar extension of a central simple `K`-algebra. -/
noncomputable def scalarExtensionAlg {K : Type u} {L : Type v} [Field K] [Field L]
    [Algebra K L] (A : CSA.{u, w} K) : AlgCat L :=
  AlgCat.of L (L ⊗[K] A.carrier)

/-- Canonical map from `A` into its raw scalar extension. -/
noncomputable def scalarExtensionMap {K : Type u} {L : Type v} [Field K] [Field L]
    [Algebra K L] (A : CSA.{u, w} K) : A.carrier →ₐ[K] L ⊗[K] A.carrier :=
  Algebra.TensorProduct.includeRight

/-- Scalar extension preserves finite dimensionality over the extended field. -/
theorem scalarExtensionAlg_finiteDimensional {K : Type u} {L : Type v} [Field K] [Field L]
    [Algebra K L] (A : CSA.{u, w} K) : FiniteDimensional L (L ⊗[K] A.carrier) := by
  infer_instance

/-- The canonical map into scalar extension is injective. -/
theorem scalarExtensionMap_injective {K : Type u} {L : Type v} [Field K] [Field L]
    [Algebra K L] (A : CSA.{u, w} K) : Function.Injective (scalarExtensionMap (L := L) A) := by
  apply Algebra.TensorProduct.includeRight_injective
  exact FaithfulSMul.algebraMap_injective K L

/-- Scalar extension of a central algebra remains central over the extended field. -/
theorem scalarExtensionAlg_isCentral {K : Type u} {L : Type v} [Field K] [Field L]
    [Algebra K L] (A : CSA.{u, w} K) : Algebra.IsCentral L (L ⊗[K] A.carrier) := by
  constructor
  intro z hz
  rw [Subalgebra.mem_center_iff] at hz
  rw [Algebra.mem_bot]
  have hz' : z ∈ Subalgebra.centralizer K
      (↑(Algebra.TensorProduct.includeRight : A.carrier →ₐ[K] L ⊗[K] A.carrier).range) := by
    rw [Subalgebra.mem_centralizer_iff]
    rintro g ⟨a, rfl⟩
    exact hz _
  rw [Subalgebra.centralizer_range_includeRight_eq_center_tensorProduct K L A.carrier] at hz'
  rcases hz' with ⟨x, hx⟩
  subst z
  clear hz
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul l a =>
      obtain ⟨k, hk⟩ := (Algebra.IsCentral.mem_center_iff K).mp a.prop
      refine ⟨l * algebraMap K L k, ?_⟩
      simpa [Algebra.TensorProduct.map_tmul, hk, Algebra.smul_def, mul_comm] using
        (TensorProduct.tmul_smul (R := K) (R' := K) (M := L) (N := A.carrier)
          k l (1 : A.carrier)).symm
  | add x y hx hy =>
      obtain ⟨lx, hx⟩ := hx
      obtain ⟨ly, hy⟩ := hy
      refine ⟨lx + ly, ?_⟩
      change algebraMap L (L ⊗[K] A.carrier) (lx + ly) = _
      rw [map_add, map_add, hx, hy]

/-- Base change of a split matrix algebra is simple.  The explicit equivalence is used below to
package its scalar extension as a central simple algebra. -/
theorem scalarExtension_matrix_isSimple {K : Type u} {L : Type v} [Field K] [Field L]
    [Algebra K L] (n : Type w) [Fintype n] [Nonempty n] [DecidableEq n] :
    IsSimpleRing (L ⊗[K] Matrix n n K) := by
  exact IsSimpleRing.of_ringEquiv (matrixEquivTensor n K L).toRingEquiv
    (inferInstance : IsSimpleRing (Matrix n n L))

/-- The standard base-change equivalence for a matrix algebra, promoted from a `K`-algebra
equivalence to an `L`-algebra equivalence. -/
noncomputable def scalarExtensionMatrixAlgEquiv {K : Type u} {L : Type v} [Field K] [Field L]
    [Algebra K L] (n : Type w) [Fintype n] [Nonempty n] [DecidableEq n] :
    (L ⊗[K] Matrix n n K) ≃ₐ[L] Matrix n n L where
  toFun := MatrixEquivTensor.toFunAlgHom n K L
  invFun := MatrixEquivTensor.invFun n K L
  left_inv := MatrixEquivTensor.left_inv n K L
  right_inv := MatrixEquivTensor.right_inv n K L
  map_mul' := map_mul (MatrixEquivTensor.toFunAlgHom n K L)
  map_add' := map_add (MatrixEquivTensor.toFunAlgHom n K L)
  commutes' l := by
    change MatrixEquivTensor.toFunAlgHom n K L (l ⊗ₜ (1 : Matrix n n K)) = _
    rw [MatrixEquivTensor.toFunAlgHom_apply, Algebra.algebraMap_eq_smul_one]
    simp

/-- The raw scalar extension of a split matrix representative, packaged as a central simple
`L`-algebra. -/
noncomputable def scalarExtensionMatrixFinScalarCSA (K L : Type u) [Field K] [Field L]
    [Algebra K L] (n : ℕ) [NeZero n] : CSA.{u, u} L where
  carrier := L ⊗[K] (matrixFinCSA (scalarCSA K) n).carrier
  isCentral := scalarExtensionAlg_isCentral (matrixFinCSA (scalarCSA K) n)
  isSimple := scalarExtension_matrix_isSimple (K := K) (L := L) (Fin n)
  fin_dim := scalarExtensionAlg_finiteDimensional (matrixFinCSA (scalarCSA K) n)

/-- Scalar extension carries every split matrix representative to the split class. -/
theorem brauerClass_scalarExtensionMatrixFinScalar_eq {K L : Type u} [Field K] [Field L]
    [Algebra K L] (n : ℕ) [NeZero n] :
    brauerClass (scalarExtensionMatrixFinScalarCSA K L n) = brauerSplitClass L := by
  calc
    brauerClass (scalarExtensionMatrixFinScalarCSA K L n) =
      brauerClass (matrixFinCSA (scalarCSA L) n) :=
      brauerClass_eq_of_algEquiv _ _
        (scalarExtensionMatrixAlgEquiv (K := K) (L := L) (Fin n))
    _ = brauerSplitClass L := brauerClass_matrixFinCSA_scalar_eq n

end GaloisForLFunctions.HTGeometry.ABHN
