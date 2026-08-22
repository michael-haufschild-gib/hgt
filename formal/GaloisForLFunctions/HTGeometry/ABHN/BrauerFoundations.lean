import Mathlib.Algebra.BrauerGroup.Defs
import Mathlib.Algebra.Central.Basic
import Mathlib.Algebra.Central.Matrix
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.RingTheory.SimpleRing.Congr
import Mathlib.RingTheory.SimpleRing.Matrix

/-!
# Foundations for Albert--Brauer--Hasse--Noether

Mathlib's `BrauerGroup` is currently a quotient of central simple algebras.  This file supplies
canonical central-simple representatives and the matrix stabilization relation built into that
quotient.  It is the first algebraic layer needed before tensor-product multiplication, scalar
extension, local invariants, and the global ABHN sequence can be constructed.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open MulOpposite

universe u v w

/-- Centrality transports along an algebra equivalence, also when the two algebra carriers live
in different universes. -/
theorem isCentral_of_algEquiv {K : Type u} [CommSemiring K]
    (D : Type v) [Semiring D] [Algebra K D] [Algebra.IsCentral K D]
    (D' : Type w) [Semiring D'] [Algebra K D'] (e : D ≃ₐ[K] D') : Algebra.IsCentral K D' where
  out x hx :=
    have ⟨k, hk⟩ := (Algebra.IsCentral.out (K := K) (D := D))
      ((MulEquivClass.apply_mem_center_iff e.symm).mpr hx)
    ⟨k, by simpa [Algebra.ofId] using congr(e $hk)⟩

/-- Transport a central simple algebra along an algebra equivalence. -/
noncomputable def csaOfAlgEquiv {K : Type u} [Field K] (A : CSA.{u, v} K)
    (B : Type w) [Ring B] [Algebra K B] (e : A.carrier ≃ₐ[K] B) : CSA.{u, w} K where
  carrier := B
  isCentral := isCentral_of_algEquiv A.carrier B e
  isSimple := IsSimpleRing.of_ringEquiv e.toRingEquiv inferInstance
  fin_dim := LinearEquiv.finiteDimensional e.toLinearEquiv

/-- The split degree-one central simple algebra over a field. -/
noncomputable def scalarCSA (K : Type u) [Field K] : CSA.{u, u} K where
  carrier := K
  isCentral := Algebra.IsCentral.self K
  isSimple := DivisionRing.isSimpleRing K
  fin_dim := FiniteDimensional.finiteDimensional_self K

/-- The opposite central simple algebra.  This will provide Brauer inverses after tensor-product
closure and the splitness of `A ⊗ Aᵐᵒᵖ` are formalized. -/
noncomputable def oppositeCSA {K : Type u} [Field K] (A : CSA.{u, v} K) : CSA.{u, v} K where
  carrier := A.carrierᵐᵒᵖ
  isCentral := inferInstance
  isSimple := inferInstance
  fin_dim := LinearEquiv.finiteDimensional (opLinearEquiv K)

/-- Matrix algebras over central simple algebras remain central simple. -/
noncomputable def matrixCSA {K : Type u} [Field K] (A : CSA.{u, v} K)
    (ι : Type w) [Fintype ι] [Nonempty ι] [DecidableEq ι] : CSA.{u, max v w} K where
  carrier := Matrix ι ι A.carrier
  isCentral := inferInstance
  isSimple := inferInstance
  fin_dim := inferInstance

/-- The `n × n` matrix representative of a central simple algebra. -/
noncomputable def matrixFinCSA {K : Type u} [Field K] (A : CSA.{u, v} K)
    (n : ℕ) [NeZero n] : CSA.{u, v} K :=
  matrixCSA A (Fin n)

/-- A one-by-one matrix algebra is canonically its coefficient algebra. -/
noncomputable def oneByOneMatrixAlgEquiv (K : Type u) [CommRing K]
    (A : Type v) [Ring A] [Algebra K A] :
    Matrix (Fin 1) (Fin 1) A ≃ₐ[K] A where
  toFun M := M 0 0
  invFun a := fun _ _ => a
  left_inv M := by
    ext i j
    fin_cases i
    fin_cases j
    rfl
  right_inv a := rfl
  map_mul' M N := by
    simp [Matrix.mul_apply]
  map_add' M N := rfl
  commutes' r := rfl

/-- Matrix stabilization realizes the defining Brauer-equivalence relation. -/
theorem isBrauerEquivalent_matrixFinCSA {K : Type u} [Field K] (A : CSA.{u, v} K)
    (n : ℕ) [NeZero n] : IsBrauerEquivalent A (matrixFinCSA A n) := by
  refine ⟨n, 1, NeZero.ne n, one_ne_zero, ?_⟩
  exact ⟨(oneByOneMatrixAlgEquiv K (Matrix (Fin n) (Fin n) A.carrier)).symm⟩

/-- The class of a central simple algebra in Mathlib's quotient presentation of the Brauer group. -/
noncomputable def brauerClass {K : Type u} [Field K] (A : CSA.{u, v} K) : BrauerGroup K :=
  Quotient.mk _ A

/-- The split class, the future zero of the Brauer group once its additive structure is built. -/
noncomputable def brauerSplitClass (K : Type u) [Field K] : BrauerGroup K :=
  brauerClass (scalarCSA K)

/-- Matrix stabilization does not change a Brauer class. -/
theorem brauerClass_matrixFinCSA_eq {K : Type u} [Field K] (A : CSA.{u, v} K)
    (n : ℕ) [NeZero n] : brauerClass (matrixFinCSA A n) = brauerClass A := by
  exact Quotient.sound (isBrauerEquivalent_matrixFinCSA A n).symm

/-- Taking the opposite algebra twice preserves its Brauer-equivalence class. -/
theorem isBrauerEquivalent_opposite_oppositeCSA {K : Type u} [Field K] (A : CSA.{u, v} K) :
    IsBrauerEquivalent A (oppositeCSA (oppositeCSA A)) := by
  refine ⟨1, 1, one_ne_zero, one_ne_zero, ?_⟩
  exact ⟨(AlgEquiv.opOp K A.carrier).mapMatrix⟩

/-- Double opposite is neutral already at the quotient level. -/
theorem brauerClass_opposite_oppositeCSA_eq {K : Type u} [Field K] (A : CSA.{u, v} K) :
    brauerClass (oppositeCSA (oppositeCSA A)) = brauerClass A := by
  exact Quotient.sound (isBrauerEquivalent_opposite_oppositeCSA A).symm

/-- Isomorphic central simple algebras define the same Brauer-equivalence class. -/
theorem isBrauerEquivalent_of_algEquiv {K : Type u} [Field K]
    (A B : CSA.{u, v} K) (e : A.carrier ≃ₐ[K] B.carrier) : IsBrauerEquivalent A B := by
  refine ⟨1, 1, one_ne_zero, one_ne_zero, ?_⟩
  exact ⟨e.mapMatrix⟩

/-- Algebra isomorphism induces equality in the Brauer quotient. -/
theorem brauerClass_eq_of_algEquiv {K : Type u} [Field K]
    (A B : CSA.{u, v} K) (e : A.carrier ≃ₐ[K] B.carrier) : brauerClass A = brauerClass B := by
  exact Quotient.sound (isBrauerEquivalent_of_algEquiv A B e)

/-- Every finite matrix algebra over a field represents the split Brauer class. -/
theorem brauerClass_matrixFinCSA_scalar_eq {K : Type u} [Field K]
    (n : ℕ) [NeZero n] : brauerClass (matrixFinCSA (scalarCSA K) n) = brauerSplitClass K := by
  simpa [brauerSplitClass] using brauerClass_matrixFinCSA_eq (scalarCSA K) n

end GaloisForLFunctions.HTGeometry.ABHN
