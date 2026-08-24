import GaloisForLFunctions.HTGeometry.ABHN.BrauerFoundations
import Mathlib.Algebra.Central.Basic
import Mathlib.Algebra.Central.Matrix
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.SimpleModule.WedderburnArtin

/-!
# Central division representatives of Brauer classes

Wedderburn--Artin supplies a finite division-ring factor for every finite-dimensional simple
algebra, but its general statement does not retain centrality over the base field.  Centrality is
reflected by a nonempty matrix algebra: a central coefficient defines a scalar matrix, and a
central scalar matrix over the base has a base-scalar diagonal entry.  Consequently every central
simple algebra, and hence every Brauer class, has a finite-dimensional central division-algebra
representative.

For a nonarchimedean local field this reduces local Brauer exhaustion to the classical structural
core: prove that each finite-dimensional central division algebra contains an unramified maximal
subfield, which then splits it.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

noncomputable section

universe u v

/-- Centrality of a nonempty matrix algebra reflects to its coefficient algebra. -/
theorem isCentral_of_matrix
    (K : Type u) [Field K] (D : Type u) [Ring D] [Algebra K D]
    (ι : Type v) [Fintype ι] [DecidableEq ι] [Nonempty ι]
    [Algebra.IsCentral K (Matrix ι ι D)] : Algebra.IsCentral K D := by
  constructor
  intro z hz
  have hzM : Matrix.scalar ι z ∈ Subalgebra.center K (Matrix ι ι D) := by
    rw [Matrix.subalgebraCenter_eq_scalarAlgHom_map]
    exact ⟨z, hz, rfl⟩
  have hzbot := Algebra.IsCentral.out hzM
  rw [Algebra.mem_bot] at hzbot
  obtain ⟨k, hk⟩ := hzbot
  rw [Algebra.mem_bot]
  refine ⟨k, ?_⟩
  let i : ι := Classical.choice inferInstance
  have hii := congrFun (congrFun hk i) i
  simpa [Matrix.algebraMap_matrix_apply] using hii

/-- Every finite-dimensional central simple algebra is a matrix algebra over a finite-dimensional
central division algebra. -/
theorem csa_exists_algEquiv_matrix_centralDivisionRing
    (K : Type u) [Field K] (A : CSA.{u, u} K) :
    ∃ (n : ℕ) (_ : NeZero n) (D : Type u) (_ : DivisionRing D) (_ : Algebra K D)
      (_ : Module.Finite K D) (_ : Algebra.IsCentral K D),
      Nonempty (A.carrier ≃ₐ[K] Matrix (Fin n) (Fin n) D) := by
  letI : IsArtinianRing A.carrier := IsArtinianRing.of_finite K A.carrier
  obtain ⟨n, hn, D, hD, aD, finD, ⟨e⟩⟩ :=
    IsSimpleRing.exists_algEquiv_matrix_divisionRing_finite K A.carrier
  letI : Algebra.IsCentral K (Matrix (Fin n) (Fin n) D) :=
    Algebra.IsCentral.of_algEquiv K A.carrier _ e
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero (NeZero.ne n))
  let hcentral : Algebra.IsCentral K D := isCentral_of_matrix K D (Fin n)
  exact ⟨n, hn, D, hD, aD, finD, hcentral, ⟨e⟩⟩

/-- A finite-dimensional central division algebra packaged as a central simple algebra. -/
noncomputable def centralDivisionCSA
    (K D : Type u) [Field K] [DivisionRing D] [Algebra K D]
    [Module.Finite K D] [Algebra.IsCentral K D] : CSA.{u, u} K where
  carrier := D
  isCentral := inferInstance
  isSimple := inferInstance
  fin_dim := by infer_instance

/-- Wedderburn--Artin reduction preserves the represented Brauer class. -/
theorem csa_exists_brauerClass_eq_centralDivision
    (K : Type u) [Field K] (A : CSA.{u, u} K) :
    ∃ (n : ℕ) (_ : NeZero n) (D : Type u) (_ : DivisionRing D) (_ : Algebra K D)
      (_ : Module.Finite K D) (_ : Algebra.IsCentral K D),
      Nonempty (A.carrier ≃ₐ[K] Matrix (Fin n) (Fin n) D) ∧
        brauerClass A = brauerClass (centralDivisionCSA K D) := by
  obtain ⟨n, hn, D, hD, aD, finD, hcentral, ⟨e⟩⟩ :=
    csa_exists_algEquiv_matrix_centralDivisionRing K A
  letI : NeZero n := hn
  have hclass : brauerClass A = brauerClass (centralDivisionCSA K D) :=
    (brauerClass_eq_of_algEquiv A (matrixFinCSA (centralDivisionCSA K D) n) e).trans
      (brauerClass_matrixFinCSA_eq (centralDivisionCSA K D) n)
  exact ⟨n, hn, D, hD, aD, finD, hcentral, ⟨e⟩, hclass⟩

/-- Every Brauer-group element has a finite-dimensional central division-algebra representative.
This is the exact algebraic reduction needed before the local unramified-splitting theorem. -/
theorem brauerGroup_exists_centralDivisionRepresentative
    (K : Type u) [Field K] (x : BrauerGroup K) :
    ∃ (D : Type u) (_ : DivisionRing D) (_ : Algebra K D)
      (_ : Module.Finite K D) (_ : Algebra.IsCentral K D),
      x = brauerClass (centralDivisionCSA K D) := by
  refine Quotient.inductionOn x ?_
  intro A
  obtain ⟨n, hn, D, hD, aD, finD, hcentral, hmatrix, hclass⟩ :=
    csa_exists_brauerClass_eq_centralDivision K A
  exact ⟨D, hD, aD, finD, hcentral, hclass⟩

end

end GaloisForLFunctions.HTGeometry.ABHN
