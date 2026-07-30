import GaloisForLFunctions.HTGeometry.RelationalHistoryExternalTimeAmbiguityClassification
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Universal finite-history similarity gauge

Every finite operational history has an exact representation gauge.  Change
the initial state by one linear equivalence, conjugate every labelled
instrument by that same equivalence, and precompose every terminal report by
the inverse equivalence.  Every reported scalar for every finite ordered word
is unchanged.

This is cardinality-free in both label and reporter families and imposes no
bound on history length.  It identifies the exact obstacle that an
operational clock-reconstruction theorem must remove: histories alone
determine a realization only modulo simultaneous similarity.
-/

namespace HTGeometry

noncomputable section

open scoped Matrix
open scoped ComplexOrder

universe u v

variable {𝕜 : Type u} {V : Type v}
  [Field 𝕜] [AddCommGroup V] [Module 𝕜 V]

/-- Apply a finite ordered word of linear instruments to an initial state. -/
def applyLinearHistory :
    List (V →ₗ[𝕜] V) → V → V
  | [], x => x
  | gate :: gates, x => applyLinearHistory gates (gate x)

/-- Change every instrument representation by one common similarity. -/
def similarityTransformInstrument
    (S : V ≃ₗ[𝕜] V) (gate : V →ₗ[𝕜] V) :
    V →ₗ[𝕜] V :=
  S.toLinearMap.comp (gate.comp S.symm.toLinearMap)

@[simp] theorem similarityTransformInstrument_apply
    (S : V ≃ₗ[𝕜] V) (gate : V →ₗ[𝕜] V) (x : V) :
    similarityTransformInstrument S gate (S x) =
      S (gate x) := by
  simp [similarityTransformInstrument, LinearMap.comp_apply]

/-- A complete finite instrument history is equivariant under simultaneous
similarity of its state and every labelled instrument. -/
theorem applyLinearHistory_similarity
    (S : V ≃ₗ[𝕜] V)
    (gates : List (V →ₗ[𝕜] V)) (x : V) :
    applyLinearHistory
        (gates.map (similarityTransformInstrument S)) (S x) =
      S (applyLinearHistory gates x) := by
  induction gates generalizing x with
  | nil => rfl
  | cons gate gates ih =>
      simp only [List.map_cons, applyLinearHistory]
      rw [similarityTransformInstrument_apply, ih]

/-- **Universal operational-history similarity gauge.** Simultaneously
transforming initial state, every labelled instrument, and every terminal
linear report by one invertible similarity preserves every scalar report of
every finite ordered history exactly. -/
theorem allFiniteLinearHistoryReports_similarity_invariant
    (S : V ≃ₗ[𝕜] V)
    (report : V →ₗ[𝕜] 𝕜)
    (gates : List (V →ₗ[𝕜] V)) (x : V) :
    (report.comp S.symm.toLinearMap)
        (applyLinearHistory
          (gates.map (similarityTransformInstrument S)) (S x)) =
      report (applyLinearHistory gates x) := by
  rw [applyLinearHistory_similarity]
  simp [LinearMap.comp_apply]

/-- The gauge theorem holds simultaneously for every report and every finite
labelled word. -/
theorem allReports_allFiniteLinearHistories_similarity_invariant
    {Reporter Label : Type*}
    (S : V ≃ₗ[𝕜] V)
    (report : Reporter → (V →ₗ[𝕜] 𝕜))
    (instrument : Label → (V →ₗ[𝕜] V))
    (word : List Label) (x : V) (r : Reporter) :
    ((report r).comp S.symm.toLinearMap)
        (applyLinearHistory
          (word.map fun label =>
            similarityTransformInstrument S (instrument label))
          (S x)) =
      report r
        (applyLinearHistory (word.map instrument) x) := by
  simpa only [List.map_map, Function.comp_apply] using!
    allFiniteLinearHistoryReports_similarity_invariant
      S (report r) (word.map instrument) x

section TransposeWitness

abbrev QubitMatrix := Matrix (Fin 2) (Fin 2) ℂ

/-- Global matrix transposition is an involutive complex-linear change of
operator-space representation. -/
abbrev qubitTransposeLinearEquiv :
    QubitMatrix ≃ₗ[ℂ] QubitMatrix :=
  Matrix.transposeLinearEquiv (Fin 2) (Fin 2) ℂ ℂ

/-- In dimension two, global transposition is not an algebra automorphism.
It therefore cannot be one of the inner algebra automorphisms that represent
ordinary unitary changes of quantum frame. -/
theorem qubitTranspose_not_multiplicative :
    ¬ ∀ A B : QubitMatrix,
      qubitTransposeLinearEquiv (A * B) =
        qubitTransposeLinearEquiv A *
          qubitTransposeLinearEquiv B := by
  intro h
  let A : QubitMatrix :=
    Matrix.single (0 : Fin 2) (1 : Fin 2) 1
  let B : QubitMatrix :=
    Matrix.single (1 : Fin 2) (0 : Fin 2) 1
  have hab := h A B
  have hentry := congr_fun (congr_fun hab (0 : Fin 2)) (0 : Fin 2)
  simp [A, B, qubitTransposeLinearEquiv, Matrix.mul_apply] at hentry

end TransposeWitness

section PhysicalTranspose

variable {n : Type v} [Fintype n]
variable {κ : Type*} [Fintype κ]

/-- Global transposition preserves finite Kraus form.  A completely positive
instrument represented by Kraus matrices `K i` is transformed into another
Kraus representation, with matrices obtained by entrywise conjugation. -/
theorem transpose_finiteKrausSum
    (K : κ → Matrix n n ℂ) (X : Matrix n n ℂ) :
    (∑ i, K i * X * (K i)ᴴ)ᵀ =
      ∑ i, (K i).map star * Xᵀ * ((K i).map star)ᴴ := by
  simp only [Matrix.transpose_sum, Matrix.transpose_mul,
    Matrix.conjTranspose_transpose]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Matrix.mul_assoc]
  congr 1
  ext a b
  simp

/-- Born reports are exactly invariant when both effect and state are
globally transposed. -/
theorem trace_transpose_mul_transpose
    (E X : Matrix n n ℂ) :
    Matrix.trace (Eᵀ * Xᵀ) = Matrix.trace (E * X) := by
  exact Matrix.trace_transpose_mul E X

/-- Transposition preserves the defining positive-semidefinite and
unit-trace conditions of a finite-dimensional density matrix. -/
theorem transpose_preserves_densityConditions
    (X : Matrix n n ℂ)
    (hX : X.PosSemidef ∧ Matrix.trace X = 1) :
    Xᵀ.PosSemidef ∧ Matrix.trace Xᵀ = 1 :=
  ⟨hX.1.transpose, by simpa using hX.2⟩

omit [Fintype n] in
/-- Transposition preserves the defining positive-semidefinite interval
conditions `0 ≤ E ≤ 1` of a finite-dimensional POVM effect. -/
theorem transpose_preserves_effectConditions
    [DecidableEq n]
    (E : Matrix n n ℂ)
    (hE : E.PosSemidef ∧ (1 - E).PosSemidef) :
    Eᵀ.PosSemidef ∧ (1 - Eᵀ).PosSemidef := by
  refine ⟨hE.1.transpose, ?_⟩
  simpa using hE.2.transpose

end PhysicalTranspose

end

end HTGeometry
