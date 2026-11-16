import GaloisForLFunctions.HTGeometry.Quantum.PositiveConstraintSupport
import GaloisForLFunctions.HTGeometry.Arxiv2510ReducedDensityMatrixApplications

/-!
# Coordinate embeddings of quantum states

An injection of basis labels induces a trace-preserving positive embedding of
states. Its image consists exactly of states supported on the corresponding
coordinate projection, and is therefore an exposed face.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry.Quantum

open Matrix _root_.HTGeometry.ConstraintRelativity
open scoped ComplexOrder

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- The isometric matrix of a basis-label injection. -/
def coordinateEmbedding (e : ι ↪ κ) : Matrix κ ι ℂ :=
  fun x a => if x = e a then 1 else 0

omit [Fintype ι] in
theorem coordinateEmbedding_isometry (e : ι ↪ κ) :
    (coordinateEmbedding e)ᴴ * coordinateEmbedding e = 1 := by
  ext a b
  simp [coordinateEmbedding, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.one_apply, e.injective.eq_iff, eq_comm]

/-- The projection onto the embedded coordinate sector. -/
def coordinateProjection (e : ι ↪ κ) : Matrix κ κ ℂ :=
  coordinateEmbedding e * (coordinateEmbedding e)ᴴ

/-- The sector projection retains exactly the basis labels in the image. -/
theorem coordinateProjection_eq_diagonal (e : ι ↪ κ) :
    coordinateProjection e = Matrix.diagonal
      (fun x => if x ∈ Set.range e then (1 : ℂ) else 0) := by
  classical
  ext x y
  by_cases hx : x ∈ Set.range e
  · obtain ⟨a, rfl⟩ := hx
    rw [coordinateProjection, Matrix.mul_apply, Finset.sum_eq_single a]
    · by_cases hy : y = e a
      · subst y
        simp [coordinateEmbedding, Matrix.conjTranspose_apply, Matrix.diagonal_apply]
      · simp [coordinateEmbedding, Matrix.conjTranspose_apply, Matrix.diagonal_apply,
          hy, Ne.symm hy]
    · intro b _ hba
      have hab : e a ≠ e b := fun h => hba (e.injective h).symm
      simp only [coordinateEmbedding, if_neg hab, zero_mul]
    · simp
  · have hx' : ∀ a, x ≠ e a := fun a h => hx ⟨a, h.symm⟩
    simp only [coordinateProjection, Matrix.mul_apply, coordinateEmbedding, hx',
      if_false, zero_mul, Finset.sum_const_zero, Matrix.diagonal_apply, if_neg hx]
    split <;> rfl

omit [DecidableEq ι] [Fintype κ] in
theorem coordinateProjection_isHermitian (e : ι ↪ κ) :
    (coordinateProjection e).IsHermitian :=
  Matrix.isHermitian_mul_conjTranspose_self _

theorem coordinateProjection_idempotent (e : ι ↪ κ) :
    coordinateProjection e * coordinateProjection e = coordinateProjection e := by
  simp only [coordinateProjection, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (coordinateEmbedding e)ᴴ, coordinateEmbedding_isometry,
    Matrix.one_mul]

/-- Embedding by an isometry preserves positivity and trace. -/
def embedDensity (e : ι ↪ κ) (ρ : DensityMatrix ι) : DensityMatrix κ :=
  ⟨coordinateEmbedding e * ρ.1 * (coordinateEmbedding e)ᴴ,
    ρ.2.1.mul_mul_conjTranspose_same _, by
      rw [Matrix.trace_mul_cycle, coordinateEmbedding_isometry, Matrix.one_mul]
      exact ρ.2.2⟩

theorem coordinateProjection_embedDensity (e : ι ↪ κ) (ρ : DensityMatrix ι) :
    coordinateProjection e * (embedDensity e ρ).1 = (embedDensity e ρ).1 := by
  change (coordinateEmbedding e * (coordinateEmbedding e)ᴴ) *
    (coordinateEmbedding e * ρ.1 * (coordinateEmbedding e)ᴴ) =
      coordinateEmbedding e * ρ.1 * (coordinateEmbedding e)ᴴ
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (coordinateEmbedding e)ᴴ, coordinateEmbedding_isometry,
    Matrix.one_mul]

/-- Isometric compression recovers the original density matrix. -/
theorem compress_embedDensity (e : ι ↪ κ) (ρ : DensityMatrix ι) :
    (coordinateEmbedding e)ᴴ * (embedDensity e ρ).1 * coordinateEmbedding e = ρ.1 := by
  change (coordinateEmbedding e)ᴴ *
    (coordinateEmbedding e * ρ.1 * (coordinateEmbedding e)ᴴ) * coordinateEmbedding e = _
  simp only [← Matrix.mul_assoc]
  rw [coordinateEmbedding_isometry, Matrix.one_mul, Matrix.mul_assoc,
    coordinateEmbedding_isometry, Matrix.mul_one]

/-- A positive state lies in the coordinate sector exactly when it is an embedded state. -/
theorem exists_embedDensity_iff (e : ι ↪ κ) (ρ : DensityMatrix κ) :
    (∃ τ : DensityMatrix ι, embedDensity e τ = ρ) ↔
      coordinateProjection e * ρ.1 = ρ.1 := by
  constructor
  · rintro ⟨τ, rfl⟩
    exact coordinateProjection_embedDensity e τ
  · intro h
    have hr : ρ.1 * coordinateProjection e = ρ.1 := by
      have ht := congrArg Matrix.conjTranspose h
      simpa only [Matrix.conjTranspose_mul, ρ.2.1.isHermitian.eq,
        (coordinateProjection_isHermitian e).eq] using ht
    let τ : DensityMatrix ι :=
      ⟨(coordinateEmbedding e)ᴴ * ρ.1 * coordinateEmbedding e,
        ρ.2.1.conjTranspose_mul_mul_same _, by
          rw [Matrix.trace_mul_cycle]
          change (coordinateProjection e * ρ.1).trace = 1
          rw [h, ρ.2.2]⟩
    refine ⟨τ, Subtype.ext ?_⟩
    change coordinateEmbedding e *
      ((coordinateEmbedding e)ᴴ * ρ.1 * coordinateEmbedding e) *
        (coordinateEmbedding e)ᴴ = ρ.1
    calc
      _ = coordinateProjection e * ρ.1 * coordinateProjection e := by
        simp only [coordinateProjection, Matrix.mul_assoc]
      _ = ρ.1 := by rw [h, hr]

/-- Coordinate embedding is injective even for mixed states. -/
theorem embedDensity_injective (e : ι ↪ κ) : Function.Injective (embedDensity e) := by
  intro ρ τ h
  apply Subtype.ext
  have hc := congrArg (fun X : DensityMatrix κ =>
    (coordinateEmbedding e)ᴴ * X.1 * coordinateEmbedding e) h
  simpa only [compress_embedDensity] using hc

end GaloisForLFunctions.HTGeometry.Quantum
