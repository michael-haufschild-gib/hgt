import GaloisForLFunctions.HTGeometry.Quantum.CoordinateStateEmbedding

/-!
# Positive duality on an encoded state sector

A Hermitian observable is nonnegative on all positive states in an encoded
sector exactly when its compression is positive semidefinite. Rank-one tests
prove the converse, so the dual description introduces no representability
assumption. This is the finite matrix polar-cone characterization of a face.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry.Quantum

open Matrix
open scoped ComplexOrder MatrixOrder

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- Positive matrices are exactly the Hermitian matrices nonnegative on every positive trace test. -/
theorem posSemidef_iff_positive_trace_tests {A : Matrix ι ι ℂ} (hA : A.IsHermitian) :
    A.PosSemidef ↔
      ∀ X : {X : Matrix ι ι ℂ // X.PosSemidef}, 0 ≤ (A * X.1).trace.re := by
  constructor
  · intro h X
    obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp X.2.nonneg
    have hf : X.1 = Bᴴ * B := by
      simpa only [Matrix.star_eq_conjTranspose] using hB
    rw [Matrix.trace_mul_comm, hf, ← constraintEnergy_eq_trace]
    exact constraintEnergy_nonneg B h
  · intro h
    apply posSemidef_of_matSesq_re_nonneg hA
    intro x
    have hx := h ⟨Matrix.vecMulVec x (star x), Matrix.posSemidef_vecMulVec_self_star x⟩
    simpa only [Matrix.mul_vecMulVec, Matrix.trace_vecMulVec,
      dotProduct_comm, matSesq_eq_dotProduct] using hx

/-- Trace duality between encoding positive states and compressing observables. -/
theorem trace_encoding_duality (V : Matrix κ ι ℂ) (B : Matrix κ κ ℂ)
    (X : Matrix ι ι ℂ) :
    (B * (V * X * Vᴴ)).trace = ((Vᴴ * B * V) * X).trace := by
  calc
    _ = ((B * V) * X * Vᴴ).trace := by simp only [Matrix.mul_assoc]
    _ = (Vᴴ * (B * V) * X).trace := Matrix.trace_mul_cycle _ _ _
    _ = _ := by simp only [Matrix.mul_assoc]

/-- The polar cone of an encoded positive sector is positivity after compression. -/
theorem compressed_posSemidef_iff (e : ι ↪ κ) (B : selfAdjoint (Matrix κ κ ℂ)) :
    ((coordinateEmbedding e)ᴴ * B.1 * coordinateEmbedding e).PosSemidef ↔
      ∀ X : {X : Matrix ι ι ℂ // X.PosSemidef},
        0 ≤ (B.1 * (coordinateEmbedding e * X.1 * (coordinateEmbedding e)ᴴ)).trace.re := by
  have hB : B.1ᴴ = B.1 := by
    simpa only [Matrix.star_eq_conjTranspose] using B.2
  have hH : ((coordinateEmbedding e)ᴴ * B.1 * coordinateEmbedding e).IsHermitian := by
    simp only [Matrix.IsHermitian, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, hB, Matrix.mul_assoc]
  rw [posSemidef_iff_positive_trace_tests hH]
  simp only [trace_encoding_duality]

end GaloisForLFunctions.HTGeometry.Quantum
