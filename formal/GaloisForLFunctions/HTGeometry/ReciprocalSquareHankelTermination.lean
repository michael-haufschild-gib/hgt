import GaloisForLFunctions.HTGeometry.ReciprocalSquareMomentConservation
import GaloisForLFunctions.HTGeometry.FiniteFieldStateSpaceHankelRank

/-!
# Finite reciprocal-square laws have terminating Hankel towers

For a finite square matrix `A`, the shifted trace-power sequence

`k ↦ trace (A ^ (k + 1))`

has a singular Hankel block of size `d² + 1`.  The proof needs no diagonalization: the first
`d² + 1` matrix powers are linearly dependent in the `d²`-dimensional matrix space, and the same
relation annihilates every row of the trace-power Hankel matrix.

Applying this to the two reciprocal squares of a rectangular transfer gives one shared moment
sequence which terminates at both finite matrix-space bounds.  The bound is intentionally not
sharp; its role is to certify finite termination without spectral assumptions.

This is classical finite-dimensional linear algebra.  It does not identify either reciprocal
square with a physical law or prove that a physical source has a non-terminating moment tower.
-/

open scoped BigOperators Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Shifted complex trace-power moments of a finite square matrix. -/
def matrixComplexTracePowerMoment {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℂ) (k : ℕ) : ℂ :=
  (A ^ (k + 1)).trace

/-- Any `d² + 1` powers of one `d × d` matrix satisfy a nonzero scalar relation. -/
theorem exists_matrixPower_relation {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℂ) :
    ∃ c : Fin (d * d + 1) → ℂ,
      (∑ j, c j • (A ^ (j : ℕ))) = 0 ∧ ∃ j, c j ≠ 0 := by
  let v : Fin (d * d + 1) → Matrix (Fin d) (Fin d) ℂ :=
    fun j ↦ A ^ (j : ℕ)
  have hv : ¬ LinearIndependent ℂ v := by
    intro hli
    have hbound := hli.fintype_card_le_finrank
    rw [Module.finrank_matrix] at hbound
    simp only [Fintype.card_fin, Module.finrank_self, mul_one] at hbound
    omega
  simpa only [v] using Fintype.not_linearIndependent_iff.mp hv

/-- A relation among matrix powers is a kernel vector of the shifted trace-power Hankel block. -/
theorem algebraicHankelMatrix_mulVec_matrixPower_relation_eq_zero
    {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ)
    (c : Fin (d * d + 1) → ℂ)
    (hc : (∑ j, c j • (A ^ (j : ℕ))) = 0) :
    HTGeometry.algebraicHankelMatrix
      (matrixComplexTracePowerMoment A) (d * d + 1) *ᵥ c = 0 := by
  funext r
  simp only [Matrix.mulVec, HTGeometry.algebraicHankelMatrix, Pi.zero_apply]
  change ∑ j : Fin (d * d + 1),
      (A ^ ((r : ℕ) + (j : ℕ) + 1)).trace * c j = 0
  have hsum :
      ∑ j : Fin (d * d + 1),
          c j • (A ^ ((r : ℕ) + 1) * A ^ (j : ℕ)) = 0 := by
    calc
      ∑ j : Fin (d * d + 1),
          c j • (A ^ ((r : ℕ) + 1) * A ^ (j : ℕ)) =
          A ^ ((r : ℕ) + 1) * ∑ j, c j • A ^ (j : ℕ) := by
        rw [Matrix.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        simp
      _ = 0 := by rw [hc, Matrix.mul_zero]
  have htrace := congrArg Matrix.trace hsum
  have htrace' :
      (∑ j : Fin (d * d + 1),
        c j * (A ^ ((r : ℕ) + 1) * A ^ (j : ℕ)).trace) = 0 := by
    simpa only [Matrix.trace_sum, Matrix.trace_smul, Matrix.trace_zero] using! htrace
  calc
    ∑ j : Fin (d * d + 1),
        (A ^ ((r : ℕ) + (j : ℕ) + 1)).trace * c j =
        ∑ j : Fin (d * d + 1),
          c j * (A ^ ((r : ℕ) + 1) * A ^ (j : ℕ)).trace := by
      apply Finset.sum_congr rfl
      intro j _
      have hp :
          A ^ ((r : ℕ) + (j : ℕ) + 1) =
            A ^ ((r : ℕ) + 1) * A ^ (j : ℕ) := by
        rw [← pow_add]
        congr 1
        omega
      rw [hp]
      ring
    _ = 0 := htrace'

/-- **Finite trace-power termination.**  Every finite matrix trace-power sequence has a singular
Hankel block. -/
theorem det_algebraicHankelMatrix_matrixComplexTracePowerMoment_eq_zero
    {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) :
    (HTGeometry.algebraicHankelMatrix
      (matrixComplexTracePowerMoment A) (d * d + 1)).det = 0 := by
  obtain ⟨c, hrel, j, hj⟩ := exists_matrixPower_relation A
  apply Matrix.det_eq_zero_of_mulVec_eq_zero_of_mem_nonZeroDivisors
    (algebraicHankelMatrix_mulVec_matrixPower_relation_eq_zero A c hrel)
    (i := j)
  simpa [mem_nonZeroDivisors_iff_ne_zero] using hj

/-- Shared shifted trace moments of the two reciprocal squares of a finite transfer. -/
def reciprocalSquareMoment {m n : ℕ}
    (D : Matrix (Fin m) (Fin n) ℂ) (k : ℕ) : ℂ :=
  ((reciprocalDomainSquare D) ^ (k + 1)).trace

/-- The shared moment may be read from the codomain reciprocal square. -/
theorem reciprocalSquareMoment_eq_codomain {m n : ℕ}
    (D : Matrix (Fin m) (Fin n) ℂ) (k : ℕ) :
    reciprocalSquareMoment D k =
      ((reciprocalCodomainSquare D) ^ (k + 1)).trace :=
  reciprocalSquare_trace_pow_succ_eq D k

/-- The shared reciprocal moment tower terminates at the finite domain matrix-space bound. -/
theorem det_algebraicHankelMatrix_reciprocalSquareMoment_domain_eq_zero
    {m n : ℕ} (D : Matrix (Fin m) (Fin n) ℂ) :
    (HTGeometry.algebraicHankelMatrix
      (reciprocalSquareMoment D) (n * n + 1)).det = 0 := by
  exact det_algebraicHankelMatrix_matrixComplexTracePowerMoment_eq_zero
    (reciprocalDomainSquare D)

/-- The same shared tower also terminates at the finite codomain matrix-space bound. -/
theorem det_algebraicHankelMatrix_reciprocalSquareMoment_codomain_eq_zero
    {m n : ℕ} (D : Matrix (Fin m) (Fin n) ℂ) :
    (HTGeometry.algebraicHankelMatrix
      (reciprocalSquareMoment D) (m * m + 1)).det = 0 := by
  have hmoment :
      reciprocalSquareMoment D =
        matrixComplexTracePowerMoment (reciprocalCodomainSquare D) := by
    funext k
    exact reciprocalSquareMoment_eq_codomain D k
  rw [hmoment]
  exact det_algebraicHankelMatrix_matrixComplexTracePowerMoment_eq_zero
    (reciprocalCodomainSquare D)

end

end GaloisForLFunctions.HTGeometry
