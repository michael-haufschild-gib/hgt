import GaloisForLFunctions.HTGeometry.OperatorConductorLength

/-!
# The balance law for invertible operator matrices

A matrix over `K[∂;δ]` that is invertible over the operator ring itself, not merely over the skew
field of fractions, carries the integral lattice onto itself.  Its conductor is therefore trivial
and every elementary divisor has degree zero: the relative position vector of the two lattices sums
to zero.

This is the determinant-balance statement for the action of a differential automorphism on the
lattice model of the variational building — the Dieudonné determinant of an invertible operator
matrix has degree zero — obtained here from the lattice description rather than from a determinant
theory.
-/

open scoped Differential
open nonZeroDivisors OreLocalization

namespace GaloisForLFunctions.HTGeometry

namespace DiffOp

noncomputable section

variable {K : Type u} [Field K] [Differential K]
variable {ι : Type*} [Fintype ι]

/-- A matrix with a two-sided row inverse has left independent rows. -/
theorem rowIndep_of_vecMul_inverse (P Q : ι → ι → DiffOp K)
    (hPQ : ∀ v : ι → DiffOp K, vecMul (vecMul v P) Q = v) : RowIndep P := by
  intro v hv
  have h := hPQ v
  rw [hv, vecMul_zero] at h
  exact h.symm

/-- The rows of a matrix with a two-sided row inverse span everything. -/
theorem rowSpace_eq_top_of_vecMul_inverse (P Q : ι → ι → DiffOp K)
    (hQP : ∀ v : ι → DiffOp K, vecMul (vecMul v Q) P = v) :
    rowSpace P = ⊤ :=
  eq_top_iff.mpr fun w _ => mem_rowSpace.mpr ⟨vecMul w Q, hQP w⟩

/-- **An invertible operator matrix preserves the integral lattice.** -/
theorem rowLattice_eq_integralLattice_of_vecMul_inverse (P Q : ι → ι → DiffOp K)
    (hQP : ∀ v : ι → DiffOp K, vecMul (vecMul v Q) P = v) :
    rowLattice P = integralLattice ι := by
  refine le_antisymm (fun w hw => (rowLattice_le_satLattice P hw).2) ?_
  rintro _ ⟨u, rfl⟩
  refine ⟨integralVec ι (vecMul u Q), ⟨vecMul u Q, rfl⟩, ?_⟩
  rw [pseudoVecMulLin_apply, pseudoVecMul_integralVec, hQP u]

variable [DecidableEq ι]

omit [DecidableEq ι] in
/-- **The balance law.**  The conductor of an invertible operator matrix is trivial. -/
theorem quotDim_conductor_eq_zero_of_vecMul_inverse (P Q : ι → ι → DiffOp K)
    (hPQ : ∀ v : ι → DiffOp K, vecMul (vecMul v P) Q = v)
    (hQP : ∀ v : ι → DiffOp K, vecMul (vecMul v Q) P = v) :
    quotDim ((rowLattice P).restrictScalars K) ((satLattice P).restrictScalars K) = 0 := by
  have hindep : RowIndep P := rowIndep_of_vecMul_inverse P Q hPQ
  rw [satLattice_eq_integralLattice P hindep,
    rowLattice_eq_integralLattice_of_vecMul_inverse P Q hQP]
  exact quotDim_of_le le_rfl

/-- **Degree balance.**  Every elementary divisor of an invertible operator matrix has degree zero,
so the relative position vector of the integral lattice and its image sums to zero. -/
theorem exists_degree_sum_eq_zero_of_vecMul_inverse (P Q : ι → ι → DiffOp K)
    (hPQ : ∀ v : ι → DiffOp K, vecMul (vecMul v P) Q = v)
    (hQP : ∀ v : ι → DiffOp K, vecMul (vecMul v Q) P = v) :
    ∃ d : ι → DiffOp K, (∀ i, d i ≠ 0) ∧ ∑ i, degree (d i) = 0 ∧ ∀ i, degree (d i) = 0 := by
  have hindep : RowIndep P := rowIndep_of_vecMul_inverse P Q hPQ
  obtain ⟨d, hd, hsum⟩ := exists_degree_sum_eq_quotDim_conductor P hindep
  have hzero : ∑ i, degree (d i) = 0 := by
    rw [← hsum]
    exact quotDim_conductor_eq_zero_of_vecMul_inverse P Q hPQ hQP
  refine ⟨d, hd, hzero, fun i => ?_⟩
  have := Finset.sum_eq_zero_iff.mp hzero i (Finset.mem_univ i)
  exact this

end

end DiffOp

end GaloisForLFunctions.HTGeometry
