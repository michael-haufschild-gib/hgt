import GaloisForLFunctions.HTGeometry.FiniteBilateralWeightedShift
import GaloisForLFunctions.RHTower.PaperPrimeRotationNormRate

/-! # Literal finite coordinate compressions of the prime rotation commutator

The operator acts on the original full bilateral Hilbert space. The coordinate
window contains the vertices `0,...,N`, hence the compressed shift has `N` edges.
-/

namespace RHTower
noncomputable section
open GaloisForLFunctions.HTGeometry HilbertSchmidt _root_.ContinuousLinearMap
open Filter Topology

def paperPrimeRotationEdgeWeight (p : Nat.Primes) (q : ℕ) (j : ℤ) : ℂ :=
  (paperRotationPhase (paperPrimeRotationFrequency p q) - 1) *
    paperRotationPhase (paperPrimeRotationFrequency p q * j)

def paperPrimeRotationCompression (p : Nat.Primes) (q N : ℕ) :
    PaperRotationHilbert →L[ℂ] PaperRotationHilbert :=
  coordTruncation (bilateralShiftWindow N) ∘L
    paperPrimeRotationCommutator p q 0 1 1 0 ∘L
      coordTruncation (bilateralShiftWindow N)

theorem paperPrimeRotationEdgeWeight_norm (p : Nat.Primes) (q : ℕ) (j : ℤ) :
    ‖paperPrimeRotationEdgeWeight p q j‖ =
      ‖paperRotationPhase (paperPrimeRotationFrequency p q) - 1‖ := by
  simp [paperPrimeRotationEdgeWeight]

theorem paperPrimeRotationPrimitive_apply (p : Nat.Primes) (q : ℕ)
    (f : PaperRotationHilbert) (i : ℤ) :
    paperPrimeRotationCommutator p q 0 1 1 0 f i =
      paperPrimeRotationEdgeWeight p q (i - 1) * f (i - 1) := by
  simp [paperPrimeRotationCommutator, paperRotationCommutator_eq,
    smul_apply, comp_apply, paperRotationWord_apply, lp.coeFn_smul,
    Pi.smul_apply, smul_eq_mul, paperPrimeRotationEdgeWeight, mul_assoc]

theorem paperPrimeRotationCompression_apply (p : Nat.Primes) (q N : ℕ)
    (f : PaperRotationHilbert) (i : ℤ) :
    paperPrimeRotationCompression p q N f i =
      if i ∈ bilateralShiftWindow N ∧ i - 1 ∈ bilateralShiftWindow N
      then paperPrimeRotationEdgeWeight p q (i - 1) * f (i - 1) else 0 := by
  simp only [paperPrimeRotationCompression, comp_apply, coordTruncation_apply_coordinate,
    paperPrimeRotationPrimitive_apply]
  split_ifs <;> simp_all

theorem paperPrimeRotationCompression_eq_weightedShift (p : Nat.Primes) (q N : ℕ) :
    paperPrimeRotationCompression p q N =
      finiteBilateralWeightedShift N (paperPrimeRotationEdgeWeight p q) := by
  apply HasLpMatrix.ext (K := fun i j =>
    if j ∈ bilateralShiftEdges N ∧ i = j + 1 then paperPrimeRotationEdgeWeight p q j else 0)
  · intro i j
    rw [paperPrimeRotationCompression_apply]
    by_cases h : i = j + 1
    · subst i
      have he : j + 1 ∈ bilateralShiftWindow N ∧ j ∈ bilateralShiftWindow N ↔
          j ∈ bilateralShiftEdges N := by
        simp only [bilateralShiftWindow, bilateralShiftEdges, Finset.mem_Icc, Finset.mem_Ico]
        omega
      simp [he, lpBasisVec, lp.single_apply]
    · have he : j ≠ i - 1 := by omega
      simp [h, lpBasisVec, lp.single_apply, he]
  · intro i j
    have h := coordMatrix_finiteBilateralWeightedShift N (paperPrimeRotationEdgeWeight p q) i j
    rw [coordMatrix_apply, lpBasis_apply, lpBasis_apply] at h
    change inner ℂ (lpBasisVec i)
      (finiteBilateralWeightedShift N (paperPrimeRotationEdgeWeight p q) (lpBasisVec j)) = _ at h
    rwa [inner_lpBasisVec] at h

theorem paperPrimeRotationCompression_traceClass (p : Nat.Primes) (q N : ℕ) :
    MemSchattenClass 1 (paperPrimeRotationCompression p q N) := by
  rw [paperPrimeRotationCompression_eq_weightedShift]
  exact finiteBilateralWeightedShift_traceClass _ _

theorem paperPrimeRotationCompression_compact (p : Nat.Primes) (q N : ℕ) :
    IsCompactOperator (paperPrimeRotationCompression p q N) :=
  (paperPrimeRotationCompression_traceClass p q N).isCompactOperator one_pos

theorem paperPrimeRotationCompression_norm_le (p : Nat.Primes) (q N : ℕ) :
    ‖paperPrimeRotationCompression p q N‖ ≤ ‖paperPrimeRotationCommutator p q 0 1 1 0‖ := by
  refine opNorm_le_bound _ (norm_nonneg _) fun f => ?_
  change ‖coordTruncation _ (paperPrimeRotationCommutator p q 0 1 1 0
    (coordTruncation _ f))‖ ≤ _
  exact (norm_coordTruncation_apply_le _ _).trans
    ((le_opNorm _ _).trans (mul_le_mul_of_nonneg_left
      (norm_coordTruncation_apply_le _ _) (norm_nonneg _)))

theorem paperPrimeRotationCompression_norm_succ (p : Nat.Primes) (q N : ℕ) :
    ‖paperPrimeRotationCompression p q (N + 1)‖ =
      ‖paperRotationPhase (paperPrimeRotationFrequency p q) - 1‖ := by
  apply le_antisymm
  · simpa [paperPrimeRotationCommutator_norm] using paperPrimeRotationCompression_norm_le p q (N + 1)
  · have h := le_opNorm (paperPrimeRotationCompression p q (N + 1)) (lpBasisVec (0 : ℤ))
    rw [paperPrimeRotationCompression_eq_weightedShift, finiteBilateralWeightedShift_basis] at h
    simpa [paperPrimeRotationCompression_eq_weightedShift, bilateralShiftEdges,
      paperPrimeRotationEdgeWeight, norm_smul,
      lpBasisVec, lp.norm_single] using h

theorem paperPrimeRotationCompression_norm_tendsto (p : Nat.Primes) (window : ℕ → ℕ) :
    Tendsto (fun q => ‖paperPrimeRotationCompression p q (window q)‖) atTop (𝓝 0) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa using (paperPrimeRotationCommutator_tendsto_zero p 0 1 1 0).norm)
    (fun _ => norm_nonneg _) (fun q => paperPrimeRotationCompression_norm_le p q (window q))

end
end RHTower
