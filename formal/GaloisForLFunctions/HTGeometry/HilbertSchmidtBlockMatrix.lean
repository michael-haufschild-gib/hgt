/-
# The block matrix of a truncated Hilbert–Schmidt kernel

A kernel truncated to a finite index block `s` is the zero-extension of an honest square matrix
indexed by `↥s`.  This file makes that identification and transports the two quantities the
regularized determinant needs: the traces of the powers and the Hilbert–Schmidt energy.

Main results:
* `ofBlock`, `blockMatrix`, `truncKernel_eq_ofBlock` — the identification.
* `hsComp_ofBlock`, `hsPow_ofBlock` — the kernel algebra is the matrix algebra.
* `hsTrace_hsPow_ofBlock` — `tr(Kₛⁿ)` is the matrix trace of the `n`-th power of the block.
* `matHSNormSq_blockMatrix_le` — the block energy is at most the kernel energy.
-/
import GaloisForLFunctions.HTGeometry.HilbertSchmidtTruncation
import GaloisForLFunctions.HTGeometry.FiniteRegularizedDeterminant

namespace HilbertSchmidt

open Finset

variable {ι : Type*} [DecidableEq ι]

/-- A matrix on a finite index block, extended by zero to the whole index type. -/
def ofBlock {s : Finset ι} (A : Matrix ↥s ↥s ℂ) : ι × ι → ℂ :=
  fun p => if h : p.1 ∈ s ∧ p.2 ∈ s then A ⟨p.1, h.1⟩ ⟨p.2, h.2⟩ else 0

/-- The block of a kernel on a finite index set, as a matrix. -/
def blockMatrix (K : ι × ι → ℂ) (s : Finset ι) : Matrix ↥s ↥s ℂ :=
  fun i j => K ((i : ι), (j : ι))

theorem ofBlock_apply_of_mem {s : Finset ι} (A : Matrix ↥s ↥s ℂ) {i j : ι}
    (hi : i ∈ s) (hj : j ∈ s) : ofBlock A (i, j) = A ⟨i, hi⟩ ⟨j, hj⟩ := by
  simp [ofBlock, hi, hj]

theorem ofBlock_apply_of_notMem_left {s : Finset ι} (A : Matrix ↥s ↥s ℂ) {i j : ι}
    (hi : i ∉ s) : ofBlock A (i, j) = 0 := by simp [ofBlock, hi]

theorem ofBlock_apply_of_notMem_right {s : Finset ι} (A : Matrix ↥s ↥s ℂ) {i j : ι}
    (hj : j ∉ s) : ofBlock A (i, j) = 0 := by simp [ofBlock, hj]

theorem truncKernel_eq_ofBlock (K : ι × ι → ℂ) (s : Finset ι) :
    truncKernel K s = ofBlock (blockMatrix K s) := by
  funext p
  simp only [truncKernel, ofBlock, blockMatrix]
  by_cases h : p.1 ∈ s ∧ p.2 ∈ s <;> simp [h]

/-- The kernel composition of two zero-extended blocks is the zero extension of their matrix
product. -/
theorem hsComp_ofBlock {s : Finset ι} (A B : Matrix ↥s ↥s ℂ) :
    hsComp (ofBlock A) (ofBlock B) = ofBlock (A * B) := by
  funext p
  obtain ⟨i, j⟩ := p
  by_cases hi : i ∈ s
  · by_cases hj : j ∈ s
    · have hzero : ∀ k ∉ s, ofBlock A (i, k) * ofBlock B (k, j) = 0 := fun k hk => by
        rw [ofBlock_apply_of_notMem_right A hk, zero_mul]
      show (∑' k, ofBlock A (i, k) * ofBlock B (k, j)) = _
      rw [tsum_eq_sum (s := s) hzero, ofBlock_apply_of_mem _ hi hj, Matrix.mul_apply,
        ← Finset.sum_coe_sort s fun k : ι => ofBlock A (i, k) * ofBlock B (k, j)]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [ofBlock_apply_of_mem A hi k.2, ofBlock_apply_of_mem B k.2 hj]
    · have hzero : ∀ k : ι, ofBlock A (i, k) * ofBlock B (k, j) = 0 := fun k => by
        rw [ofBlock_apply_of_notMem_right B hj, mul_zero]
      show (∑' k, ofBlock A (i, k) * ofBlock B (k, j)) = _
      rw [ofBlock_apply_of_notMem_right (A * B) hj]
      simp [hzero]
  · have hzero : ∀ k : ι, ofBlock A (i, k) * ofBlock B (k, j) = 0 := fun k => by
      rw [ofBlock_apply_of_notMem_left A hi, zero_mul]
    show (∑' k, ofBlock A (i, k) * ofBlock B (k, j)) = _
    rw [ofBlock_apply_of_notMem_left (A * B) hi]
    simp [hzero]

theorem hsPow_ofBlock {s : Finset ι} (A : Matrix ↥s ↥s ℂ) (n : ℕ) :
    hsPow (ofBlock A) n = ofBlock (A ^ (n + 1)) := by
  induction n with
  | zero => simp [hsPow]
  | succ n ih =>
    rw [hsPow, ih, hsComp_ofBlock]
    congr 1
    rw [pow_succ' A (n + 1)]

/-- The kernel trace of a power of a zero-extended block is the matrix trace of the power. -/
theorem hsTrace_hsPow_ofBlock {s : Finset ι} (A : Matrix ↥s ↥s ℂ) (n : ℕ) :
    ∑' i : ι, hsPow (ofBlock A) n (i, i) = (A ^ (n + 1)).trace := by
  rw [hsPow_ofBlock, tsum_eq_sum (s := s) fun i hi => ofBlock_apply_of_notMem_left _ hi,
    Matrix.trace, ← Finset.sum_coe_sort s fun i : ι => ofBlock (A ^ (n + 1)) (i, i)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ofBlock_apply_of_mem _ i.2 i.2]
  simp

/-- The kernel trace of a power of the truncation is the matrix trace of the power of the block. -/
theorem hsTrace_hsPow_truncKernel (K : ι × ι → ℂ) (s : Finset ι) (n : ℕ) :
    ∑' i : ι, hsPow (truncKernel K s) n (i, i) = ((blockMatrix K s) ^ (n + 1)).trace := by
  rw [truncKernel_eq_ofBlock, hsTrace_hsPow_ofBlock]

omit [DecidableEq ι] in
/-- The Hilbert–Schmidt energy of the block is the partial entry sum. -/
theorem matHSNormSq_blockMatrix (K : ι × ι → ℂ) (s : Finset ι) :
    GaloisForLFunctions.HTGeometry.matHSNormSq (blockMatrix K s) = ∑ p ∈ s ×ˢ s, ‖K p‖ ^ (2 : ℕ) := by
  rw [GaloisForLFunctions.HTGeometry.matHSNormSq, Finset.sum_product,
    ← Finset.sum_coe_sort s fun i : ι => ∑ j ∈ s, ‖K (i, j)‖ ^ (2 : ℕ)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_coe_sort s fun j : ι => ‖K ((i : ι), j)‖ ^ (2 : ℕ)]
  rfl

/-- The block energy never exceeds the kernel energy. -/
theorem matHSNormSq_blockMatrix_le {K : ι × ι → ℂ} (hK : IsHS K) (s : Finset ι) :
    GaloisForLFunctions.HTGeometry.matHSNormSq (blockMatrix K s) ≤ hsNormSq K := by
  rw [matHSNormSq_blockMatrix, ← hsNormSq_truncKernel_eq_sum]
  exact hsNormSq_truncKernel_le hK s

end HilbertSchmidt
