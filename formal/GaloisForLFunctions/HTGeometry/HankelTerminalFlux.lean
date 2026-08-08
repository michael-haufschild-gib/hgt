import Mathlib

/-!
# Finite Hankel transport and terminal flux

A moment flow satisfying

`m_k' = -(k+1) m_(k+1)`

has a finite-section Lyapunov law.  The weighted upper shift transports every interior row and
column exactly; finite truncation loses only a symmetric rank-two term supported on the terminal
basis vector.  This module proves the matrix identity and its entrywise differential realization
for an arbitrary real moment flow.
-/

open Matrix
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Finite Hankel block with indices `0, ..., n-1`. -/
def finiteHankelMatrix (m : ℕ → ℝ) (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => m ((i : ℕ) + (j : ℕ))

/-- Weighted raising shift with weight `i + 1/2` from row `i` to row `i+1`. -/
def hankelWeightedUpperShift (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i k => if (k : ℕ) = (i : ℕ) + 1 then (i : ℝ) + 1 / 2 else 0

/-- Terminal basis vector of a finite Hankel section. -/
def hankelTerminalBasis (n : ℕ) : Fin n → ℝ :=
  fun i => if (i : ℕ) + 1 = n then 1 else 0

/-- Moment vector carried by the terminal truncation face. -/
def hankelTerminalMomentVector (m : ℕ → ℝ) (n : ℕ) : Fin n → ℝ :=
  fun j => ((n : ℝ) - 1 / 2) * m (n + (j : ℕ))

/-- Rank-one outer product, kept explicit to avoid choosing an inner-product convention. -/
def realOuterProduct {n : ℕ} (u v : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => u i * v j

/-- Entrywise derivative prescribed by the moment recursion. -/
def finiteHankelDerivativeMatrix (m : ℕ → ℝ) (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => -(((i : ℕ) + (j : ℕ) + 1 : ℕ) : ℝ) *
    m ((i : ℕ) + (j : ℕ) + 1)

theorem finiteHankelMatrix_isHermitian (m : ℕ → ℝ) (n : ℕ) :
    (finiteHankelMatrix m n).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  simp [finiteHankelMatrix, add_comm]

private theorem hankelWeightedUpperShift_mul_apply
    (m : ℕ → ℝ) (n : ℕ) (i j : Fin n) :
    (hankelWeightedUpperShift n * finiteHankelMatrix m n) i j =
      if _h : (i : ℕ) + 1 < n then
        ((i : ℝ) + 1 / 2) * m ((i : ℕ) + 1 + (j : ℕ))
      else 0 := by
  rw [Matrix.mul_apply]
  by_cases hi : (i : ℕ) + 1 < n
  · rw [dif_pos hi]
    let k : Fin n := ⟨(i : ℕ) + 1, hi⟩
    rw [Finset.sum_eq_single k]
    · simp [hankelWeightedUpperShift, finiteHankelMatrix, k]
    · intro b _hb hbk
      have hbne : (b : ℕ) ≠ (i : ℕ) + 1 := by
        intro hval
        apply hbk
        exact Fin.ext hval
      simp [hankelWeightedUpperShift, hbne]
    · intro hk
      exact (hk (Finset.mem_univ k)).elim
  · rw [dif_neg hi]
    apply Finset.sum_eq_zero
    intro k _hk
    have hkne : (k : ℕ) ≠ (i : ℕ) + 1 := by
      intro hval
      have hkn : (k : ℕ) < n := k.isLt
      omega
    simp [hankelWeightedUpperShift, hkne]

private theorem finiteHankelMatrix_mul_weightedUpperShift_transpose_apply
    (m : ℕ → ℝ) (n : ℕ) (i j : Fin n) :
    (finiteHankelMatrix m n * (hankelWeightedUpperShift n)ᵀ) i j =
      if _h : (j : ℕ) + 1 < n then
        ((j : ℝ) + 1 / 2) * m ((i : ℕ) + ((j : ℕ) + 1))
      else 0 := by
  rw [Matrix.mul_apply]
  by_cases hj : (j : ℕ) + 1 < n
  · rw [dif_pos hj]
    let k : Fin n := ⟨(j : ℕ) + 1, hj⟩
    rw [Finset.sum_eq_single k]
    · simp [hankelWeightedUpperShift, finiteHankelMatrix, k]
      ring
    · intro b _hb hbk
      have hbne : (b : ℕ) ≠ (j : ℕ) + 1 := by
        intro hval
        apply hbk
        exact Fin.ext hval
      simp [hankelWeightedUpperShift, hbne]
    · intro hk
      exact (hk (Finset.mem_univ k)).elim
  · rw [dif_neg hj]
    apply Finset.sum_eq_zero
    intro k _hk
    have hkne : (k : ℕ) ≠ (j : ℕ) + 1 := by
      intro hval
      have hkn : (k : ℕ) < n := k.isLt
      omega
    simp [hankelWeightedUpperShift, hkne]

/-- **Finite Hankel Lyapunov law.**  Interior moment transport is exact; all truncation error is
the symmetric rank-two terminal flux `e v^T + v e^T`. -/
theorem finiteHankelDerivativeMatrix_eq_transport_sub_terminalFlux
    (m : ℕ → ℝ) (n : ℕ) :
    finiteHankelDerivativeMatrix m n =
      -(hankelWeightedUpperShift n * finiteHankelMatrix m n) -
        finiteHankelMatrix m n * (hankelWeightedUpperShift n)ᵀ -
      (realOuterProduct (hankelTerminalBasis n) (hankelTerminalMomentVector m n) +
        realOuterProduct (hankelTerminalMomentVector m n) (hankelTerminalBasis n)) := by
  ext i j
  simp only [Matrix.neg_apply, Matrix.sub_apply, Matrix.add_apply]
  rw [hankelWeightedUpperShift_mul_apply,
    finiteHankelMatrix_mul_weightedUpperShift_transpose_apply]
  by_cases hi : (i : ℕ) + 1 < n
  · rw [dif_pos hi]
    have hiterm : (i : ℕ) + 1 ≠ n := by omega
    by_cases hj : (j : ℕ) + 1 < n
    · rw [dif_pos hj]
      have hjterm : (j : ℕ) + 1 ≠ n := by omega
      simp [finiteHankelDerivativeMatrix, realOuterProduct,
        hankelTerminalBasis, hiterm, hjterm]
      have hmi : (i : ℕ) + 1 + (j : ℕ) = (i : ℕ) + (j : ℕ) + 1 := by omega
      have hmj : (i : ℕ) + ((j : ℕ) + 1) = (i : ℕ) + (j : ℕ) + 1 := by omega
      rw [hmi, hmj]
      ring
    · rw [dif_neg hj]
      have hjterm : (j : ℕ) + 1 = n := by omega
      simp [finiteHankelDerivativeMatrix, realOuterProduct,
        hankelTerminalBasis, hankelTerminalMomentVector, hiterm, hjterm]
      have hmi : (i : ℕ) + 1 + (j : ℕ) = (i : ℕ) + (j : ℕ) + 1 := by omega
      have hmn : n + (i : ℕ) = (i : ℕ) + (j : ℕ) + 1 := by omega
      have hncast : (n : ℝ) = (j : ℝ) + 1 := by exact_mod_cast hjterm.symm
      rw [hmi, hmn, hncast]
      ring
  · rw [dif_neg hi]
    have hiterm : (i : ℕ) + 1 = n := by omega
    by_cases hj : (j : ℕ) + 1 < n
    · rw [dif_pos hj]
      have hjterm : (j : ℕ) + 1 ≠ n := by omega
      simp [finiteHankelDerivativeMatrix, realOuterProduct,
        hankelTerminalBasis, hankelTerminalMomentVector, hiterm, hjterm]
      have hmj : (i : ℕ) + ((j : ℕ) + 1) = (i : ℕ) + (j : ℕ) + 1 := by omega
      have hmn : n + (j : ℕ) = (i : ℕ) + (j : ℕ) + 1 := by omega
      have hncast : (n : ℝ) = (i : ℝ) + 1 := by exact_mod_cast hiterm.symm
      rw [hmj, hmn, hncast]
      ring
    · rw [dif_neg hj]
      have hjterm : (j : ℕ) + 1 = n := by omega
      simp [finiteHankelDerivativeMatrix, realOuterProduct,
        hankelTerminalBasis, hankelTerminalMomentVector, hiterm, hjterm]
      have hmni : n + (i : ℕ) = (i : ℕ) + (j : ℕ) + 1 := by omega
      have hmnj : n + (j : ℕ) = (i : ℕ) + (j : ℕ) + 1 := by omega
      have hncasti : (n : ℝ) = (i : ℝ) + 1 := by exact_mod_cast hiterm.symm
      have hijNat : (i : ℕ) = (j : ℕ) := by omega
      have hijCast : (i : ℝ) = (j : ℝ) := by exact_mod_cast hijNat
      rw [hmni, hmnj, hncasti, hijCast]
      ring

/-- A moment recursion realizes the Lyapunov law as the actual derivative of every matrix entry. -/
theorem hasDerivAt_finiteHankelMatrix_entry_of_momentRecursion
    (m : ℝ → ℕ → ℝ) (n : ℕ) (y : ℝ)
    (hm : ∀ k : ℕ, HasDerivAt (fun t => m t k)
      (-((k : ℝ) + 1) * m y (k + 1)) y)
    (i j : Fin n) :
    HasDerivAt (fun t => finiteHankelMatrix (m t) n i j)
      ((-(hankelWeightedUpperShift n * finiteHankelMatrix (m y) n) -
          finiteHankelMatrix (m y) n * (hankelWeightedUpperShift n)ᵀ -
        (realOuterProduct (hankelTerminalBasis n)
            (hankelTerminalMomentVector (m y) n) +
          realOuterProduct (hankelTerminalMomentVector (m y) n)
            (hankelTerminalBasis n))) i j) y := by
  rw [← finiteHankelDerivativeMatrix_eq_transport_sub_terminalFlux]
  simpa [finiteHankelMatrix, finiteHankelDerivativeMatrix, Nat.cast_add,
    Nat.cast_one, add_assoc] using hm ((i : ℕ) + (j : ℕ))

end

end GaloisForLFunctions.HTGeometry
