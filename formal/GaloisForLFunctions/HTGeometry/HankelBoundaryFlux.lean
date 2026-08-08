import GaloisForLFunctions.HTGeometry.HankelTerminalFlux

/-!
# Boundary flux of a singular finite Hankel block

For a moment flow satisfying `mₖ' = -(k+1)mₖ₊₁`, finite truncation leaves one symmetric rank-two
terminal flux.  On a null vector of the current Hankel block, both bulk Lyapunov terms vanish.
Consequently the full quadratic derivative is the product of exactly two boundary coordinates:
the leading coefficient of the null polynomial and its pairing with the first omitted monomial.

This identifies the genuine first-crossing obstruction.  No estimate on interior matrix entries can
control a crossing unless it controls this one terminal coupling.
-/

open Matrix
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Pairing of a coefficient vector with the first moment column omitted from an `n x n` Hankel
block. -/
def hankelFirstOmittedCoupling (m : ℕ → ℝ) (n : ℕ) (c : Fin n → ℝ) : ℝ :=
  ∑ j : Fin n, c j * m (n + (j : ℕ))

/-- A real rank-one outer product evaluates as the product of its two boundary coordinates. -/
theorem dotProduct_realOuterProduct_mulVec {n : ℕ}
    (c u v : Fin n → ℝ) :
    c ⬝ᵥ (realOuterProduct u v *ᵥ c) = (c ⬝ᵥ u) * (v ⬝ᵥ c) := by
  simp only [dotProduct, Matrix.mulVec, realOuterProduct]
  calc
    (∑ i, c i * ∑ j, u i * v j * c j) =
        ∑ i, (c i * u i) * ∑ j, v j * c j := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = (∑ i, c i * u i) * ∑ j, v j * c j := by
      rw [Finset.sum_mul]

/-- The terminal basis reads the leading coefficient of a vector of length `n+1`. -/
theorem dotProduct_hankelTerminalBasis_succ
    {n : ℕ} (c : Fin (n + 1) → ℝ) :
    c ⬝ᵥ hankelTerminalBasis (n + 1) = c (Fin.last n) := by
  rw [dotProduct, Finset.sum_eq_single (Fin.last n)]
  · simp [hankelTerminalBasis]
  · intro j _ hj
    have hval : (j : ℕ) + 1 ≠ n + 1 := by
      intro h
      apply hj
      apply Fin.ext
      simpa using Nat.add_right_cancel h
    have hval' : (j : ℕ) ≠ n := by
      intro h
      apply hj
      apply Fin.ext
      simpa using h
    simp [hankelTerminalBasis, hval']
  · intro h
    exact (h (Finset.mem_univ (Fin.last n))).elim

/-- The terminal moment vector is the first omitted moment column times the universal transport
weight `n - 1/2`. -/
theorem dotProduct_hankelTerminalMomentVector
    (m : ℕ → ℝ) (n : ℕ) (c : Fin n → ℝ) :
    hankelTerminalMomentVector m n ⬝ᵥ c =
      ((n : ℝ) - 1 / 2) * hankelFirstOmittedCoupling m n c := by
  rw [dotProduct, hankelFirstOmittedCoupling, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [hankelTerminalMomentVector]
  ring

/-- **Null-vector terminal-flux law.** On a kernel vector of a finite Hankel block, the quadratic
form of its derivative matrix contains no bulk term.  It is exactly minus twice the product of the
terminal coefficient and terminal moment pairing. -/
theorem dotProduct_finiteHankelDerivativeMatrix_mulVec_of_kernel
    (m : ℕ → ℝ) (n : ℕ) (c : Fin n → ℝ)
    (hc : finiteHankelMatrix m n *ᵥ c = 0) :
    c ⬝ᵥ (finiteHankelDerivativeMatrix m n *ᵥ c) =
      -2 * (c ⬝ᵥ hankelTerminalBasis n) *
        (hankelTerminalMomentVector m n ⬝ᵥ c) := by
  let H := finiteHankelMatrix m n
  let T := hankelWeightedUpperShift n
  let e := hankelTerminalBasis n
  let v := hankelTerminalMomentVector m n
  have hsym : Hᵀ = H := by
    ext i j
    simp [H, finiteHankelMatrix, add_comm]
  have hTH : (T * H) *ᵥ c = 0 := by
    rw [← Matrix.mulVec_mulVec, hc, Matrix.mulVec_zero]
  have hHT : c ⬝ᵥ ((H * Tᵀ) *ᵥ c) = 0 := by
    rw [← Matrix.mulVec_mulVec, ← hsym, Matrix.dotProduct_transpose_mulVec, hc,
      dotProduct_zero]
  rw [finiteHankelDerivativeMatrix_eq_transport_sub_terminalFlux]
  change c ⬝ᵥ ((-(T * H) - H * Tᵀ -
    (realOuterProduct e v + realOuterProduct v e)) *ᵥ c) =
      -2 * (c ⬝ᵥ e) * (v ⬝ᵥ c)
  simp only [Matrix.sub_mulVec, Matrix.neg_mulVec, Matrix.add_mulVec,
    dotProduct_sub, dotProduct_neg, dotProduct_add, hTH, hHT,
    neg_zero, zero_sub]
  rw [dotProduct_realOuterProduct_mulVec, dotProduct_realOuterProduct_mulVec]
  have hcomm : v ⬝ᵥ c = c ⬝ᵥ v := dotProduct_comm _ _
  have hcomm' : e ⬝ᵥ c = c ⬝ᵥ e := dotProduct_comm _ _
  rw [hcomm, hcomm']
  ring

/-- **Monic null-polynomial form.** For a block of size `n+1`, the terminal flux is the leading
coefficient times the first omitted coupling, with universal weight `2n+1`. -/
theorem dotProduct_finiteHankelDerivativeMatrix_mulVec_of_kernel_succ
    (m : ℕ → ℝ) (n : ℕ) (c : Fin (n + 1) → ℝ)
    (hc : finiteHankelMatrix m (n + 1) *ᵥ c = 0) :
    c ⬝ᵥ (finiteHankelDerivativeMatrix m (n + 1) *ᵥ c) =
      -(2 * (n : ℝ) + 1) * c (Fin.last n) *
        hankelFirstOmittedCoupling m (n + 1) c := by
  rw [dotProduct_finiteHankelDerivativeMatrix_mulVec_of_kernel m (n + 1) c hc,
    dotProduct_hankelTerminalBasis_succ,
    dotProduct_hankelTerminalMomentVector]
  push_cast
  ring

end

end GaloisForLFunctions.HTGeometry
