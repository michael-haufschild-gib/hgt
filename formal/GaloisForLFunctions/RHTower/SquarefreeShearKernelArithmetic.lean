import GaloisForLFunctions.RHTower.SquarefreeShearKernelFourier
import GaloisForLFunctions.HTGeometry.ABHN.CyclicGaloisH2CarryNormQuotient
import GaloisForLFunctions.HTGeometry.ConstraintRelativity.CofinalRankTransfer

/-!
# Arithmetic bridges for the squarefree shear kernel

This module identifies the literal `ZMod p` shear matrix used by the Fourier formulas with the
previously certified `Fin p` spectral block, then specializes the exact all-complement tensor norm
to the Euler totient ratio.  Thus the arithmetic Fourier kernel and the rank/inertia/norm kernel
are one matrix up to canonical simultaneous reindexing.
-/

open scoped BigOperators Matrix.Norms.L2Operator

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- Canonical reindexing from the spectral block's `Fin (p - 2 + 2)` carrier to `ZMod p`. -/
def primeShearIndexEquiv (p : ℕ) (hp : p.Prime) : Fin (p - 2 + 2) ≃ ZMod p := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  exact (finCongr (Nat.sub_add_cancel hp.two_le)).trans (ZMod.finEquiv p).toEquiv

/-- Canonical prime shear reindexing preserves the distinguished zero coordinate. -/
theorem primeShearIndexEquiv_eq_zero_iff
    {p : ℕ} (hp : p.Prime) (i : Fin (p - 2 + 2)) :
    primeShearIndexEquiv p hp i = 0 ↔ i = 0 := by
  rw [← ZMod.val_eq_zero]
  simp [primeShearIndexEquiv,
    GaloisForLFunctions.HTGeometry.ABHN.zmod_finEquiv_val]

/-- The literal prime residue shear kernel is exactly the prior raw spectral block after canonical
simultaneous reindexing. -/
theorem primeShearKernel_submatrix_eq_localRawShearBlock
    {p : ℕ} (hp : p.Prime) :
    (primeShearKernel p).submatrix (primeShearIndexEquiv p hp) (primeShearIndexEquiv p hp) =
      localRawShearBlock (p - 2) := by
  ext i j
  simp only [Matrix.submatrix_apply, primeShearKernel, localRawShearBlock,
    localShearKernel]
  rw [show (p : ℂ) = localScale (p - 2) by
    rw [localScale]
    exact_mod_cast (Nat.sub_add_cancel hp.two_le).symm]
  rw [if_congr (primeShearIndexEquiv_eq_zero_iff hp i) rfl rfl,
    if_congr (primeShearIndexEquiv_eq_zero_iff hp j) rfl rfl]

/-- Canonical product reindexing from all spectral coordinates to the composite residue ring. -/
def squarefreePrimeShearIndexEquiv
    {k : ℕ} (P : SquarefreePrimeFamily k) :
    (∀ i, Fin (P.primeValue i - 2 + 2)) ≃ ZMod P.product :=
  (Equiv.piCongrRight (fun i => primeShearIndexEquiv (P.primeValue i) (P.prime i))).trans
    (GaloisForLFunctions.IrregularStokes.DistinctPrimeFamily.crtEquiv P).toEquiv.symm

/-- The literal composite CRT shear kernel is exactly the prior raw squarefree spectral tensor
after canonical simultaneous reindexing. -/
theorem squarefreePrimeShearKernel_submatrix_eq_squarefreeShearTensor
    {k : ℕ} (P : SquarefreePrimeFamily k) :
    Matrix.submatrix (squarefreePrimeShearKernel P)
        (squarefreePrimeShearIndexEquiv P) (squarefreePrimeShearIndexEquiv P) =
      squarefreeShearTensor (fun i => P.primeValue i - 2) := by
  classical
  let E := GaloisForLFunctions.IrregularStokes.DistinctPrimeFamily.crtEquiv P
  have he (x : ∀ i, Fin (P.primeValue i - 2 + 2)) :
      E (squarefreePrimeShearIndexEquiv P x) =
        fun i => primeShearIndexEquiv (P.primeValue i) (P.prime i) (x i) := by
    exact E.apply_symm_apply _
  ext x y
  rw [Matrix.submatrix_apply, squarefreePrimeShearKernel, squarefreeShearTensor,
    tensorFamily_apply]
  rw [he x, he y]
  apply Finset.prod_congr rfl
  intro i _
  simpa [Matrix.submatrix_apply] using congrFun
    (congrFun (primeShearKernel_submatrix_eq_localRawShearBlock (P.prime i)) (x i)) (y i)

/-- Spectral excess parameter `k = p - 2` for one certified prime coordinate. -/
def squarefreePrimeKernelExcess {k : ℕ} (P : SquarefreePrimeFamily k) (i : Fin k) : ℕ :=
  P.primeValue i - 2

/-- The spectral scale at prime excess `p - 2` is exactly `p`. -/
theorem realScale_squarefreePrimeKernelExcess
    {k : ℕ} (P : SquarefreePrimeFamily k) (i : Fin k) :
    realScale (squarefreePrimeKernelExcess P i) = P.primeValue i := by
  simp [realScale, squarefreePrimeKernelExcess, Nat.cast_sub (P.prime i).two_le]

/-- One exposed complement branch has exact normalized norm `(p - 1) / p`. -/
theorem localComplementNorm_squarefreePrimeKernelExcess
    {k : ℕ} (P : SquarefreePrimeFamily k) (i : Fin k) :
    (realScale (squarefreePrimeKernelExcess P i) - 1) /
        realScale (squarefreePrimeKernelExcess P i) =
      ((P.primeValue i - 1 : ℕ) : ℝ) / P.primeValue i := by
  rw [realScale_squarefreePrimeKernelExcess]
  rw [Nat.cast_sub (P.prime i).one_le]
  norm_num

/-- `(SG8a)`: the exact operator norm of the fully exposed complement tensor is the Euler totient
ratio of the actual squarefree prime product. -/
theorem allComplementTensor_squarefreePrime_l2_opNorm_eq_totientRatio
    {k : ℕ} (P : SquarefreePrimeFamily k) :
    ‖allComplementTensor (squarefreePrimeKernelExcess P)‖ =
      (Nat.totient P.product : ℝ) / P.product := by
  rw [allComplementTensor_l2_opNorm]
  simp_rw [localComplementNorm_squarefreePrimeKernelExcess]
  rw [show (∏ i, ((P.primeValue i - 1 : ℕ) : ℝ) / (P.primeValue i : ℝ)) =
      (∏ i, ((P.primeValue i - 1 : ℕ) : ℝ)) / ∏ i, (P.primeValue i : ℝ) by
    simp [Finset.prod_div_distrib]]
  have htot :=
    HTGeometry.ConstraintRelativity.totient_prod_of_pairwise_coprime
      (Finset.univ : Finset (Fin k)) P.primeValue
      (fun i _ j _ hij => P.pairwise_coprime hij)
  simp_rw [Nat.totient_prime (P.prime _)] at htot
  rw [GaloisForLFunctions.IrregularStokes.DistinctPrimeFamily.product]
  push_cast
  congr 1
  norm_cast
  exact htot.symm

end


end RHTower
