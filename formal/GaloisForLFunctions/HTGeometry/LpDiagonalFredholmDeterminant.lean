import GaloisForLFunctions.HTGeometry.LpDiagonalSchattenEnergy
import GaloisForLFunctions.HTGeometry.ReciprocalRecoveryFactorization

/-! # The operator Fredholm determinant of a complex summable diagonal

The standard Hilbert basis identifies the actual bounded multiplier with its
diagonal kernel. Its trace removes the regularization from the global entire
determinant, yielding the convergent product of the diagonal entries of `I+T`.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section
open _root_.RHTower HilbertSchmidt ContinuousLinearMap

theorem coordMatrix_lpDiagonalCLM (g : ℕ → ℂ) {C : ℝ}
    (hC : 0 ≤ C) (hg : ∀ n, ‖g n‖ ≤ C) :
    RHTower.coordMatrix (lpBasis ℕ) (lpDiagonalCLM g hC hg) = diagMul g := by
  funext p
  rcases p with ⟨i, j⟩
  rw [RHTower.coordMatrix_apply, lpBasis_apply, lpBasis_apply, lp.inner_single_left,
    lpDiagonalCLM_apply, lp.coeFn_single]
  by_cases h : i = j
  · subst h
    simp [diagMul, RCLike.inner_apply]
  · simp [diagMul, h, RCLike.inner_apply]

theorem opTrace_lpDiagonalCLM (g : ℕ → ℂ) {C : ℝ}
    (hC : 0 ≤ C) (hg : ∀ n, ‖g n‖ ≤ C) (hs : Summable fun n => ‖g n‖) :
    opTrace (lpDiagonalCLM g hC hg) = ∑' n, g n := by
  have hS1 : MemSchattenClass 1 (lpDiagonalCLM g hC hg) :=
    (memSchattenClass_lpDiagonalCLM_iff g hC hg zero_lt_one).mpr (by simpa using hs)
  rw [RHTower.opTrace_eq_tsum_basis_of_memSchattenClass_one hS1 (lpBasis ℕ)]
  refine tsum_congr fun n => ?_
  rw [lpBasis_apply, lp.inner_single_left, lpDiagonalCLM_apply,
    lp.single_apply, Pi.single_eq_same]
  simp

theorem fredholmDetOp_lpDiagonalCLM_of_hasProd (g : ℕ → ℂ) {C : ℝ}
    (hC : 0 ≤ C) (hg : ∀ n, ‖g n‖ ≤ C) (hs : Summable fun n => ‖g n‖)
    {P : ℂ} (hP : HasProd (fun n => 1 + g n) P) :
    RHTower.fredholmDetOp (lpBasis ℕ) (lpDiagonalCLM g hC hg) = P := by
  have he : HasProd (fun n => Complex.exp (-g n)) (Complex.exp (-(∑' n, g n))) :=
    hs.of_norm.hasSum.neg.cexp
  have hd := ReciprocalFusion.entireDet2_diagMul_neg_one
    (RHTower.summable_norm_sq_of_summable_norm hs) (hP.mul he)
  rw [RHTower.fredholmDetOp, RHTower.det2Op, coordMatrix_lpDiagonalCLM, hd,
    opTrace_lpDiagonalCLM g hC hg hs, mul_assoc, ← Complex.exp_add,
    neg_add_cancel, Complex.exp_zero, mul_one]

end
end GaloisForLFunctions.HTGeometry
