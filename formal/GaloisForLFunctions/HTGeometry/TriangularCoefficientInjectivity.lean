import GaloisForLFunctions.HTGeometry.KernelRigidityTransfer
import GaloisForLFunctions.HTGeometry.NevanlinnaJetTriangular

/-!
# Injectivity of a triangular coefficient matrix

The coefficient matrix converting Cauchy powers into Nevanlinna jets is lower triangular, with
diagonal `r! · a z · (q' z) ^ r`.  Away from the critical locus — where `a` and `q'` both avoid zero
— that diagonal never vanishes, so the matrix is invertible and no nonzero packet is annihilated by
its transpose.

This is the condition consumed by the rigidity transfer, and the exact point at which noncriticality
is required.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- **A lower triangular matrix with nonvanishing diagonal has injective transpose action.** -/
theorem transpose_annihilator_eq_zero_of_lowerTriangular
    {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ)
    (htri : ∀ r k, r < k → M r k = 0) (hdiag : ∀ r, M r r ≠ 0)
    (c : Fin m → ℂ) (hc : ∀ k, ∑ r, c r * M r k = 0) :
    ∀ r, c r = 0 := by
  classical
  have hdet : M.det ≠ 0 := by
    rw [Matrix.det_of_lowerTriangular M htri]
    exact Finset.prod_ne_zero_iff.2 fun i _ => hdiag i
  have hinj : Function.Injective M.transpose.mulVec := by
    rw [Matrix.mulVec_injective_iff_isUnit, Matrix.isUnit_iff_isUnit_det,
      Matrix.det_transpose, isUnit_iff_ne_zero]
    exact hdet
  have hzero : M.transpose.mulVec c = 0 := by
    funext k
    simpa [Matrix.mulVec, dotProduct, Matrix.transpose_apply, mul_comm] using hc k
  have hc0 : c = 0 := hinj (by simpa using hzero)
  intro r
  exact congrFun hc0 r

/-- The Nevanlinna jet coefficient array, read as a square matrix at a fixed node. -/
def nevanlinnaJetCoeffMatrix (a q : ℂ → ℂ) (m : ℕ) (z : ℂ) :
    Matrix (Fin m) (Fin m) ℂ :=
  fun r k => nevanlinnaJetCoeff a q r k z

/-- The jet coefficient matrix is lower triangular. -/
theorem nevanlinnaJetCoeffMatrix_lowerTriangular (a q : ℂ → ℂ) (m : ℕ) (z : ℂ)
    (r k : Fin m) (hrk : r < k) : nevanlinnaJetCoeffMatrix a q m z r k = 0 := by
  have := nevanlinnaJetCoeff_eq_zero_of_lt a q (r := (r : ℕ)) (k := (k : ℕ)) hrk
  simp [nevanlinnaJetCoeffMatrix, this]

/-- Off the critical locus the diagonal of the jet coefficient matrix never vanishes. -/
theorem nevanlinnaJetCoeffMatrix_diagonal_ne_zero
    {a q : ℂ → ℂ} {z : ℂ} (ha : a z ≠ 0) (hq : deriv q z ≠ 0) (m : ℕ) (r : Fin m) :
    nevanlinnaJetCoeffMatrix a q m z r r ≠ 0 := by
  rw [nevanlinnaJetCoeffMatrix, nevanlinnaJetCoeff_diagonal]
  refine mul_ne_zero (mul_ne_zero ?_ ha) (pow_ne_zero _ hq)
  exact_mod_cast Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)

/-- **Noncriticality gives the transpose injectivity the rigidity transfer needs.**  Where the
amplitude and the derivative of the Cayley parameter both avoid zero, no nonzero coefficient packet
is annihilated by the transposed Nevanlinna jet coefficient matrix. -/
theorem nevanlinnaJetCoeff_transpose_annihilator_eq_zero
    {a q : ℂ → ℂ} {z : ℂ} (ha : a z ≠ 0) (hq : deriv q z ≠ 0) (m : ℕ)
    (c : Fin m → ℂ)
    (hc : ∀ k : Fin m, ∑ r : Fin m, c r * nevanlinnaJetCoeff a q r k z = 0) :
    ∀ r, c r = 0 :=
  transpose_annihilator_eq_zero_of_lowerTriangular (nevanlinnaJetCoeffMatrix a q m z)
    (nevanlinnaJetCoeffMatrix_lowerTriangular a q m z)
    (nevanlinnaJetCoeffMatrix_diagonal_ne_zero ha hq m) c hc

end

end GaloisForLFunctions.HTGeometry
