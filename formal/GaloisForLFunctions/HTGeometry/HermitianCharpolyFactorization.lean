import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem

/-!
# The characteristic polynomial of a Hermitian matrix factors over its eigenvalues

Conjugating by the eigenvector unitary turns the characteristic determinant into the diagonal one,
so the characteristic polynomial splits into the linear factors given by the eigenvalues.  Comparing
coefficients with Vieta's formulas identifies every elementary symmetric function of the eigenvalues
with a coefficient of the characteristic polynomial.

Neither statement is in mathlib, and both are what turns a symmetric expression in the spectrum into
a polynomial in the matrix entries.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

variable {𝕜 : Type*} [RCLike 𝕜] {I : Type*} [Fintype I] [DecidableEq I]

/-- **The characteristic polynomial of a Hermitian matrix splits over its eigenvalues.** -/
theorem isHermitian_charpoly_eq_prod {A : Matrix I I 𝕜} (hA : A.IsHermitian) :
    A.charpoly = ∏ i, (Polynomial.X - Polynomial.C ((hA.eigenvalues i : ℝ) : 𝕜)) := by
  classical
  refine Polynomial.funext fun t => ?_
  rw [Matrix.eval_charpoly, Polynomial.eval_prod]
  have hspec := hA.spectral_theorem
  set U : Matrix I I 𝕜 := (hA.eigenvectorUnitary : Matrix I I 𝕜) with hU
  set D : Matrix I I 𝕜 := Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues) with hD
  have hAeq : A = U * D * star U := by
    rw [hspec, Unitary.conjStarAlgAut_apply]
  have hUstar : U * star U = 1 := by
    have := hA.eigenvectorUnitary.2
    rw [Matrix.mem_unitaryGroup_iff] at this
    exact this
  have hscal : (Matrix.scalar I) t = t • (1 : Matrix I I 𝕜) := by
    ext i j
    by_cases hij : i = j <;> simp [Matrix.scalar_apply, hij]
  have hfix : U * (t • (1 : Matrix I I 𝕜)) * star U = t • (1 : Matrix I I 𝕜) := by
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hUstar]
  have hconj : (Matrix.scalar I) t - A = U * ((Matrix.scalar I) t - D) * star U := by
    rw [hAeq, Matrix.mul_sub, Matrix.sub_mul, hscal, hfix]
  have hdetU : U.det * (star U).det = 1 := by
    rw [← Matrix.det_mul, hUstar, Matrix.det_one]
  have hdiag : (Matrix.scalar I) t - D = Matrix.diagonal fun i => t - ((hA.eigenvalues i : ℝ) : 𝕜) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [hD, Matrix.scalar_apply, Matrix.diagonal_apply_eq]
    · simp [hD, Matrix.scalar_apply, hij]
  rw [hconj, Matrix.det_mul, Matrix.det_mul, hdiag, Matrix.det_diagonal]
  calc U.det * (∏ i, (t - ((hA.eigenvalues i : ℝ) : 𝕜))) * (star U).det
      = (U.det * (star U).det) * ∏ i, (t - ((hA.eigenvalues i : ℝ) : 𝕜)) := by ring
    _ = ∏ i, (t - ((hA.eigenvalues i : ℝ) : 𝕜)) := by rw [hdetU, one_mul]
    _ = ∏ i, (Polynomial.eval t (Polynomial.X - Polynomial.C ((hA.eigenvalues i : ℝ) : 𝕜))) := by
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]

/-- **Vieta for a Hermitian spectrum.**  Every elementary symmetric function of the eigenvalues is,
up to sign, a coefficient of the characteristic polynomial. -/
theorem isHermitian_esymm_eigenvalues_eq_coeff {A : Matrix I I 𝕜} (hA : A.IsHermitian) {j : ℕ}
    (hj : j ≤ Fintype.card I) :
    (Multiset.map (fun i => ((hA.eigenvalues i : ℝ) : 𝕜)) Finset.univ.val).esymm j
      = (-1) ^ j * A.charpoly.coeff (Fintype.card I - j) := by
  classical
  set s : Multiset 𝕜 := Multiset.map (fun i => ((hA.eigenvalues i : ℝ) : 𝕜)) Finset.univ.val with hs
  have hcard : s.card = Fintype.card I := by
    rw [hs, Multiset.card_map]
    rfl
  have hprod : A.charpoly = (Multiset.map (fun t => Polynomial.X - Polynomial.C t) s).prod := by
    rw [isHermitian_charpoly_eq_prod hA, hs, Multiset.map_map]
    rfl
  have hle : Fintype.card I - j ≤ s.card := by
    rw [hcard]
    exact Nat.sub_le _ _
  have hcoeff := Multiset.prod_X_sub_C_coeff s hle
  rw [← hprod, hcard] at hcoeff
  have hsub : Fintype.card I - (Fintype.card I - j) = j := by omega
  rw [hsub] at hcoeff
  rw [hcoeff, ← mul_assoc, ← pow_add]
  have hsign : ((-1 : 𝕜)) ^ j * (-1) ^ j = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  calc s.esymm j = 1 * s.esymm j := (one_mul _).symm
    _ = ((-1 : 𝕜) ^ j * (-1) ^ j) * s.esymm j := by rw [hsign]
    _ = (-1 : 𝕜) ^ (j + j) * s.esymm j := by rw [← pow_add]

end GaloisForLFunctions.HTGeometry
