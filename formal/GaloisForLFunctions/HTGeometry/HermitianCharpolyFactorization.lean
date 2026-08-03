import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem

/-!
# Vieta for a Hermitian spectrum

Mathlib factors the characteristic polynomial of a Hermitian matrix over its eigenvalues
(`Matrix.IsHermitian.charpoly_eq`).  Comparing coefficients with Vieta's formulas identifies every
elementary symmetric function of the eigenvalues with a coefficient of the characteristic
polynomial, with no injectivity assumption on the spectrum.

This is what turns a symmetric expression in the spectrum into a polynomial in the matrix entries.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

variable {𝕜 : Type*} [RCLike 𝕜] {I : Type*} [Fintype I] [DecidableEq I]

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
    rw [hA.charpoly_eq, hs, Multiset.map_map]
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
