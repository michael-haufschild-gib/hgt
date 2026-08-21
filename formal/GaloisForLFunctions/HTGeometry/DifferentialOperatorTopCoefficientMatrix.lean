import GaloisForLFunctions.HTGeometry.DifferentialOperatorOre
import Mathlib.Data.Matrix.Basic

/-!
# The leading matrix of an invertible operator matrix of positive degree is singular

For skew polynomials the top coefficient of a product is the product of the top coefficients:
`(a ∂^d)(b ∂^e) = a b ∂^{d+e} + (lower)`, because commuting `∂^d` past `b` changes only the lower
terms.  Entrywise this makes the *leading matrix* `A_d = (coeff (A i j) d)` multiplicative:
`(A B)_{d+e} = A_d · B_e` whenever the entries of `A` and `B` have degrees at most `d` and `e`.

Applying it to `A B = 1` with `d + e > 0` gives `A_d · B_e = 0`, so a matrix of operators which is
invertible over the operator ring and has an entry of positive degree has a *singular* leading
matrix.  This is the first structural constraint of the slope theory of such matrices: the degree
of a product can drop only along the kernel of the leading matrix.

* `coeff_dpartial_iterate_at`, `coeff_mul_of_degree_le` — the bounded top-coefficient law;
* `topCoeffMatrix`, `topCoeffMatrix_mul`;
* `not_isUnit_topCoeffMatrix`.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

namespace DiffOp

noncomputable section

variable {K : Type u} [CommRing K] [Differential K]

theorem coeff_dpartial_iterate_at (n : ℕ) (q : DiffOp K) {e : ℕ} (he : degree q ≤ e) :
    coeff (dpartial^[n] q) (n + e) = coeff q e := by
  rcases eq_or_lt_of_le he with heq | hlt
  · have hidx : n + e = degree q + n := by omega
    rw [hidx, coeff_dpartial_iterate_top, leadCoeff, heq]
  · have h1 : coeff (dpartial^[n] q) (n + e) = 0 :=
      coeff_eq_zero_of_degree_lt
        (lt_of_le_of_lt (degree_dpartial_iterate_le n q) (by omega))
    have h2 : coeff q e = 0 := coeff_eq_zero_of_degree_lt hlt
    rw [h1, h2]

/-- **The top coefficient of a product, with degree bounds.** -/
theorem coeff_mul_of_degree_le {p q : DiffOp K} {d e : ℕ} (hp : degree p ≤ d)
    (hq : degree q ≤ e) : coeff (p * q) (d + e) = coeff p d * coeff q e := by
  classical
  rw [coeff_mul]
  by_cases hd : d ∈ (toFinsupp p).support
  · refine (Finset.sum_eq_single_of_mem d hd ?_).trans ?_
    · intro n hn hne
      have hnle : n ≤ degree p := Finset.le_sup (f := id) hn
      have hlt : degree (dpartial^[n] q) < d + e :=
        lt_of_le_of_lt (degree_dpartial_iterate_le n q) (by omega)
      rw [coeff_eq_zero_of_degree_lt hlt, mul_zero]
    · rw [show d + e = d + e from rfl, coeff_dpartial_iterate_at d q hq]
  · have hzero : coeff p d = 0 := by
      by_contra hcon
      exact hd (Finsupp.mem_support_iff.mpr hcon)
    rw [hzero, zero_mul]
    refine Finset.sum_eq_zero fun n hn => ?_
    have hnle : n ≤ degree p := Finset.le_sup (f := id) hn
    have hne : n ≠ d := by
      intro hcon
      exact hd (hcon ▸ hn)
    have hlt : degree (dpartial^[n] q) < d + e :=
      lt_of_le_of_lt (degree_dpartial_iterate_le n q) (by omega)
    rw [coeff_eq_zero_of_degree_lt hlt, mul_zero]

variable {ι : Type*}

/-- The matrix of coefficients at a fixed order. -/
def topCoeffMatrix (A : Matrix ι ι (DiffOp K)) (d : ℕ) : Matrix ι ι K :=
  Matrix.of fun i j => coeff (A i j) d

@[simp] theorem topCoeffMatrix_apply (A : Matrix ι ι (DiffOp K)) (d : ℕ) (i j : ι) :
    topCoeffMatrix A d i j = coeff (A i j) d := rfl

/-- **The leading matrix is multiplicative.** -/
theorem topCoeffMatrix_mul [Fintype ι] (A B : Matrix ι ι (DiffOp K)) (d e : ℕ)
    (hA : ∀ i j, degree (A i j) ≤ d) (hB : ∀ i j, degree (B i j) ≤ e) :
    topCoeffMatrix (A * B) (d + e) = topCoeffMatrix A d * topCoeffMatrix B e := by
  ext i j
  show coeff ((A * B) i j) (d + e) = ∑ k, coeff (A i k) d * coeff (B k j) e
  have hentry : (A * B) i j = ∑ k, A i k * B k j := by
    rw [Matrix.mul_apply]
  rw [hentry, ← coeffAddHom_apply (d + e), map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [coeffAddHom_apply]
  exact coeff_mul_of_degree_le (hA i k) (hB k j)

/-- **A matrix of operators invertible over the operator ring with an entry of positive degree has
a singular leading matrix.** -/
theorem not_isUnit_topCoeffMatrix [Fintype ι] [DecidableEq ι] [Nontrivial K]
    {A B : Matrix ι ι (DiffOp K)} (hAB : A * B = 1) {d e : ℕ}
    (hA : ∀ i j, degree (A i j) ≤ d) (hB : ∀ i j, degree (B i j) ≤ e)
    (hpos : 0 < d + e) (hBne : topCoeffMatrix B e ≠ 0) :
    ¬ IsUnit (topCoeffMatrix A d) := by
  have hprod : topCoeffMatrix A d * topCoeffMatrix B e = 0 := by
    rw [← topCoeffMatrix_mul A B d e hA hB, hAB]
    ext i j
    show coeff ((1 : Matrix ι ι (DiffOp K)) i j) (d + e) = 0
    by_cases hij : i = j
    · rw [hij, Matrix.one_apply_eq]
      show coeff (mono 0 1 : DiffOp K) (d + e) = 0
      rw [coeff_mono_of_ne]
      omega
    · rw [Matrix.one_apply_ne hij]
      rw [coeff_zero]
  intro hunit
  obtain ⟨U, hU⟩ := hunit
  refine hBne ?_
  have hstep : (↑U⁻¹ : Matrix ι ι K) * (topCoeffMatrix A d * topCoeffMatrix B e)
      = (↑U⁻¹ : Matrix ι ι K) * 0 := by rw [hprod]
  rw [mul_zero, ← mul_assoc, ← hU, Units.inv_mul, one_mul] at hstep
  exact hstep

end

end DiffOp

end GaloisForLFunctions.HTGeometry
