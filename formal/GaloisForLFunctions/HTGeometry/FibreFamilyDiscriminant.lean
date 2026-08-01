import GaloisForLFunctions.HTGeometry.PrimeNonSquare
import Mathlib.Algebra.MvPolynomial.Division

/-!
# The fibre family and its discriminant

The fibre equation with indeterminate coefficients, `q a^{n+1} - ∑_{j<n} c_j a^j`, specialises at
`q = 1`, `c_1 = 1` and all other coefficients zero to `a^{n+1} - a`, which is separable.  So its
discriminant does not vanish there, and in particular is not divisible by `c_0`.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

universe u

variable (K : Type u) [CommRing K]

/-- **The fibre equation with indeterminate coefficients**: the variable `X n` is the leading
coefficient `q` and the variables `X j` for `j < n` are the coefficients `c_j`. -/
noncomputable def fibreFamily (n : ℕ) : Polynomial (MvPolynomial ℕ K) :=
  Polynomial.C (MvPolynomial.X n) * Polynomial.X ^ (n + 1)
    - ∑ j ∈ Finset.range n, Polynomial.C (MvPolynomial.X j) * Polynomial.X ^ j

/-- The specialisation sending the leading coefficient and `c_1` to one and every other coefficient
to zero. -/
noncomputable def fibreSpecialisation (n : ℕ) : MvPolynomial ℕ K →+* K :=
  MvPolynomial.eval (fun i => if i = n then 1 else if i = 1 then 1 else 0)

/-- **The specialised fibre equation is `a^{n+1} - a`.** -/
theorem map_fibreFamily {n : ℕ} (hn : 2 ≤ n) :
    (fibreFamily K n).map (fibreSpecialisation K n)
      = Polynomial.X ^ (n + 1) - Polynomial.X := by
  rw [fibreFamily, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_C, Polynomial.map_sum]
  congr 1
  · rw [fibreSpecialisation, MvPolynomial.eval_X, if_pos rfl, map_one, one_mul]
  · rw [Finset.sum_eq_single 1]
    · rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X, pow_one,
        fibreSpecialisation, MvPolynomial.eval_X, if_neg (by omega), if_pos rfl, map_one, one_mul]
    · intro b hb hb1
      rw [Polynomial.map_mul, Polynomial.map_C, fibreSpecialisation, MvPolynomial.eval_X,
        if_neg (by simp at hb; omega), if_neg hb1, map_zero, zero_mul]
    · intro hc
      exact absurd (Finset.mem_range.2 (by omega)) hc

/-- The degree of the fibre family is `n + 1`. -/
theorem natDegree_fibreFamily [Nontrivial K] {n : ℕ} :
    (fibreFamily K n).natDegree = n + 1 := by
  rw [fibreFamily, Polynomial.natDegree_sub_eq_left_of_natDegree_lt, Polynomial.natDegree_C_mul_X_pow]
  · exact MvPolynomial.X_ne_zero n
  · have hsum : (∑ j ∈ Finset.range n, Polynomial.C (MvPolynomial.X j) * Polynomial.X ^ j :
        Polynomial (MvPolynomial ℕ K)).natDegree ≤ n :=
      Polynomial.natDegree_sum_le_of_forall_le _ _ (fun j hj =>
        le_trans (Polynomial.natDegree_C_mul_X_pow_le _ _) (le_of_lt (Finset.mem_range.1 hj)))
    rw [Polynomial.natDegree_C_mul_X_pow _ _ (MvPolynomial.X_ne_zero n)]
    omega

/-- Its leading coefficient is the leading variable. -/
theorem leadingCoeff_fibreFamily [Nontrivial K] {n : ℕ} :
    (fibreFamily K n).leadingCoeff = MvPolynomial.X n := by
  rw [Polynomial.leadingCoeff, natDegree_fibreFamily, fibreFamily, Polynomial.coeff_sub,
    Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl, mul_one,
    Polynomial.finsetSum_coeff]
  have hzero : ∀ j ∈ Finset.range n,
      (Polynomial.C (MvPolynomial.X j) * Polynomial.X ^ j : Polynomial (MvPolynomial ℕ K)).coeff
        (n + 1) = 0 := by
    intro j hj
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg (by simp at hj; omega), mul_zero]
  rw [Finset.sum_congr rfl hzero, Finset.sum_const_zero, sub_zero]

/-! ## The discriminant of the family -/

section Field

variable {F : Type u} [Field F] [CharZero F]

omit [CharZero F] in
/-- **The specialisation kills the first coefficient.** -/
theorem fibreSpecialisation_X_zero {n : ℕ} (hn : 2 ≤ n) :
    fibreSpecialisation F n (MvPolynomial.X 0) = 0 := by
  rw [fibreSpecialisation, MvPolynomial.eval_X, if_neg (by omega), if_neg (by omega)]

/-- **The first coefficient does not divide the discriminant of the family.** -/
theorem not_X_zero_dvd_discr_fibreFamily {n : ℕ} (hn : 2 ≤ n) :
    ¬ (MvPolynomial.X 0 ∣ (fibreFamily F n).discr) := by
  have hdegF : (fibreFamily F n).natDegree = n + 1 := natDegree_fibreFamily F
  have hpos : 0 < (fibreFamily F n).degree := by
    rw [← Polynomial.natDegree_pos_iff_degree_pos, hdegF]
    omega
  have hmap := map_fibreFamily F hn
  have hdegmap : ((fibreFamily F n).map (fibreSpecialisation F n)).natDegree
      = (fibreFamily F n).natDegree := by
    rw [hmap, hdegF, Polynomial.natDegree_sub_eq_left_of_natDegree_lt, Polynomial.natDegree_X_pow]
    rw [Polynomial.natDegree_X_pow, Polynomial.natDegree_X]
    omega
  have hlc : fibreSpecialisation F n (fibreFamily F n).leadingCoeff ≠ 0 := by
    rw [leadingCoeff_fibreFamily, fibreSpecialisation, MvPolynomial.eval_X, if_pos rfl]
    exact one_ne_zero
  have hsep : ((fibreFamily F n).map (fibreSpecialisation F n)).Separable := by
    rw [hmap]
    exact separable_X_pow_succ_sub_X (by omega) (Nat.cast_ne_zero.2 (by omega))
  have hdiscmap : ((fibreFamily F n).map (fibreSpecialisation F n)).discr ≠ 0 := by
    refine discr_ne_zero_of_separable ?_ hsep
    rw [← Polynomial.natDegree_pos_iff_degree_pos, hdegmap, hdegF]
    omega
  rw [discr_map (fibreSpecialisation F n) hpos hdegmap hlc] at hdiscmap
  exact not_dvd_of_hom_ne_zero _ (fibreSpecialisation_X_zero hn) hdiscmap

/-- **The discriminant times the first coefficient is not a square.**  This is the statement that
excludes the quadratic subfield in the Kummer base change. -/
theorem not_isSquare_X_zero_mul_discr {n : ℕ} (hn : 2 ≤ n) :
    ¬ IsSquare (MvPolynomial.X 0 * (fibreFamily F n).discr) :=
  not_isSquare_of_prime_of_not_dvd MvPolynomial.X_prime (not_X_zero_dvd_discr_fibreFamily hn)

end Field

end GaloisForLFunctions.HTGeometry
