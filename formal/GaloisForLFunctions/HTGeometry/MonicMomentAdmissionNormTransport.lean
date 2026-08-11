import GaloisForLFunctions.HTGeometry.MonicMomentAdmission

/-!
# Division-free norm transport for canonical monic moment admission

The inverse-Hankel admission is orthogonal to every lower polynomial whenever its leading solve
block is nonsingular.  This file computes the Euler transport of its square without positivity or
Jacobi quotients.  The resulting raw norm-flux identity continues to make sense when the next
Hankel face becomes singular.
-/

open scoped BigOperators
open Polynomial

namespace HTGeometry

noncomputable section

/-- The canonical inverse-Hankel admission is orthogonal to every polynomial of lower degree. -/
theorem momentInner_monicMomentAdmission_lower_eq_zero
    {s : ℕ → ℝ} {n : ℕ} (hdet : (momentHankelMatrix s n).det ≠ 0)
    {q : Polynomial ℝ} (hq : q.natDegree < n) :
    momentInner s (monicMomentAdmissionPolynomial s n) q = 0 := by
  let b : Fin n → ℝ := Polynomial.toFn n q
  have hqof : Polynomial.ofFn n b = q :=
    Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt hq
  rw [← hqof, momentInner_def, Polynomial.ofFn_eq_sum_monomial,
    Finset.mul_sum, momentFunctional_finset_sum]
  apply Finset.sum_eq_zero
  intro i _
  have hz := momentFunctional_X_pow_mul_monicMomentAdmissionPolynomial_eq_zero hdet i
  have hpoly :
      monicMomentAdmissionPolynomial s n * Polynomial.monomial (i : ℕ) (b i) =
        (b i) • (X ^ (i : ℕ) * monicMomentAdmissionPolynomial s n) := by
    simp only [Polynomial.smul_eq_C_mul, ← Polynomial.C_mul_X_pow_eq_monomial]
    ring
  rw [hpoly, momentFunctional_smul, hz, mul_zero]

/-- Lower remainder after removing two visible top jets from `X²(P_n^sharp)'`. -/
def monicMomentAdmissionNormRemainder (s : ℕ → ℝ) (n : ℕ) : Polynomial ℝ :=
  let P := monicMomentAdmissionPolynomial s n
  X ^ 2 * P.derivative - (n : ℝ) • (X * P) + P.coeff (n - 1) • P

/-- The top two coefficients cancel identically in the canonical norm remainder. -/
theorem monicMomentAdmissionNormRemainder_degree_lt
    (s : ℕ → ℝ) {n : ℕ} (hn : 0 < n) :
    (monicMomentAdmissionNormRemainder s n).degree < (n : WithBot ℕ) := by
  let P := monicMomentAdmissionPolynomial s n
  have hPmonic : P.Monic := monicMomentAdmissionPolynomial_monic s n
  have hPdeg : P.natDegree = n := monicMomentAdmissionPolynomial_natDegree s n
  have htop : P.coeff n = 1 := by
    simpa only [hPdeg] using hPmonic.coeff_natDegree
  rw [Polynomial.degree_lt_iff_coeff_zero]
  intro k hk
  have hnk : n ≤ k := by exact_mod_cast hk
  by_cases hkn : k = n
  · subst k
    simp only [monicMomentAdmissionNormRemainder, Polynomial.coeff_add,
      Polynomial.coeff_sub, Polynomial.coeff_smul]
    by_cases hn1 : n = 1
    · have htop1' : (monicMomentAdmissionPolynomial s 1).coeff 1 = 1 := by
        simpa only [monicMomentAdmissionPolynomial_natDegree] using
          (monicMomentAdmissionPolynomial_monic s 1).coeff_natDegree
      rw [hn1, Polynomial.coeff_X_pow_mul', if_neg (by omega : ¬2 ≤ 1),
        Polynomial.coeff_X_mul]
      simp only [Nat.cast_one, one_smul, htop1']
      ring
    · have hn2 : 2 ≤ n := by omega
      rw [Polynomial.coeff_X_pow_mul', if_pos hn2, Polynomial.coeff_derivative]
      rw [show X * P = X ^ 1 * P by simp,
        Polynomial.coeff_X_pow_mul', if_pos (by omega : 1 ≤ n)]
      have hidx : n - 2 + 1 = n - 1 := by omega
      rw [hidx, htop]
      have hcast : ((n - 2 : ℕ) : ℝ) + 1 = ((n - 1 : ℕ) : ℝ) := by
        rw [Nat.cast_sub (by omega : 2 ≤ n), Nat.cast_sub (by omega : 1 ≤ n)]
        ring
      rw [hcast]
      change P.coeff (n - 1) * ((n - 1 : ℕ) : ℝ) -
        (n : ℝ) • P.coeff (n - 1) + P.coeff (n - 1) • 1 = 0
      have hprevcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ n)]
        norm_num
      rw [hprevcast]
      ring
  · have hnk' : n < k := lt_of_le_of_ne hnk (Ne.symm hkn)
    by_cases hk1 : k = n + 1
    · subst k
      have hhigh : P.coeff (n + 1) = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt (hPdeg.symm ▸ Nat.lt_succ_self n)
      simp only [monicMomentAdmissionNormRemainder, Polynomial.coeff_add,
        Polynomial.coeff_sub, Polynomial.coeff_smul]
      rw [Polynomial.coeff_X_pow_mul', if_pos (by omega : 2 ≤ n + 1),
        Polynomial.coeff_derivative]
      rw [show X * P = X ^ 1 * P by simp,
        Polynomial.coeff_X_pow_mul', if_pos (by omega : 1 ≤ n + 1)]
      have hidx : n + 1 - 2 + 1 = n := by omega
      have hidx' : n + 1 - 1 = n := by omega
      rw [hidx, hidx', htop, hhigh]
      push_cast
      have hcast : ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) := by
        rw [Nat.cast_sub (by omega : 1 ≤ n)]
        norm_num
      rw [hcast]
      ring
    · have hklarge : n + 1 < k := by omega
      have hk2 : 2 ≤ k := by omega
      have hprev : P.coeff (k - 1) = 0 := by
        apply Polynomial.coeff_eq_zero_of_natDegree_lt
        rw [hPdeg]
        omega
      have hcur : P.coeff k = 0 := by
        apply Polynomial.coeff_eq_zero_of_natDegree_lt
        rw [hPdeg]
        omega
      simp only [monicMomentAdmissionNormRemainder, Polynomial.coeff_add,
        Polynomial.coeff_sub, Polynomial.coeff_smul]
      rw [Polynomial.coeff_X_pow_mul', if_pos hk2, Polynomial.coeff_derivative]
      rw [show X * P = X ^ 1 * P by simp,
        Polynomial.coeff_X_pow_mul', if_pos (by omega : 1 ≤ k)]
      have hidx : k - 2 + 1 = k - 1 := by omega
      rw [hidx, hprev, hcur]
      ring

/-- Euler transport of the canonical admission square in division-free norm/odd-current
coordinates.  Only nonsingularity of the leading solve block is used. -/
theorem momentFunctional_X_shiftedEuler_one_sq_monicMomentAdmission
    {s : ℕ → ℝ} {n : ℕ} (hn : 0 < n)
    (hdet : (momentHankelMatrix s n).det ≠ 0) :
    let P := monicMomentAdmissionPolynomial s n
    momentFunctional s (X * (X * (P ^ 2).derivative + P ^ 2)) =
      ((2 * n + 1 : ℕ) : ℝ) * momentInner s P (X * P) -
        2 * P.coeff (n - 1) * momentInner s P P := by
  dsimp only
  let P := monicMomentAdmissionPolynomial s n
  let R := monicMomentAdmissionNormRemainder s n
  have hRdeg : R.natDegree < n := by
    by_cases hRzero : R = 0
    · rw [hRzero, Polynomial.natDegree_zero]
      exact hn
    · exact (Polynomial.natDegree_lt_iff_degree_lt hRzero).mpr (by
        simpa only [R] using monicMomentAdmissionNormRemainder_degree_lt s hn)
  have hRzero : momentInner s P R = 0 :=
    momentInner_monicMomentAdmission_lower_eq_zero hdet hRdeg
  have hpoly :
      X * (X * (P ^ 2).derivative + P ^ 2) =
        (2 : ℝ) • (P * R) +
          (((2 * n + 1 : ℕ) : ℝ)) • (P * (X * P)) +
        (-(2 * P.coeff (n - 1))) • (P * P) := by
    simp only [R, monicMomentAdmissionNormRemainder, P, pow_two,
      Polynomial.derivative_mul, Polynomial.smul_eq_C_mul]
    push_cast
    simp only [map_add, map_mul, map_neg, map_one, map_ofNat]
    ring
  rw [hpoly, momentFunctional_add, momentFunctional_add,
    momentFunctional_smul, momentFunctional_smul, momentFunctional_smul,
    ← momentInner_def, ← momentInner_def, ← momentInner_def, hRzero]
  ring

end

end HTGeometry
