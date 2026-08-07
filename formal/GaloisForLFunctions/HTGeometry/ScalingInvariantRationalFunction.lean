import Mathlib

/-!
# Scaling-invariant rational functions are constants

If a coprime pair of polynomials satisfies the cross identity produced by invariance of `P/Q` under
the substitution `X ↦ aX`, then `P` and `Q` are constants, provided the powers of `a` are pairwise
distinct.

The mechanism: coprimality turns the cross identity into `P ∣ P(aX)`, and the two sides have the
same degree, so `P(aX) = λP` with `λ = a^{deg P}`; comparing coefficients leaves one index, so `P`
is a monomial, and likewise `Q`.  The cross identity forces the two scalars to agree, hence the two
degrees, and two coprime monomials of the same degree have degree zero.

One scalar with pairwise distinct powers is enough — in characteristic zero, `a = 2`.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

variable {L : Type*} [Field L]

/-- The scalar of a scaling eigenvector is the corresponding power. -/
theorem scaling_eigenvalue_eq_pow {a : L} {P : Polynomial L} (hP0 : P ≠ 0) {lam : L}
    (h : P.comp (Polynomial.C a * Polynomial.X) = Polynomial.C lam * P) :
    lam = a ^ P.natDegree := by
  have hlead : P.coeff P.natDegree ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hP0
  have hc := congrArg (fun R : Polynomial L => R.coeff P.natDegree) h
  simp only [Polynomial.comp_C_mul_X_coeff, Polynomial.coeff_C_mul] at hc
  rw [mul_comm] at hc
  exact (mul_right_cancel₀ hlead hc).symm

/-- A polynomial fixed up to a scalar by the substitution `X ↦ aX` is a monomial. -/
theorem eq_monomial_of_comp_scaling {a : L}
    (hsep : ∀ i j : ℕ, i ≠ j → a ^ i ≠ a ^ j) {P : Polynomial L} {lam : L}
    (h : P.comp (Polynomial.C a * Polynomial.X) = Polynomial.C lam * P) :
    P = Polynomial.C (P.coeff P.natDegree) * Polynomial.X ^ P.natDegree := by
  classical
  rcases eq_or_ne P 0 with rfl | hP0
  · simp
  have hlam : lam = a ^ P.natDegree := scaling_eigenvalue_eq_pow hP0 h
  have hcoeff : ∀ i : ℕ, P.coeff i * a ^ i = lam * P.coeff i := by
    intro i
    have hc := congrArg (fun R : Polynomial L => R.coeff i) h
    simpa only [Polynomial.comp_C_mul_X_coeff, Polynomial.coeff_C_mul] using hc
  ext i
  rcases eq_or_ne i P.natDegree with rfl | hi
  · simp
  · have hzero : P.coeff i = 0 := by
      by_contra hne
      have hc := hcoeff i
      rw [hlam, mul_comm (a ^ P.natDegree)] at hc
      exact hsep i P.natDegree hi (mul_right_cancel₀ hne hc)
    simp [hzero, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, hi]

/-- The substitution `X ↦ aX` preserves degrees. -/
theorem natDegree_comp_scaling {a : L} (ha : a ≠ 0) (R : Polynomial L) :
    (R.comp (Polynomial.C a * Polynomial.X)).natDegree = R.natDegree := by
  rcases eq_or_ne R 0 with rfl | hR
  · simp
  · rw [Polynomial.natDegree_comp, Polynomial.natDegree_C_mul_X a ha, mul_one]

/-- The substitution `X ↦ aX` does not annihilate a nonzero polynomial. -/
theorem comp_scaling_ne_zero {a : L} (ha : a ≠ 0) {R : Polynomial L} (hR : R ≠ 0) :
    R.comp (Polynomial.C a * Polynomial.X) ≠ 0 := by
  intro hc
  have h0 := congrArg (fun T : Polynomial L => T.coeff R.natDegree) hc
  simp only [Polynomial.comp_C_mul_X_coeff, Polynomial.coeff_zero] at h0
  exact mul_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hR) (pow_ne_zero _ ha) h0

/-- A polynomial dividing its own scaling is a scaling eigenvector. -/
theorem exists_scaling_eigenvalue {a : L} (ha : a ≠ 0) {R : Polynomial L} (hR : R ≠ 0)
    (hdvd : R ∣ R.comp (Polynomial.C a * Polynomial.X)) :
    ∃ lam : L, R.comp (Polynomial.C a * Polynomial.X) = Polynomial.C lam * R := by
  obtain ⟨S, hS⟩ := hdvd
  have hSne : S ≠ 0 := by
    intro h
    rw [h, mul_zero] at hS
    exact comp_scaling_ne_zero ha hR hS
  have hdeg : S.natDegree = 0 := by
    have h1 := natDegree_comp_scaling ha R
    rw [hS, Polynomial.natDegree_mul hR hSne] at h1
    omega
  refine ⟨S.coeff 0, ?_⟩
  rw [hS, Polynomial.eq_C_of_natDegree_eq_zero hdeg]
  ring

/-- **A scaling-invariant coprime fraction has constant numerator and denominator.** -/
theorem natDegree_eq_zero_of_scaling_invariant {a : L} (ha : a ≠ 0)
    (hsep : ∀ i j : ℕ, i ≠ j → a ^ i ≠ a ^ j)
    {P Q : Polynomial L} (hP0 : P ≠ 0) (hQ0 : Q ≠ 0) (hcop : IsCoprime P Q)
    (heq : P.comp (Polynomial.C a * Polynomial.X) * Q
      = P * Q.comp (Polynomial.C a * Polynomial.X)) :
    P.natDegree = 0 ∧ Q.natDegree = 0 := by
  classical
  have hdvdP : P ∣ P.comp (Polynomial.C a * Polynomial.X) :=
    hcop.dvd_of_dvd_mul_right ⟨Q.comp (Polynomial.C a * Polynomial.X), heq⟩
  have hdvdQ : Q ∣ Q.comp (Polynomial.C a * Polynomial.X) :=
    hcop.symm.dvd_of_dvd_mul_right
      ⟨P.comp (Polynomial.C a * Polynomial.X), by linear_combination -heq⟩
  obtain ⟨lamP, hlamP⟩ := exists_scaling_eigenvalue ha hP0 hdvdP
  obtain ⟨lamQ, hlamQ⟩ := exists_scaling_eigenvalue ha hQ0 hdvdQ
  have hPmon := eq_monomial_of_comp_scaling hsep hlamP
  have hQmon := eq_monomial_of_comp_scaling hsep hlamQ
  -- the two eigenvalues agree, hence the two degrees
  have hlamEq : lamP = lamQ := by
    have h1 : Polynomial.C lamP * (P * Q) = Polynomial.C lamQ * (P * Q) := by
      have h2 : Polynomial.C lamP * P * Q = P * (Polynomial.C lamQ * Q) := by
        rw [← hlamP, ← hlamQ]; exact heq
      linear_combination h2
    have hPQ : P * Q ≠ 0 := mul_ne_zero hP0 hQ0
    have := mul_right_cancel₀ hPQ h1
    exact Polynomial.C_injective this
  have hdegEq : P.natDegree = Q.natDegree := by
    have h1 := scaling_eigenvalue_eq_pow hP0 hlamP
    have h2 := scaling_eigenvalue_eq_pow hQ0 hlamQ
    by_contra hne
    exact hsep P.natDegree Q.natDegree hne (by rw [← h1, ← h2, hlamEq])
  -- two coprime monomials of the same degree have degree zero
  have hzero : P.natDegree = 0 := by
    by_contra hd
    have hdvdXP : (Polynomial.X : Polynomial L) ∣ P := by
      rw [hPmon]; exact Dvd.dvd.mul_left (dvd_pow_self _ hd) _
    have hdvdXQ : (Polynomial.X : Polynomial L) ∣ Q := by
      rw [hQmon]; exact Dvd.dvd.mul_left (dvd_pow_self _ (hdegEq ▸ hd)) _
    exact (Polynomial.not_isUnit_X (R := L)) (hcop.isUnit_of_dvd' hdvdXP hdvdXQ)
  exact ⟨hzero, hdegEq ▸ hzero⟩

end GaloisForLFunctions.HTGeometry
