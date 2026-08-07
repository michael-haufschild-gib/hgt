import Mathlib

/-!
# Scaling-invariant rational functions are constants

If a coprime pair of polynomials satisfies the cross identity produced by invariance of `P/Q` under
the substitution `X ↦ aX`, then `P` and `Q` are constants, provided the powers of `a` are pairwise
distinct.

The mechanism: coprimality turns the cross identity into `P ∣ P(aX)`, and the two sides have the
same degree, so `P(aX) = λP`.  Comparing coefficients gives `aⁱ = λ` for every index carrying a
nonzero coefficient, so only one index survives and `P` is a monomial; the same for `Q`.  Two
coprime monomials have degree zero.

One scalar with pairwise distinct powers is enough — in characteristic zero, `a = 2`.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

variable {L : Type*} [Field L]

/-- A polynomial fixed up to a scalar by the substitution `X ↦ aX` is a monomial. -/
theorem eq_monomial_of_comp_scaling {a : L}
    (hsep : ∀ i j : ℕ, i ≠ j → a ^ i ≠ a ^ j) {P : Polynomial L} {lam : L}
    (h : P.comp (Polynomial.C a * Polynomial.X) = Polynomial.C lam * P) :
    P = Polynomial.C (P.coeff P.natDegree) * Polynomial.X ^ P.natDegree := by
  classical
  rcases eq_or_ne P 0 with rfl | hP0
  · simp
  have hcoeff : ∀ i : ℕ, a ^ i * P.coeff i = lam * P.coeff i := by
    intro i
    have := congrArg (fun R : Polynomial L => R.coeff i) h
    simpa [Polynomial.comp_C_mul_X_coeff, Polynomial.coeff_C_mul] using this
  have hlead : P.coeff P.natDegree ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hP0
  have hlam : lam = a ^ P.natDegree := by
    have := hcoeff P.natDegree
    field_simp at this
    rcases this with h1 | h1
    · exact h1.symm
    · exact absurd h1 hlead
  ext i
  rcases eq_or_ne i P.natDegree with rfl | hi
  · simp
  · have hzero : P.coeff i = 0 := by
      by_contra hne
      have := hcoeff i
      rw [hlam] at this
      have hpow : a ^ i = a ^ P.natDegree := by
        field_simp at this
        rcases this with h1 | h1
        · exact h1
        · exact absurd h1 hne
      exact hsep i P.natDegree hi hpow
    simp [hzero, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, hi]

/-- **A scaling-invariant coprime fraction has constant numerator and denominator.** -/
theorem natDegree_eq_zero_of_scaling_invariant {a : L} (ha : a ≠ 0)
    (hsep : ∀ i j : ℕ, i ≠ j → a ^ i ≠ a ^ j)
    {P Q : Polynomial L} (hP0 : P ≠ 0) (hQ0 : Q ≠ 0) (hcop : IsCoprime P Q)
    (heq : P.comp (Polynomial.C a * Polynomial.X) * Q
      = P * Q.comp (Polynomial.C a * Polynomial.X)) :
    P.natDegree = 0 ∧ Q.natDegree = 0 := by
  classical
  have hscale : ∀ R : Polynomial L, (R.comp (Polynomial.C a * Polynomial.X)).natDegree
      = R.natDegree := by
    intro R
    rcases eq_or_ne R 0 with rfl | hR
    · simp
    · rw [Polynomial.natDegree_comp]
      have : (Polynomial.C a * Polynomial.X : Polynomial L).natDegree = 1 := by
        rw [Polynomial.natDegree_C_mul_X a ha]
      rw [this, mul_one]
  -- the numerator is fixed up to a scalar
  have hdvdP : P ∣ P.comp (Polynomial.C a * Polynomial.X) := by
    refine (IsCoprime.dvd_of_dvd_mul_right hcop ?_)
    exact ⟨Q.comp (Polynomial.C a * Polynomial.X), by rw [← heq]; ring⟩
  have hdvdQ : Q ∣ Q.comp (Polynomial.C a * Polynomial.X) := by
    refine (IsCoprime.dvd_of_dvd_mul_right hcop.symm ?_)
    exact ⟨P.comp (Polynomial.C a * Polynomial.X), by rw [heq]; ring⟩
  have hconst : ∀ R : Polynomial L, R ≠ 0 → R ∣ R.comp (Polynomial.C a * Polynomial.X) →
      ∃ lam : L, R.comp (Polynomial.C a * Polynomial.X) = Polynomial.C lam * R := by
    intro R hR ⟨S, hS⟩
    have hSne : S ≠ 0 := by
      intro h
      rw [h, mul_zero] at hS
      have hcompne : R.comp (Polynomial.C a * Polynomial.X) ≠ 0 := by
        intro hc
        have := hscale R
        rw [hc] at this
        simp only [Polynomial.natDegree_zero] at this
        exact hR (Polynomial.eq_zero_of_natDegree_eq_zero_of_coeff_zero R this.symm ▸ hR |>.elim)
      exact hcompne hS
    have hdeg : S.natDegree = 0 := by
      have h1 := hscale R
      rw [hS, Polynomial.natDegree_mul hR hSne] at h1
      omega
    refine ⟨S.coeff 0, ?_⟩
    rw [hS, Polynomial.eq_C_of_natDegree_eq_zero hdeg]
    ring
  obtain ⟨lamP, hlamP⟩ := hconst P hP0 hdvdP
  obtain ⟨lamQ, hlamQ⟩ := hconst Q hQ0 hdvdQ
  have hPmon := eq_monomial_of_comp_scaling hsep hlamP
  have hQmon := eq_monomial_of_comp_scaling hsep hlamQ
  -- two coprime monomials have degree zero
  constructor
  · by_contra hd
    have hdvd : (Polynomial.X : Polynomial L) ∣ P := by
      rw [hPmon]
      exact Dvd.dvd.mul_left (dvd_pow_self _ hd) _
    have hdvd' : (Polynomial.X : Polynomial L) ∣ Q := by
      have hQdeg : Q.natDegree ≠ 0 := by
        by_contra hQd
        have hQC := Polynomial.eq_C_of_natDegree_eq_zero (Nat.eq_zero_of_not_pos
          (by omega : ¬ 0 < Q.natDegree) ▸ (by omega : Q.natDegree = 0))
        exact absurd rfl hQd
      rw [hQmon]
      exact Dvd.dvd.mul_left (dvd_pow_self _ hQdeg) _
    exact (Polynomial.not_isUnit_X (R := L)) (hcop.isUnit_of_dvd' hdvd hdvd')
  · by_contra hd
    have hdvd' : (Polynomial.X : Polynomial L) ∣ Q := by
      rw [hQmon]
      exact Dvd.dvd.mul_left (dvd_pow_self _ hd) _
    have hdvd : (Polynomial.X : Polynomial L) ∣ P := by
      have hPdeg : P.natDegree ≠ 0 := by
        by_contra hPd
        exact absurd rfl hPd
      rw [hPmon]
      exact Dvd.dvd.mul_left (dvd_pow_self _ hPdeg) _
    exact (Polynomial.not_isUnit_X (R := L)) (hcop.isUnit_of_dvd' hdvd hdvd')

end GaloisForLFunctions.HTGeometry
