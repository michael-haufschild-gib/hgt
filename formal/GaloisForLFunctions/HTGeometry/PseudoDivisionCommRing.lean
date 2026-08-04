import GaloisForLFunctions.HTGeometry.DifferentialCharacteristicPseudoReduction

/-!
# Pseudo-division over a commutative ring

Dividing by a polynomial whose leading coefficient is not invertible still works after multiplying
the dividend by a power of that leading coefficient.  mathlib has division by a monic polynomial and
division over a field; this is the pseudo-division that works over an arbitrary commutative ring, in
the univariate case and at a distinguished variable of a multivariable ring.

The point of proving it over a ring rather than a field is that the multiplier is then explicitly a
power of the initial: no denominators are introduced, so a certificate obtained this way stays inside
the polynomial ring and its multiplier is controlled.
-/

namespace GaloisForLFunctions

open MvPolynomial

noncomputable section

/-- **Univariate pseudo-division over a commutative ring.** -/
theorem exists_pseudoDivision {R : Type*} [CommRing R] {q : Polynomial R}
    (hq : 0 < q.natDegree) (p : Polynomial R) :
    ∃ (e : ℕ) (a b : Polynomial R),
      Polynomial.C q.leadingCoeff ^ e * p = q * a + b ∧ b.natDegree < q.natDegree := by
  classical
  induction hn : p.natDegree using Nat.strong_induction_on generalizing p with
  | _ n ih =>
    by_cases hlt : p.natDegree < q.natDegree
    · exact ⟨0, 0, p, by simp, hlt⟩
    · push Not at hlt
      set d := p.natDegree with hd
      set m := q.natDegree with hm
      set p' : Polynomial R := Polynomial.C q.leadingCoeff * p -
        Polynomial.C p.leadingCoeff * (q * Polynomial.X ^ (d - m)) with hp'
      have hcoeff : ∀ k : ℕ, d ≤ k → p'.coeff k = 0 := by
        intro k hk
        rw [hp']
        simp only [Polynomial.coeff_sub, Polynomial.coeff_C_mul,
          Polynomial.coeff_mul_X_pow']
        rw [if_pos (by omega)]
        rcases lt_or_eq_of_le hk with hlt' | heq
        · have h1 : p.coeff k = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
          have h2 : q.coeff (k - (d - m)) = 0 :=
            Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
          rw [h1, h2]
          ring
        · rw [← heq]
          have h2 : d - (d - m) = m := by omega
          rw [h2]
          simp only [Polynomial.leadingCoeff, ← hd, ← hm]
          ring
      have hdlt : p'.natDegree < d := by
        by_contra hcon
        push Not at hcon
        have hne : p'.coeff p'.natDegree ≠ 0 := by
          intro h0
          have hp'0 : p' = 0 := Polynomial.leadingCoeff_eq_zero.1 h0
          rw [hp'0] at hcon
          simp only [Polynomial.natDegree_zero] at hcon
          omega
        exact hne (hcoeff _ hcon)
      obtain ⟨e, a, b, hab, hb⟩ := ih p'.natDegree (by omega) p' rfl
      refine ⟨e + 1, a + Polynomial.C q.leadingCoeff ^ e *
        (Polynomial.C p.leadingCoeff * Polynomial.X ^ (d - m)), b, ?_, hb⟩
      have hstep : Polynomial.C q.leadingCoeff ^ (e + 1) * p =
          Polynomial.C q.leadingCoeff ^ e * p' +
            Polynomial.C q.leadingCoeff ^ e *
              (Polynomial.C p.leadingCoeff * (q * Polynomial.X ^ (d - m))) := by
        rw [hp']
        ring
      rw [hstep, hab]
      ring

/-- **Pseudo-division at a distinguished variable, over a commutative ring.**  The multiplier is a
power of the initial at that variable, so the identity stays inside the polynomial ring. -/
theorem exists_mvPolynomial_pseudoDivision {R σ : Type*} [CommRing R] (i : σ)
    (Q D : MvPolynomial σ R) (hD : 0 < MvPolynomial.degreeOf i D) :
    ∃ (e : ℕ) (a b : MvPolynomial σ R),
      mvPolynomialInitialAt i D ^ e * Q = D * a + b ∧
        MvPolynomial.degreeOf i b < MvPolynomial.degreeOf i D := by
  classical
  set eq := mvPolynomialPolynomialEquivAt (K := R) i with heq
  have hDdeg : 0 < (eq D).natDegree := by
    rw [heq, mvPolynomialPolynomialEquivAt_apply,
      ← mvPolynomial_degreeOf_eq_natDegree_asPolynomialAt]
    exact hD
  obtain ⟨e, a, b, hab, hb⟩ := exists_pseudoDivision hDdeg (eq Q)
  refine ⟨e, eq.symm a, eq.symm b, ?_, ?_⟩
  · apply eq.injective
    rw [map_mul, map_add, map_mul, map_pow, AlgEquiv.apply_symm_apply,
      AlgEquiv.apply_symm_apply]
    rw [heq, mvPolynomialPolynomialEquivAt_initial]
    exact hab
  · have hbdeg : MvPolynomial.degreeOf i (eq.symm b) = b.natDegree := by
      rw [mvPolynomial_degreeOf_eq_natDegree_asPolynomialAt,
        ← mvPolynomialPolynomialEquivAt_apply, heq, AlgEquiv.apply_symm_apply]
    have hDdeg' : MvPolynomial.degreeOf i D = (eq D).natDegree := by
      rw [heq, mvPolynomialPolynomialEquivAt_apply,
        mvPolynomial_degreeOf_eq_natDegree_asPolynomialAt]
    rw [hbdeg, hDdeg']
    exact hb

open scoped Differential

/-- **The fresh-jet commutator, for an arbitrary index type.**  Differentiating in the jet `(i, n+1)`
after the total derivation equals total differentiation after that partial derivative, plus the
partial derivative in the jet `(i, n)`.  This is the corpus's scalar commutator, proved for a general
family of differential indeterminates so that it applies to a doubled jet ring. -/
theorem pderiv_succ_differentialPolynomialOverDerivation_family
    {ι K : Type*} [CommRing K] [Differential K] [DecidableEq ι] (i : ι) (n : ℕ)
    (P : DifferentialPolynomial ι K) :
    MvPolynomial.pderiv (i, n + 1) (differentialPolynomialOverDerivation ι K P) =
      differentialPolynomialOverDerivation ι K (MvPolynomial.pderiv (i, n + 1) P) +
        MvPolynomial.pderiv (i, n) P := by
  classical
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add P Q hP hQ =>
      simp only [map_add, hP, hQ]
      abel
  | mul_X P j hP =>
      rcases j with ⟨a, m⟩
      simp only [Derivation.leibniz, smul_eq_mul,
        differentialPolynomialOverDerivation_X]
      by_cases hai : a = i
      · subst hai
        by_cases hmn : m = n
        · subst hmn
          simp [MvPolynomial.pderiv_X]
          rw [hP]
          ring
        · by_cases hmtop : m = n + 1
          · subst hmtop
            have hne : n + 1 ≠ n := Nat.ne_of_gt (Nat.lt_succ_self n)
            simp [MvPolynomial.pderiv_X, Nat.add_comm]
            rw [hP]
            ring
          · simp only [MvPolynomial.pderiv_X, Prod.ext_iff, hmn, hmtop, and_true, and_false,
              if_false, ite_false]
            simp only [Pi.single_apply, Prod.mk.injEq, hmn, hmtop, and_false, if_false]
            rw [hP]
            ring
      · simp [MvPolynomial.pderiv_X, Prod.ext_iff, hai]
        rw [hP]
        ring

end

end GaloisForLFunctions
