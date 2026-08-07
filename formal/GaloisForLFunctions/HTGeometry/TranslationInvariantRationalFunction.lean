import GaloisForLFunctions.HTGeometry.ScalingInvariantRationalFunction

/-!
# Translation-invariant rational functions are constants

The additive analogue of the scaling statement.  In characteristic zero a single nonzero
translation already rigidifies: a polynomial fixed by `X ↦ X + c` is constant, because its
derivative is fixed too and a degree-one polynomial visibly moves.

Consequently a coprime pair satisfying the cross identity produced by invariance of `P/Q` under one
translation has constant numerator and denominator.

This is the deck group of the additive group, and it is the model for the compact orbifold
signatures, whose universal cover is the additive group of the plane and whose deck groups act by
translations.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

variable {L : Type*} [Field L] [CharZero L]

/-- **A polynomial fixed by one nonzero translation is constant.** -/
theorem natDegree_eq_zero_of_comp_X_add_C {c : L} (hc : c ≠ 0) :
    ∀ (P : Polynomial L), P.comp (Polynomial.X + Polynomial.C c) = P → P.natDegree = 0 := by
  intro P
  induction hd : P.natDegree using Nat.strong_induction_on generalizing P with
  | _ n ih =>
    intro hP
    by_contra hne
    have hPne : P.natDegree ≠ 0 := by omega
    have hderiv : (Polynomial.derivative P).comp (Polynomial.X + Polynomial.C c)
        = Polynomial.derivative P := by
      have h := congrArg Polynomial.derivative hP
      rw [Polynomial.derivative_comp] at h
      simpa using h
    have hlt : (Polynomial.derivative P).natDegree < n := by
      have := Polynomial.natDegree_derivative_lt hPne
      omega
    have hzero := ih _ hlt (Polynomial.derivative P) rfl hderiv
    have hdeq : (Polynomial.derivative P).natDegree = P.natDegree - 1 :=
      Polynomial.natDegree_derivative P
    have hd1 : P.natDegree = 1 := by omega
    set a := P.coeff 1 with ha
    set b := P.coeff 0 with hb
    have hPform : P = Polynomial.C a * Polynomial.X + Polynomial.C b :=
      Polynomial.eq_X_add_C_of_natDegree_le_one (by omega)
    have hane : a ≠ 0 := by
      intro h
      have hle : P.natDegree ≤ 0 := by
        rw [hPform, h, map_zero, zero_mul, zero_add]
        exact le_of_eq (Polynomial.natDegree_C _)
      omega
    have hcomp : (Polynomial.C a * Polynomial.X + Polynomial.C b).comp
        (Polynomial.X + Polynomial.C c)
        = (Polynomial.C a * Polynomial.X + Polynomial.C b) + Polynomial.C (a * c) := by
      simp only [Polynomial.add_comp, Polynomial.mul_comp, Polynomial.C_comp, Polynomial.X_comp,
        map_mul]
      ring
    rw [hPform, hcomp] at hP
    have hzeroC : Polynomial.C (a * c) = 0 := by
      linear_combination hP
    have hprod : a * c = 0 := by
      simpa using congrArg (fun R : Polynomial L => R.coeff 0) hzeroC
    rcases mul_eq_zero.mp hprod with h | h
    · exact hane h
    · exact hc h

/-- **A translation-invariant coprime fraction has constant numerator and denominator.** -/
theorem natDegree_eq_zero_of_translation_invariant {c : L} (hc : c ≠ 0)
    {P Q : Polynomial L} (hP0 : P ≠ 0) (hQ0 : Q ≠ 0) (hcop : IsCoprime P Q)
    (heq : P.comp (Polynomial.X + Polynomial.C c) * Q
      = P * Q.comp (Polynomial.X + Polynomial.C c)) :
    P.natDegree = 0 ∧ Q.natDegree = 0 := by
  classical
  have hdegcomp : ∀ R : Polynomial L,
      (R.comp (Polynomial.X + Polynomial.C c)).natDegree = R.natDegree := by
    intro R
    rcases eq_or_ne R 0 with rfl | hR
    · simp
    · rw [Polynomial.natDegree_comp, Polynomial.natDegree_X_add_C, mul_one]
  have hne : ∀ R : Polynomial L, R ≠ 0 → R.comp (Polynomial.X + Polynomial.C c) ≠ 0 := by
    intro R hR h
    have hd := hdegcomp R
    rw [h] at hd
    have hlead := congrArg Polynomial.leadingCoeff h
    rw [Polynomial.leadingCoeff_comp (by simp)] at hlead
    simp only [Polynomial.leadingCoeff_zero, Polynomial.leadingCoeff_X_add_C, one_pow,
      mul_one] at hlead
    exact hR (Polynomial.leadingCoeff_eq_zero.mp hlead)
  have hfix : ∀ R : Polynomial L, R ≠ 0 → R ∣ R.comp (Polynomial.X + Polynomial.C c) →
      R.comp (Polynomial.X + Polynomial.C c) = R := by
    intro R hR ⟨S, hS⟩
    have hSne : S ≠ 0 := by
      intro h
      rw [h, mul_zero] at hS
      exact hne R hR hS
    have hdeg : S.natDegree = 0 := by
      have h1 := hdegcomp R
      rw [hS, Polynomial.natDegree_mul hR hSne] at h1
      omega
    have hlead := congrArg Polynomial.leadingCoeff hS
    rw [Polynomial.leadingCoeff_comp (by simp), Polynomial.leadingCoeff_mul] at hlead
    simp only [Polynomial.leadingCoeff_X_add_C, one_pow, mul_one] at hlead
    have hR0 : R.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hR
    have hSlead : S.leadingCoeff = 1 := by
      have h2 : R.leadingCoeff * 1 = R.leadingCoeff * S.leadingCoeff := by
        rw [mul_one]
        exact hlead
      exact (mul_left_cancel₀ hR0 h2).symm
    have hS1 : S = 1 := by
      have hSC : S = Polynomial.C (S.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hdeg
      have hone : S.coeff 0 = 1 := by
        rw [← hSlead, Polynomial.leadingCoeff, hdeg]
      rw [hSC, hone, map_one]
    rw [hS, hS1, mul_one]
  have hdvdP : P ∣ P.comp (Polynomial.X + Polynomial.C c) :=
    hcop.dvd_of_dvd_mul_right ⟨Q.comp (Polynomial.X + Polynomial.C c), heq⟩
  have hdvdQ : Q ∣ Q.comp (Polynomial.X + Polynomial.C c) :=
    hcop.symm.dvd_of_dvd_mul_right
      ⟨P.comp (Polynomial.X + Polynomial.C c), by linear_combination -heq⟩
  exact ⟨natDegree_eq_zero_of_comp_X_add_C hc P (hfix P hP0 hdvdP),
    natDegree_eq_zero_of_comp_X_add_C hc Q (hfix Q hQ0 hdvdQ)⟩

end GaloisForLFunctions.HTGeometry
