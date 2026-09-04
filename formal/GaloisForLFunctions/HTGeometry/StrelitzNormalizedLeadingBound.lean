import GaloisForLFunctions.HTGeometry.PolynomialCoefficientMvPolynomialGrowth

/-!
# Normalized leading-coefficient bound for Strelitz relations

If the function value has norm at least one, maximality of the selected function-value degree lets
one cancel all but one common power of that value from the leading-summand inequality.  Thus the
leading logarithmic-jet coefficient times `|F|` is controlled solely by the lower coefficient
values.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- **Normalized leading-coefficient inequality.** At an exact root with `1 ≤ |F|`, the leading
coefficient gains one full factor of `|F|` against the finite sum of lower coefficients. -/
theorem norm_eval₂_maximal_strelitzValueCoeff_mul_norm_le_sum_erase
    (Q : MvPolynomial (Fin 3) (Polynomial ℂ))
    {D : ℕ} (hD : D ∈ strelitzValueSupport Q)
    (hmax : ∀ d ∈ strelitzValueSupport Q, d ≤ D)
    (z F U V : ℂ) (hF : 1 ≤ ‖F‖)
    (hrel : MvPolynomial.eval₂ (Polynomial.evalRingHom z) ![F, U, V] Q = 0) :
    ‖MvPolynomial.eval₂ (Polynomial.evalRingHom z) ![U, V]
        (strelitzValueCoeff Q D)‖ * ‖F‖ ≤
      ∑ d ∈ (strelitzValueSupport Q).erase D,
        ‖MvPolynomial.eval₂ (Polynomial.evalRingHom z) ![U, V]
          (strelitzValueCoeff Q d)‖ := by
  classical
  have hiso := norm_eval₂_strelitzValueCoeff_mul_pow_le_sum_erase
    Q hD z F U V hrel
  by_cases hD0 : D = 0
  · subst D
    have hempty : (strelitzValueSupport Q).erase 0 = ∅ := by
      ext d
      constructor
      · intro hd
        have hderase := Finset.mem_erase.mp hd
        have hdle := hmax d hderase.2
        have : d = 0 := Nat.eq_zero_of_le_zero hdle
        exact (hderase.1 this).elim
      · simp
    rw [hempty] at hiso ⊢
    simp only [Finset.sum_empty, pow_zero, mul_one] at hiso
    have hzero : ‖MvPolynomial.eval₂ (Polynomial.evalRingHom z) ![U, V]
        (strelitzValueCoeff Q 0)‖ = 0 := by
      exact le_antisymm hiso (norm_nonneg _)
    rw [hzero, zero_mul]
    simp
  · have hDpos : 0 < D := Nat.pos_of_ne_zero hD0
    have hlower : ∀ d ∈ (strelitzValueSupport Q).erase D, d ≤ D - 1 := by
      intro d hd
      have hdne : d ≠ D := (Finset.mem_erase.mp hd).1
      have hdle : d ≤ D := hmax d (Finset.mem_erase.mp hd).2
      omega
    have hrhs :
        ∑ d ∈ (strelitzValueSupport Q).erase D,
            ‖MvPolynomial.eval₂ (Polynomial.evalRingHom z) ![U, V]
              (strelitzValueCoeff Q d)‖ * ‖F‖ ^ d ≤
          (∑ d ∈ (strelitzValueSupport Q).erase D,
            ‖MvPolynomial.eval₂ (Polynomial.evalRingHom z) ![U, V]
              (strelitzValueCoeff Q d)‖) * ‖F‖ ^ (D - 1) := by
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum fun d hd =>
        mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ hF (hlower d hd)) (norm_nonneg _)
    have hcombined := hiso.trans hrhs
    have hpowpos : 0 < ‖F‖ ^ (D - 1) := pow_pos (lt_of_lt_of_le zero_lt_one hF) _
    have hfactor : ‖F‖ ^ D = ‖F‖ ^ (D - 1) * ‖F‖ := by
      rw [← pow_succ]
      congr 1
      omega
    rw [hfactor] at hcombined
    have hcommon : ‖F‖ ^ (D - 1) *
          (‖MvPolynomial.eval₂ (Polynomial.evalRingHom z) ![U, V]
            (strelitzValueCoeff Q D)‖ * ‖F‖) ≤
        ‖F‖ ^ (D - 1) *
          (∑ d ∈ (strelitzValueSupport Q).erase D,
            ‖MvPolynomial.eval₂ (Polynomial.evalRingHom z) ![U, V]
              (strelitzValueCoeff Q d)‖) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hcombined
    nlinarith

end

end GaloisForLFunctions.HTGeometry
