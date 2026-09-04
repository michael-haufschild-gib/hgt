import GaloisForLFunctions.HTGeometry.StrelitzValueCoefficientDecomposition

/-!
# Leading function-value coefficient of a Strelitz relation

A nonzero logarithmic-jet relation has a maximal function-value degree with nonzero coefficient.
At every exact root of the relation, its leading summand equals the negative sum of all lower
summands.  Taking norms gives the finite-sum inequality used in the maximum-modulus part of the
Valiron--Zimogljad--Strelitz argument.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A nonzero Strelitz relation has a maximal occurring value degree, and its coefficient is
nonzero. -/
theorem exists_maximal_strelitzValueCoeff
    {Q : MvPolynomial (Fin 3) (Polynomial ℂ)} (hQ : Q ≠ 0) :
    ∃ D ∈ strelitzValueSupport Q,
      strelitzValueCoeff Q D ≠ 0 ∧
      ∀ d ∈ strelitzValueSupport Q, d ≤ D := by
  classical
  obtain ⟨d, hd, -⟩ := exists_nonzero_strelitzValueCoeff hQ
  obtain ⟨D, hD, hmax⟩ := Finset.exists_max_image
    (strelitzValueSupport Q) (fun e => e) ⟨d, hd⟩
  exact ⟨D, hD, strelitzValueCoeff_ne_zero_of_mem hD,
    fun e he => hmax e he⟩

/-- At an exact root, the maximal value-degree summand is the negative sum of all other
summands. -/
theorem eval₂_strelitzValueCoeff_mul_pow_eq_neg_sum_erase
    (Q : MvPolynomial (Fin 3) (Polynomial ℂ))
    {D : ℕ} (hD : D ∈ strelitzValueSupport Q)
    (z F U V : ℂ)
    (hrel : MvPolynomial.eval₂ (Polynomial.evalRingHom z) ![F, U, V] Q = 0) :
    MvPolynomial.eval₂ (Polynomial.evalRingHom z) ![U, V]
        (strelitzValueCoeff Q D) * F ^ D =
      -∑ d ∈ (strelitzValueSupport Q).erase D,
        MvPolynomial.eval₂ (Polynomial.evalRingHom z) ![U, V]
          (strelitzValueCoeff Q d) * F ^ d := by
  classical
  have hsum :
      ∑ d ∈ strelitzValueSupport Q,
          MvPolynomial.eval₂ (Polynomial.evalRingHom z) ![U, V]
            (strelitzValueCoeff Q d) * F ^ d = 0 := by
    rw [eval₂_strelitzValueSupport]
    exact hrel
  have herase := Finset.sum_erase_add
    (s := strelitzValueSupport Q)
    (f := fun d => MvPolynomial.eval₂ (Polynomial.evalRingHom z) ![U, V]
      (strelitzValueCoeff Q d) * F ^ d) hD
  rw [hsum] at herase
  linear_combination herase

/-- Norm inequality obtained from exact leading-summand isolation. -/
theorem norm_eval₂_strelitzValueCoeff_mul_pow_le_sum_erase
    (Q : MvPolynomial (Fin 3) (Polynomial ℂ))
    {D : ℕ} (hD : D ∈ strelitzValueSupport Q)
    (z F U V : ℂ)
    (hrel : MvPolynomial.eval₂ (Polynomial.evalRingHom z) ![F, U, V] Q = 0) :
    ‖MvPolynomial.eval₂ (Polynomial.evalRingHom z) ![U, V]
        (strelitzValueCoeff Q D)‖ * ‖F‖ ^ D ≤
      ∑ d ∈ (strelitzValueSupport Q).erase D,
        ‖MvPolynomial.eval₂ (Polynomial.evalRingHom z) ![U, V]
          (strelitzValueCoeff Q d)‖ * ‖F‖ ^ d := by
  rw [← norm_pow, ← norm_mul,
    eval₂_strelitzValueCoeff_mul_pow_eq_neg_sum_erase Q hD z F U V hrel,
    norm_neg]
  simpa only [norm_mul, norm_pow] using
    (norm_sum_le ((strelitzValueSupport Q).erase D)
      (fun d => MvPolynomial.eval₂ (Polynomial.evalRingHom z) ![U, V]
        (strelitzValueCoeff Q d) * F ^ d))

end

end GaloisForLFunctions.HTGeometry
