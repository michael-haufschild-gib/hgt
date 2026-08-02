import GaloisForLFunctions.HTGeometry.HolderShiftElimination

/-!
# The leading term of a jet substitution

Translating each jet variable by a rational increment leaves the top total-degree layer of a
polynomial untouched except for the coefficient shift.  For a degree-compatible monomial order this
says the leading monomial is preserved and the leading coefficient is shifted.

Multiplicativity of the leading coefficient then converts a multiplicative shift equation between
polynomials in the jets into the same equation between two rational functions: the ratio of the two
leading coefficients solves `w(X+1) = q·w(X)`.
-/

open MvPolynomial MonomialOrder Finsupp

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions RationalIncrementHolder

noncomputable section

variable {m : ℕ}

/-- On the top total-degree layer the jet substitution acts by the coefficient shift. -/
theorem coeff_jetTranslate_top (rj : ℕ → RatFunc ℂ) {P : MvPolynomial (Fin m) (RatFunc ℂ)}
    {β : Fin m →₀ ℕ} (hβ : P.totalDegree ≤ β.degree) :
    coeff β (jetTranslateWith rj m P) = ratShift (coeff β P) :=
  coeff_jetTranslate_of_le_degSumWith rj
    (fun _ hα => le_trans (MvPolynomial.le_totalDegree hα) hβ)

/-- The jet substitution preserves the degree-lexicographic leading monomial. -/
theorem degree_jetTranslate (rj : ℕ → RatFunc ℂ) {P : MvPolynomial (Fin m) (RatFunc ℂ)}
    (hP : P ≠ 0) :
    degLex.degree (jetTranslateWith rj m P) = degLex.degree P := by
  classical
  have hβ₀ : degLex.degree P ∈ P.support := (MonomialOrder.degree_mem_support_iff P).mpr hP
  have hc₀ : coeff (degLex.degree P) P ≠ 0 := MvPolynomial.mem_support_iff.mp hβ₀
  have hdeg₀ : (degLex.degree P).degree = P.totalDegree := degree_degLexDegree
  have hcoeff₀ : coeff (degLex.degree P) (jetTranslateWith rj m P)
      = ratShift (coeff (degLex.degree P) P) :=
    coeff_jetTranslate_top rj (le_of_eq hdeg₀.symm)
  have hne₀ : coeff (degLex.degree P) (jetTranslateWith rj m P) ≠ 0 := by
    rw [hcoeff₀]
    intro h0
    exact hc₀ (ratShift_injective (by rw [h0, map_zero]))
  have hTP : jetTranslateWith rj m P ≠ 0 := by
    intro h0
    rw [h0, coeff_zero] at hne₀
    exact hne₀ rfl
  have h1 : degLex.degree P ≼[degLex] degLex.degree (jetTranslateWith rj m P) :=
    MonomialOrder.le_degree (MvPolynomial.mem_support_iff.mpr hne₀)
  have h2 : degLex.degree (jetTranslateWith rj m P) ≼[degLex] degLex.degree P := by
    have hγ : coeff (degLex.degree (jetTranslateWith rj m P)) (jetTranslateWith rj m P) ≠ 0 :=
      MonomialOrder.coeff_degree_ne_zero_iff.mpr hTP
    have hγdeg : (degLex.degree (jetTranslateWith rj m P)).degree
        = (jetTranslateWith rj m P).totalDegree := degree_degLexDegree
    have hle : (degLex.degree (jetTranslateWith rj m P)).degree ≤ (degLex.degree P).degree := by
      rw [hγdeg, hdeg₀]
      exact totalDegree_jetTranslate_leWith rj P
    rcases hle.lt_or_eq with hlt | heq
    · refine le_of_lt ?_
      rw [MonomialOrder.degLex_lt_iff, DegLex.lt_iff, ofDegLex_toDegLex, ofDegLex_toDegLex]
      exact Or.inl hlt
    · have htopγ := coeff_jetTranslate_top (β := degLex.degree (jetTranslateWith rj m P)) rj
        (le_of_eq (heq.trans hdeg₀).symm)
      rw [htopγ] at hγ
      refine MonomialOrder.le_degree (MvPolynomial.mem_support_iff.mpr ?_)
      intro h0
      exact hγ (by rw [h0, map_zero])
  exact degLex.toSyn.injective (le_antisymm h2 h1)

/-- The jet substitution shifts the degree-lexicographic leading coefficient. -/
theorem leadingCoeff_jetTranslate (rj : ℕ → RatFunc ℂ) {P : MvPolynomial (Fin m) (RatFunc ℂ)}
    (hP : P ≠ 0) :
    degLex.leadingCoeff (jetTranslateWith rj m P) = ratShift (degLex.leadingCoeff P) := by
  rw [MonomialOrder.leadingCoeff, MonomialOrder.leadingCoeff, degree_jetTranslate rj hP]
  exact coeff_jetTranslate_top rj (le_of_eq (degree_degLexDegree (f := P)).symm)

/-- **A multiplicative shift equation descends to the coefficient field.**  If the jet substitution
multiplies a quotient of jet polynomials by a rational factor, the ratio of the two leading
coefficients is a rational solution of the same multiplicative shift equation. -/
theorem ratShift_leadingCoeff_ratio (rj : ℕ → RatFunc ℂ) {q : RatFunc ℂ}
    {P Q : MvPolynomial (Fin m) (RatFunc ℂ)} (hP : P ≠ 0) (hQ : Q ≠ 0)
    (heq : jetTranslateWith rj m P * Q
      = MvPolynomial.C q * (P * jetTranslateWith rj m Q)) :
    ratShift (degLex.leadingCoeff P / degLex.leadingCoeff Q)
      = q * (degLex.leadingCoeff P / degLex.leadingCoeff Q) := by
  have hlcP : degLex.leadingCoeff P ≠ 0 := MonomialOrder.leadingCoeff_ne_zero_iff.mpr hP
  have hlcQ : degLex.leadingCoeff Q ≠ 0 := MonomialOrder.leadingCoeff_ne_zero_iff.mpr hQ
  have hkey := congrArg (fun R : MvPolynomial (Fin m) (RatFunc ℂ) => degLex.leadingCoeff R) heq
  simp only [MonomialOrder.leadingCoeff_mul, MonomialOrder.leadingCoeff_C,
    leadingCoeff_jetTranslate rj hP, leadingCoeff_jetTranslate rj hQ] at hkey
  have hshiftQ : ratShift (degLex.leadingCoeff Q) ≠ 0 := by
    intro h0
    exact hlcQ (ratShift_injective (by rw [h0, map_zero]))
  rw [map_div₀, div_eq_iff hshiftQ]
  field_simp
  linear_combination hkey

end

end GaloisForLFunctions.HTGeometry
