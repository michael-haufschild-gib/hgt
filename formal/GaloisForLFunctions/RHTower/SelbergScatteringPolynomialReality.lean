import GaloisForLFunctions.RHTower.CoshPolynomialPeriodClassification

/-!
# Polynomial reality on the native critical scattering parabola

The Casimir at Eisenstein parameter `s = 1/4 + it/2` is
`3/16 + t²/4 + it/4`. A complex polynomial takes real values on infinitely
many points of this parabola exactly when it is a real constant. Schwarz
reflection and the quadratic deck involution force a nonzero additive period
for the composed polynomial; polynomial period rigidity gives the classification.
-/

open Complex Polynomial Set

namespace RHTower.SelbergScatteringPolynomialReality

noncomputable section

/-- Native modular scattering Casimir on the centered critical-line parameter. -/
def criticalCasimir (z : ℂ) : ℂ := 3 / 16 + z ^ 2 / 4 + I * z / 4

/-- The polynomial whose evaluation is the native critical scattering Casimir. -/
def casimirPolynomial : Polynomial ℂ :=
  C (1 / 4) * X ^ 2 + C (I / 4) * X + C (3 / 16)

@[simp] theorem eval_casimirPolynomial (z : ℂ) :
    casimirPolynomial.eval z = criticalCasimir z := by
  simp [casimirPolynomial, criticalCasimir]
  ring

theorem natDegree_casimirPolynomial : casimirPolynomial.natDegree = 2 := by
  exact Polynomial.natDegree_quadratic (by norm_num : (1 / 4 : ℂ) ≠ 0)

/-- The two-sheet involution of the native Casimir polynomial. -/
theorem criticalCasimir_reflection (z : ℂ) :
    criticalCasimir (-z - I) = criticalCasimir z := by
  simp only [criticalCasimir]
  ring_nf

/-- Reality on infinitely many real parameters forces a real constant polynomial. -/
theorem constant_of_infinite_real_locus (P : Polynomial ℂ)
    (hinf : Set.Infinite {t : ℝ | (P.eval (criticalCasimir t)).im = 0}) :
    ∃ c : ℝ, P = C (c : ℂ) := by
  let Q : Polynomial ℂ := P.comp casimirPolynomial
  have heval (z : ℂ) : Q.eval z = P.eval (criticalCasimir z) := by
    simp [Q]
  have hmap : Q.map (starRingEnd ℂ) = Q := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply (hinf.image Complex.ofReal_injective.injOn).mono
    rintro _ ⟨t, ht, rfl⟩
    change (Q.map (starRingEnd ℂ)).eval (t : ℂ) = Q.eval (t : ℂ)
    change (P.eval (criticalCasimir (t : ℂ))).im = 0 at ht
    have hm := Polynomial.eval_map_apply (p := Q) (starRingEnd ℂ) (t : ℂ)
    simpa only [Complex.conj_ofReal, heval,
      Complex.conj_eq_iff_im.mpr ht] using hm
  have hconj (z : ℂ) : star (Q.eval z) = Q.eval (star z) := by
    change (starRingEnd ℂ) (Q.eval z) = Q.eval ((starRingEnd ℂ) z)
    simpa only [hmap] using
      (Polynomial.eval_map_apply (p := Q) (starRingEnd ℂ) z).symm
  have hminus (z : ℂ) : Q.eval (-z - I) = Q.eval z := by
    rw [heval, heval, criticalCasimir_reflection]
  have hplus (z : ℂ) : Q.eval (-z + I) = Q.eval z := by
    apply star_injective
    rw [hconj, hconj]
    simpa only [star_add, star_neg, Complex.star_def, Complex.conj_I,
      sub_eq_add_neg] using hminus (star z)
  have hperiod : Function.Periodic Q.eval (2 * I) := by
    intro z
    have h := (hplus (-z - I)).trans (hminus z)
    convert h using 1
    congr 1
    ring
  have hQzero : Q.natDegree = 0 := by
    by_contra h
    have hd : 0 < Q.degree :=
      Polynomial.natDegree_pos_iff_degree_pos.mp (Nat.pos_of_ne_zero h)
    have hz := RHTower.polynomial_eval_periodic_eq_zero hd hperiod
    norm_num at hz
  have hPzero : P.natDegree = 0 := by
    have hdeg : Q.natDegree = P.natDegree * 2 := by
      change (P.comp casimirPolynomial).natDegree = _
      rw [Polynomial.natDegree_comp, natDegree_casimirPolynomial]
    omega
  have hP := Polynomial.eq_C_of_natDegree_eq_zero hPzero
  obtain ⟨t, ht⟩ := hinf.nonempty
  have hc : (P.coeff 0).im = 0 := by
    change (P.eval (criticalCasimir (t : ℂ))).im = 0 at ht
    rw [hP, Polynomial.eval_C] at ht
    exact ht
  refine ⟨(P.coeff 0).re, hP.trans ?_⟩
  congr 1
  exact Complex.ext rfl (by simp [hc])

/-- Exact classification of polynomials real on infinitely many native critical Casimirs. -/
theorem infinite_real_locus_iff (P : Polynomial ℂ) :
    Set.Infinite {t : ℝ | (P.eval (criticalCasimir t)).im = 0} ↔
      ∃ c : ℝ, P = C (c : ℂ) := by
  constructor
  · exact constant_of_infinite_real_locus P
  · rintro ⟨c, rfl⟩
    simpa using (Set.infinite_univ : Set.Infinite (Set.univ : Set ℝ))

/-- Every nonconstant polynomial has only finitely many real-valued native critical Casimirs. -/
theorem finite_real_locus (P : Polynomial ℂ) (hP : 0 < P.natDegree) :
    Set.Finite {t : ℝ | (P.eval (criticalCasimir t)).im = 0} := by
  rw [← Set.not_infinite]
  intro hinf
  obtain ⟨c, hc⟩ := constant_of_infinite_real_locus P hinf
  simp [hc] at hP

end
end RHTower.SelbergScatteringPolynomialReality
