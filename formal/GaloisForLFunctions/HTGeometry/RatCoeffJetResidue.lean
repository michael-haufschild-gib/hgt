import GaloisForLFunctions.HTGeometry.PolyCoeffJetResidue
import GaloisForLFunctions.HTGeometry.DigammaFieldRatio

/-!
# The residue of a jet combination with rational coefficients

A finite family of rational coefficients has a common denominator, so a combination of jet monomials
over `ℂ(s)` is a polynomial-coefficient combination divided by one polynomial.  Dividing the
denominator by the power of its own degree contributes exactly its leading coefficient, so the
residue of the quotient is the residue of the numerator divided by that leading coefficient.
-/

open Filter Topology Complex Polynomial

namespace GaloisForLFunctions

variable {σ : ℝ}

/-- **The residue of a jet combination with rational coefficients.**  With a common denominator `q`,
the combination normalized by the dominant shape divided by `s^{deg q}` converges to the dominant
residue divided by the leading coefficient of `q`. -/
theorem tendsto_sum_ratCoeff_jetMonomial (hσ : 0 < σ) {n N : ℕ} (p : Fin N → Polynomial ℂ)
    {q : Polynomial ℂ} (hq : q ≠ 0) (e : Fin N → Fin (n + 1) → ℕ) (β : Fin N)
    (hdom : ∀ α : Fin N,
      (e α 0 = e β 0 ∧ (p α).natDegree + jetSDeg (e β) = (p β).natDegree + jetSDeg (e α))
      ∨ ((p α).natDegree + jetSDeg (e β) < (p β).natDegree + jetSDeg (e α)
        ∨ ((p α).natDegree + jetSDeg (e β) = (p β).natDegree + jetSDeg (e α)
          ∧ e α 0 < e β 0))) :
    Tendsto (fun t : ℝ =>
        ((∑ α : Fin N, (p α).eval ((σ : ℂ) + (t : ℂ) * Complex.I) * jetMonomial σ (e α) t)
            / q.eval ((σ : ℂ) + (t : ℂ) * Complex.I))
          / (polyJetShape σ (e β 0) ((p β).natDegree) (jetSDeg (e β)) t
            / ((σ : ℂ) + (t : ℂ) * Complex.I) ^ q.natDegree)) atTop
      (nhds ((∑ α ∈ Finset.univ.filter (fun α : Fin N =>
            e α 0 = e β 0 ∧ (p α).natDegree + jetSDeg (e β) = (p β).natDegree + jetSDeg (e α)),
          (p α).leadingCoeff * ∏ j : Fin (n + 1), (jetLeadingConst (j : ℕ)) ^ (e α j))
        / q.leadingCoeff)) := by
  classical
  have hleadne : q.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hq
  have hnum := tendsto_sum_polyCoeff_jetMonomial hσ p e β hdom
  have hden := tendsto_eval_div_pow_natDegree_vertical σ q
  have hinv := hden.inv₀ hleadne
  have hmul := hnum.mul hinv
  have hgoal : (∑ α ∈ Finset.univ.filter (fun α : Fin N =>
        e α 0 = e β 0 ∧ (p α).natDegree + jetSDeg (e β) = (p β).natDegree + jetSDeg (e α)),
        (p α).leadingCoeff * ∏ j : Fin (n + 1), (jetLeadingConst (j : ℕ)) ^ (e α j))
      / q.leadingCoeff
      = (∑ α ∈ Finset.univ.filter (fun α : Fin N =>
        e α 0 = e β 0 ∧ (p α).natDegree + jetSDeg (e β) = (p β).natDegree + jetSDeg (e α)),
        (p α).leadingCoeff * ∏ j : Fin (n + 1), (jetLeadingConst (j : ℕ)) ^ (e α j))
        * (q.leadingCoeff)⁻¹ := div_eq_mul_inv _ _
  rw [hgoal]
  refine hmul.congr' ?_
  filter_upwards [eventually_vertLog_ne_zero, eventually_vertical_ne_zero σ,
    eventually_eval_ne_zero σ hq,
    eventually_jetNormFactor_ne_zero hσ (e β 0) (jetSDeg (e β))] with t hL hs hqt hF
  have hshape : polyJetShape σ (e β 0) ((p β).natDegree) (jetSDeg (e β)) t ≠ 0 := by
    rw [polyJetShape]
    exact div_ne_zero (mul_ne_zero (pow_ne_zero _ hL) (pow_ne_zero _ hs)) (pow_ne_zero _ hs)
  have hpow : ((σ : ℂ) + (t : ℂ) * Complex.I) ^ q.natDegree ≠ 0 := pow_ne_zero _ hs
  field_simp

end GaloisForLFunctions
