import GaloisForLFunctions.HTGeometry.JetShiftTopCoefficient
import GaloisForLFunctions.HTGeometry.QuadraticNoNormalizingShift

/-!
# The descent of a normalizing shift for the two quadratic maps

Assembling the branches.  A normalizing shift of `z ↦ z² + 1` (or of `z ↦ (z − 1)²`) at jet level
`N + 3` is sliced in the coordinate `y_{N+2}`; the denominator of the slice is a scalar eigenvector,
so either it has positive degree and the affine cocycle of its two top coefficients is a normalizing
shift one level down, or the shift is a polynomial `u` in `y_{N+2}`.  For the polynomial the degree
decides: degree zero forces the linear coefficient `∂_{N+2}σ_{N+3} = (N+3)·R''·y₁` of the shift term
to vanish, which it does not; degree at least three reproduces the cocycle and descends again.

So for both maps the descent is complete except for polynomial degrees one and two.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- **The descent for a map whose second derivative survives.**  A normalizing shift at jet level
`N + 3` either descends one level, or is a polynomial of degree one or two in `y_{N+2}`. -/
theorem hasNormalizingShift_pred_or_low_degree {C : Type*} [Field C] [CharZero C]
    (R : RatFunc C) (hR : substitutionDeriv R ≠ 0)
    (hR2 : JetField.pd ((), 0) (substitutionDeriv R) ≠ 0) (N : ℕ)
    (h : HasNormalizingShift R hR (show (1 : ℕ) ≤ N + 3 by omega)) :
    HasNormalizingShift R hR (show (1 : ℕ) ≤ N + 2 by omega)
      ∨ ∃ (u : Polynomial ↥(jetPrefixField C (N + 2))) (A B : ↥(jetPrefixField C (N + 2))),
          (u.natDegree = 1 ∨ u.natDegree = 2) ∧
            substitutionShift R (N + 3)
              = (A : JetField C Unit) * (JetField.jet ((), N + 2) : JetField C Unit)
                + (B : JetField C Unit) ∧
            twistComp (jetSubstitutionPrefix R hR (N + 2)).toRingHom
                (substitutionAffine R (show (1 : ℕ) ≤ N + 2 by omega)) u
              = Polynomial.C (substitutionDerivPrefix R (show (1 : ℕ) ≤ N + 2 by omega)) * u
                - (Polynomial.C A * Polynomial.X + Polynomial.C B) := by
  rcases hasNormalizingShift_pred_or_polynomial R hR N h with hpred | ⟨u, A, B, hAB, hcu⟩
  · exact Or.inl hpred
  rcases Nat.lt_or_ge u.natDegree 3 with hlt | hge
  · interval_cases hdeg : u.natDegree
    · exfalso
      have hA0 : A = 0 := top_eq_zero_of_polynomial_branch_deg_zero R hR N hdeg hcu
      have hAcoe : (A : JetField C Unit) = JetField.pd ((), N + 2) (substitutionShift R (N + 3)) :=
        coe_eq_pd_top_of_affine R N hAB
      rw [hA0] at hAcoe
      exact pd_top_substitutionShift_ne_zero R (N + 1) hR2 (by
        rw [← hAcoe]; rfl)
    · exact Or.inr ⟨u, A, B, Or.inl hdeg, hAB, hcu⟩
    · exact Or.inr ⟨u, A, B, Or.inr hdeg, hAB, hcu⟩
  · exact Or.inl (hasNormalizingShift_of_polynomial_branch R hR N hge hcu)

/-- **The descent for `z ↦ z² + 1`.** -/
theorem quadOne_hasNormalizingShift_pred_or_low_degree (N : ℕ)
    (h : HasNormalizingShift (algebraMap (Polynomial ℂ) (RatFunc ℂ) quadOne)
      quadOne_substitutionDeriv_ne_zero (show (1 : ℕ) ≤ N + 3 by omega)) :
    HasNormalizingShift (algebraMap (Polynomial ℂ) (RatFunc ℂ) quadOne)
        quadOne_substitutionDeriv_ne_zero (show (1 : ℕ) ≤ N + 2 by omega)
      ∨ ∃ (u : Polynomial ↥(jetPrefixField ℂ (N + 2))) (A B : ↥(jetPrefixField ℂ (N + 2))),
          (u.natDegree = 1 ∨ u.natDegree = 2) ∧
            substitutionShift (algebraMap (Polynomial ℂ) (RatFunc ℂ) quadOne) (N + 3)
              = (A : JetField ℂ Unit) * (JetField.jet ((), N + 2) : JetField ℂ Unit)
                + (B : JetField ℂ Unit) ∧
            twistComp (jetSubstitutionPrefix (algebraMap (Polynomial ℂ) (RatFunc ℂ) quadOne)
                quadOne_substitutionDeriv_ne_zero (N + 2)).toRingHom
                (substitutionAffine (algebraMap (Polynomial ℂ) (RatFunc ℂ) quadOne)
                  (show (1 : ℕ) ≤ N + 2 by omega)) u
              = Polynomial.C (substitutionDerivPrefix
                    (algebraMap (Polynomial ℂ) (RatFunc ℂ) quadOne)
                    (show (1 : ℕ) ≤ N + 2 by omega)) * u
                - (Polynomial.C A * Polynomial.X + Polynomial.C B) :=
  hasNormalizingShift_pred_or_low_degree _ quadOne_substitutionDeriv_ne_zero
    quadOne_pd_substitutionDeriv_ne_zero N h

/-- **The descent for `z ↦ (z − 1)²`.** -/
theorem quadTwo_hasNormalizingShift_pred_or_low_degree (N : ℕ)
    (h : HasNormalizingShift (algebraMap (Polynomial ℂ) (RatFunc ℂ) quadTwo)
      quadTwo_substitutionDeriv_ne_zero (show (1 : ℕ) ≤ N + 3 by omega)) :
    HasNormalizingShift (algebraMap (Polynomial ℂ) (RatFunc ℂ) quadTwo)
        quadTwo_substitutionDeriv_ne_zero (show (1 : ℕ) ≤ N + 2 by omega)
      ∨ ∃ (u : Polynomial ↥(jetPrefixField ℂ (N + 2))) (A B : ↥(jetPrefixField ℂ (N + 2))),
          (u.natDegree = 1 ∨ u.natDegree = 2) ∧
            substitutionShift (algebraMap (Polynomial ℂ) (RatFunc ℂ) quadTwo) (N + 3)
              = (A : JetField ℂ Unit) * (JetField.jet ((), N + 2) : JetField ℂ Unit)
                + (B : JetField ℂ Unit) ∧
            twistComp (jetSubstitutionPrefix (algebraMap (Polynomial ℂ) (RatFunc ℂ) quadTwo)
                quadTwo_substitutionDeriv_ne_zero (N + 2)).toRingHom
                (substitutionAffine (algebraMap (Polynomial ℂ) (RatFunc ℂ) quadTwo)
                  (show (1 : ℕ) ≤ N + 2 by omega)) u
              = Polynomial.C (substitutionDerivPrefix
                    (algebraMap (Polynomial ℂ) (RatFunc ℂ) quadTwo)
                    (show (1 : ℕ) ≤ N + 2 by omega)) * u
                - (Polynomial.C A * Polynomial.X + Polynomial.C B) :=
  hasNormalizingShift_pred_or_low_degree _ quadTwo_substitutionDeriv_ne_zero
    quadTwo_pd_substitutionDeriv_ne_zero N h

end

end GaloisForLFunctions.HTGeometry
