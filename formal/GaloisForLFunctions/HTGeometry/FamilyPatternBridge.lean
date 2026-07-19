import GaloisForLFunctions.HTGeometry.FamilyJetReshape
import GaloisForLFunctions.HTGeometry.PolynomialPatternRectangularization

/-!
# The multi-shift pattern bridge, contradiction step

A relation among a finite family of translates becomes, after reshaping the spectral variable into
polynomial coefficients and renaming into dependent shift/order form, a polynomial-coefficient
relation carried by a finite differential pattern whose shift palette is `Fin m` itself.

This file supplies the step that turns pattern-freeness back into a contradiction: if every pattern
coefficient of the reshaped relation vanishes, the original relation was zero.  It needs nothing
about the palette beyond injectivity of the shift codes, so unlike the single-shift bridge it does
not rely on the shift index being a subsingleton.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- The canonical shift codes for an `m`-translate pattern: the palette is `Fin m` itself. -/
def familyShiftCode (m : ℕ) : Fin m → Fin m := id

theorem familyShiftCode_injective (m : ℕ) : Function.Injective (familyShiftCode m) :=
  Function.injective_id

/-- The constant jet-order assignment of an `m`-translate pattern. -/
def familyOrders (m n : ℕ) : Fin m → ℕ := fun _ => n + 1

/-- The finite pattern attached to a family jet relation. -/
def familyPatternOfRelation (m n : ℕ) (P : MvPolynomial (FamilyJetIndex m n) ℂ) :
    FiniteDifferentialPattern (Fin m) :=
  finitePatternOfPolynomial (familyShiftCode m) (familyShiftCode_injective m) (familyOrders m n)
    (renameToFamilyShiftJets m n (familyReshapeJet m n P))

/-- **The back half of the multi-shift bridge.**  If every pattern coefficient of the reshaped
relation vanishes, the original family jet relation was zero.  This is the step that turns
pattern-freeness into a contradiction, and it needs nothing about the palette beyond injectivity of
the shift codes. -/
theorem familyJetRelation_eq_zero_of_patternCoefficients_zero {m n : ℕ}
    (P : MvPolynomial (FamilyJetIndex m n) ℂ)
    (hzero : ∀ b, polynomialPatternCoefficientVector (familyShiftCode m)
        (familyShiftCode_injective m) (familyOrders m n)
        (renameToFamilyShiftJets m n (familyReshapeJet m n P)) b = 0) :
    P = 0 := by
  have hQ : renameToFamilyShiftJets m n (familyReshapeJet m n P) = 0 :=
    polynomial_eq_zero_of_patternCoefficientVector_eq_zero (familyShiftCode m)
      (familyShiftCode_injective m) (familyOrders m n) _ hzero
  have hR : familyReshapeJet m n P = 0 := by
    refine renameToFamilyShiftJets_injective m n ?_
    rw [hQ]
    simp [renameToFamilyShiftJets]
  exact familyReshapeJet_injective m n (by rw [hR, map_zero])

/-- **The forward step of the multi-shift bridge.**  The pattern coefficient expansion of a family
jet relation, evaluated at jet values `x` and spectral value `z`, is the original relation evaluated
at the family jet vector. -/
theorem familyPatternExpansion_eq_eval {m n : ℕ} (P : MvPolynomial (FamilyJetIndex m n) ℂ)
    (z : ℂ) (x : (Σ _ : Fin m, Fin (n + 1)) → ℂ) :
    (∑ b, polynomialPatternCoefficientVector (familyShiftCode m) (familyShiftCode_injective m)
        (familyOrders m n) (renameToFamilyShiftJets m n (familyReshapeJet m n P)) b *
      z ^ patternDegree (familyPatternOfRelation m n P) b *
      (patternExponent (familyPatternOfRelation m n P) b).prod (fun i e => x i ^ e))
      = MvPolynomial.eval (Sum.elim (fun _ => z) fun p => x ⟨p.1, p.2⟩) P := by
  simp only [familyPatternOfRelation]
  rw [polynomialPatternCoefficientExpansion]
  have hrename : MvPolynomial.eval x (specializePolynomialCoefficients z
        (renameToFamilyShiftJets m n (familyReshapeJet m n P)))
      = MvPolynomial.eval (fun q => x ((familySigmaEquiv m n).symm q))
          (specializePolynomialCoefficients z (familyReshapeJet m n P)) := by
    simp only [renameToFamilyShiftJets, specializePolynomialCoefficients, MvPolynomial.eval_map]
    simpa [Function.comp_def] using
      (MvPolynomial.eval₂_rename (Polynomial.evalRingHom z) (familySigmaEquiv m n).symm x
        (familyReshapeJet m n P))
  exact hrename.trans (eval_specialize_familyReshapeJet m n z
    (fun q => x ((familySigmaEquiv m n).symm q)) P)

end

end GaloisForLFunctions.HTGeometry
