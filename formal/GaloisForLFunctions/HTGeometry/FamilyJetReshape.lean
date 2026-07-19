import GaloisForLFunctions.HTGeometry.FamilyPolynomialGauge
import GaloisForLFunctions.HTGeometry.PolynomialRelationDetector

/-!
# Reshaping family jets into polynomial-coefficient form

A relation among a finite family of functions can be read with the spectral variable absorbed into
the coefficients, as a polynomial-coefficient relation in the jet variables alone.  That is the
form the pattern machinery consumes.

This is the multi-component analogue of `reshapeJet`, which handles one distinguished spectral
variable in `Fin (n + 2)`; here the spectral variable is the `Sum.inl` coordinate and the jet
variables are indexed by component and order.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- Reshaping the spectral variable of a family jet polynomial into polynomial coefficients. -/
def familyReshapeJet (m n : ℕ) :
    MvPolynomial (FamilyJetIndex m n) ℂ →+* MvPolynomial (Fin m × Fin (n + 1)) (Polynomial ℂ) :=
  MvPolynomial.eval₂Hom (MvPolynomial.C.comp Polynomial.C)
    (Sum.elim (fun _ => MvPolynomial.C Polynomial.X) fun p => MvPolynomial.X p)

/-- The inverse reshaping: the polynomial coefficient re-expands into the spectral variable. -/
def familyReshapeJetInv (m n : ℕ) :
    MvPolynomial (Fin m × Fin (n + 1)) (Polynomial ℂ) →+* MvPolynomial (FamilyJetIndex m n) ℂ :=
  MvPolynomial.eval₂Hom
    (Polynomial.eval₂RingHom MvPolynomial.C (MvPolynomial.X (Sum.inl () : FamilyJetIndex m n)))
    fun p => MvPolynomial.X (Sum.inr p)

theorem familyReshapeJetInv_comp_familyReshapeJet (m n : ℕ) :
    (familyReshapeJetInv m n).comp (familyReshapeJet m n) = RingHom.id _ := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [familyReshapeJet, familyReshapeJetInv]
  · intro s
    cases s with
    | inl x =>
        cases x
        simp [familyReshapeJet, familyReshapeJetInv]
    | inr p =>
        simp [familyReshapeJet, familyReshapeJetInv]

theorem familyReshapeJet_injective (m n : ℕ) :
    Function.Injective (familyReshapeJet m n) := by
  intro a b h
  have ha := RingHom.congr_fun (familyReshapeJetInv_comp_familyReshapeJet m n) a
  have hb := RingHom.congr_fun (familyReshapeJetInv_comp_familyReshapeJet m n) b
  rw [RingHom.comp_apply, RingHom.id_apply] at ha hb
  rw [← ha, ← hb, h]

/-- **Reshaping commutes with specialization.**  Specializing the polynomial coefficients at `z`
and evaluating at the jet values is evaluating the original at the full family jet vector. -/
theorem eval_specialize_familyReshapeJet (m n : ℕ) (z : ℂ) (v : Fin m × Fin (n + 1) → ℂ)
    (P : MvPolynomial (FamilyJetIndex m n) ℂ) :
    MvPolynomial.eval v (specializePolynomialCoefficients z (familyReshapeJet m n P))
      = MvPolynomial.eval (Sum.elim (fun _ => z) v) P := by
  rw [specializePolynomialCoefficients, MvPolynomial.eval_map]
  have hhom : ((MvPolynomial.eval₂Hom (Polynomial.evalRingHom z) v).comp (familyReshapeJet m n)) =
      (MvPolynomial.eval (Sum.elim (fun _ => z) v) : _ →+* ℂ) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [familyReshapeJet]
    · intro s
      cases s with
      | inl x =>
          cases x
          simp [familyReshapeJet]
      | inr p =>
          simp [familyReshapeJet]
  exact RingHom.congr_fun hhom P

/-- The jet coordinates of a family, as the pattern's dependent shift/order type. -/
def familySigmaEquiv (m n : ℕ) : (Σ _ : Fin m, Fin (n + 1)) ≃ Fin m × Fin (n + 1) :=
  Equiv.sigmaEquivProd _ _

/-- Renaming the family jet coordinates into the pattern's dependent form. -/
def renameToFamilyShiftJets {R : Type*} [CommSemiring R] (m n : ℕ)
    (Q : MvPolynomial (Fin m × Fin (n + 1)) R) :
    MvPolynomial (Σ _ : Fin m, Fin (n + 1)) R :=
  MvPolynomial.rename (familySigmaEquiv m n).symm Q

theorem renameToFamilyShiftJets_injective {R : Type*} [CommSemiring R] (m n : ℕ) :
    Function.Injective (renameToFamilyShiftJets (R := R) m n) :=
  MvPolynomial.rename_injective _ (familySigmaEquiv m n).symm.injective

end

end GaloisForLFunctions.HTGeometry
