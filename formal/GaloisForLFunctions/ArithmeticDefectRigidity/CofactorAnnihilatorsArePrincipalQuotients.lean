import GaloisForLFunctions.ArithmeticDefectRigidity.TheCofactorLimitIsAWienerModule
import GaloisForLFunctions.HTGeometry.PrincipalIdealQuotientsLocalizeCharacterHulls

/-!
# Cofactor annihilators are principal ideal quotients

The Wiener ideal killing a selected cofactor vector is the principal
quotient of the cyclic annihilator. Its hull agrees with the original
hull wherever the selected coordinate is nonzero.
-/

noncomputable section
set_option autoImplicit false
open GaloisForLFunctions.ArithmeticOrientationTheory
open GaloisForLFunctions.HTGeometry
open WienerAlgebraAt

namespace GaloisForLFunctions.ArithmeticDefectRigidity.ActualCofactorLimit

/-- The ideal annihilating the cyclic orbit of one cofactor vector. -/
def cofactorAnnihilator {ε : SubcriticalDamping} (L : ActualCofactorLimit ε)
    (p : ℕ+) : Ideal (WienerAlgebraAt (1 / 2)) :=
  (annihilator L).colon
    (Ideal.span {pointMass (σ := 1 / 2) (p : ℕ)} : Set (WienerAlgebraAt (1 / 2)))

/-- Principal ideal division is exactly annihilation of the selected cyclic vector. -/
theorem mem_cofactorAnnihilator_iff {ε : SubcriticalDamping}
    (L : ActualCofactorLimit ε) (p : ℕ+) (a : WienerAlgebraAt (1 / 2)) :
    a ∈ cofactorAnnihilator L p ↔ wienerRepresentation L a (vector L p) = 0 := by
  change a ∈ (annihilator L).colon
    (Ideal.span {pointMass (σ := 1 / 2) (p : ℕ)} : Set (WienerAlgebraAt (1 / 2))) ↔ _
  rw [Ideal.mem_colon_span_singleton, mem_annihilator_iff, map_mul,
    wienerRepresentation_pointMass]
  simp only [mul_apply_eq_comp, dilation_vector, mul_one]

theorem annihilator_le_cofactorAnnihilator {ε : SubcriticalDamping}
    (L : ActualCofactorLimit ε) (p : ℕ+) :
    annihilator L ≤ cofactorAnnihilator L p := Ideal.le_colon

/-- A zero cofactor gives the whole algebra as its vector annihilator. -/
theorem cofactorAnnihilator_eq_top_iff {ε : SubcriticalDamping}
    (L : ActualCofactorLimit ε) (p : ℕ+) :
    cofactorAnnihilator L p = ⊤ ↔ vector L p = 0 := by
  rw [Ideal.eq_top_iff_one, mem_cofactorAnnihilator_iff, map_one]
  rfl

/-- Cofactor hulls retain precisely the original hull away from the selected
coordinate hyperplane; on that hyperplane only containment is forced. -/
theorem cofactor_hull_inclusions {ε : SubcriticalDamping}
    (L : ActualCofactorLimit ε) (p : ℕ+) :
    {ω ∈ moduleHull L | ω.ω p ≠ 0} ⊆
      {ω : BohrPoint | ∀ a ∈ cofactorAnnihilator L p,
        ArithmeticOrientationTheory.bohrEval (1 / 2) a.toFn ω = 0} ∧
    {ω : BohrPoint | ∀ a ∈ cofactorAnnihilator L p,
        ArithmeticOrientationTheory.bohrEval (1 / 2) a.toFn ω = 0} ⊆ moduleHull L := by
  constructor
  · rintro ω ⟨hω, hp⟩ a ha
    let χ := WienerAlgebraAt.bohrCharacter (1 / 2) ω
    have hχp : χ (pointMass (p : ℕ)) ≠ 0 := by
      change ArithmeticOrientationTheory.bohrEval (1 / 2) (pointMass (p : ℕ)).toFn ω ≠ 0
      rw [toFn_pointMass, bohrEval_pointMass (σ := 1 / 2) (n := (p : ℕ)) p.property.ne' ω]
      apply div_ne_zero hp
      rw [ne_eq, Complex.cpow_eq_zero_iff]
      exact fun hz => p.property.ne' (by exact_mod_cast hz.1)
    have hker : annihilator L ≤ RingHom.ker χ.toRingHom := by
      intro b hb
      exact hω b hb
    have hquot := (principal_colon_le_character_ker_iff
      (annihilator L) χ.toRingHom (pointMass (p : ℕ)) hχp).mpr hker
    exact hquot ha
  · intro ω hω a ha
    exact hω a (annihilator_le_cofactorAnnihilator L p ha)

end GaloisForLFunctions.ArithmeticDefectRigidity.ActualCofactorLimit

#print axioms GaloisForLFunctions.ArithmeticDefectRigidity.ActualCofactorLimit.mem_cofactorAnnihilator_iff
#print axioms GaloisForLFunctions.ArithmeticDefectRigidity.ActualCofactorLimit.cofactor_hull_inclusions
#print axioms GaloisForLFunctions.ArithmeticDefectRigidity.ActualCofactorLimit.cofactorAnnihilator_eq_top_iff
end
