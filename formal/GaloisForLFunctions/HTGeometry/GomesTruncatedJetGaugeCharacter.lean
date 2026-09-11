import GaloisForLFunctions.HTGeometry.GomesTruncatedJetInternalUnits
import GaloisForLFunctions.HTGeometry.GomesTruncatedJetAugmentation

/-!
# A split scalar character of the actual gauge group

The first matrix diagonal entry defines a character into nonzero complex
scalars. Literal scalar matrices provide a section, and the character gives
the determinant of every symmetry.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry.GammaFactorialFock

/-- The nonzero scalar coordinate of an actual invertible clock symmetry. -/
def gomesTruncatedJetGaugeCharacter (n : ℕ) (z : ℂ) :
    gomesTruncatedJetGaugeGroup n z →* ℂˣ :=
  (Units.map (gomesTruncatedJetAugmentation n z).toMonoidHom).comp
    (gomesTruncatedJetInternalUnitsEquiv n z).symm.toMonoidHom

/-- The scalar character is the actual first diagonal matrix entry. -/
theorem gomesTruncatedJetGaugeCharacter_val (n : ℕ) (z : ℂ)
    (u : gomesTruncatedJetGaugeGroup n z) :
    (gomesTruncatedJetGaugeCharacter n z u).val = u.val.val 0 0 := rfl

/-- Every nonzero scalar acts by its literal scalar matrix in every gauge group. -/
def gomesTruncatedJetScalarSection (n : ℕ) (z : ℂ) :
    ℂˣ →* gomesTruncatedJetGaugeGroup n z where
  toFun c := ⟨Units.map (algebraMap ℂ (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)).toMonoidHom c,
    (gomesTruncatedJetJointAlgebra n z).algebraMap_mem c.val⟩
  map_one' := by
    apply Subtype.ext
    exact map_one _
  map_mul' c d := by
    apply Subtype.ext
    exact map_mul _ c d

/-- The section is represented by the literal scalar matrix. -/
theorem gomesTruncatedJetScalarSection_val (n : ℕ) (z : ℂ) (c : ℂˣ) :
    (gomesTruncatedJetScalarSection n z c).val.val =
      algebraMap ℂ (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) c.val := rfl

/-- Reading the scalar of a scalar symmetry recovers the original nonzero complex number. -/
theorem gomesTruncatedJetGaugeCharacter_scalarSection (n : ℕ) (z : ℂ) (c : ℂˣ) :
    gomesTruncatedJetGaugeCharacter n z (gomesTruncatedJetScalarSection n z c) = c := by
  apply Units.ext
  rw [gomesTruncatedJetGaugeCharacter_val, gomesTruncatedJetScalarSection_val]
  simp [Matrix.algebraMap_eq_diagonal]

/-- Every nonzero complex scalar occurs as the character of an actual symmetry. -/
theorem gomesTruncatedJetGaugeCharacter_surjective (n : ℕ) (z : ℂ) :
    Function.Surjective (gomesTruncatedJetGaugeCharacter n z) := by
  intro c
  exact ⟨gomesTruncatedJetScalarSection n z c, gomesTruncatedJetGaugeCharacter_scalarSection n z c⟩

/-- Distinct nonzero scalars give distinct actual clock symmetries. -/
theorem gomesTruncatedJetScalarSection_injective (n : ℕ) (z : ℂ) :
    Function.Injective (gomesTruncatedJetScalarSection n z) := by
  intro c d h
  have hc := congrArg (gomesTruncatedJetGaugeCharacter n z) h
  simpa only [gomesTruncatedJetGaugeCharacter_scalarSection] using hc

/-- The character supplies the exact determinant of every actual gauge transformation. -/
theorem gomesTruncatedJetGaugeCharacter_det (n : ℕ) (z : ℂ)
    (u : gomesTruncatedJetGaugeGroup n z) :
    u.val.val.det = (gomesTruncatedJetGaugeCharacter n z u).val ^ (n + 1) :=
  gomesTruncatedJetJointAlgebra_det n z ⟨u.val.val, u.property⟩

end GaloisForLFunctions.HTGeometry.GammaFactorialFock
