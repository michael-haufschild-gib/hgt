import GaloisForLFunctions.RHTower.CCMActualHeadWallGramLightConeReflectionFiber
import GaloisForLFunctions.RHTower.CCMRestrictedWeilPoleHingeFirstContact

/-!
# Reflection obstruction for wall-light control at a CCM pole first contact

The literal restricted-Weil source is reflection-even as a full sesquilinear form: its even and
odd channels have no cross term.  In contrast, the oriented wall-chord jet is reflection-odd.
The only first-contact vectors certified by the exact pole compression are the two reflection
parity poles.  Therefore the wall jet vanishes on both of them.

This rules out a specific proposed landing mechanism: a source-faithful producer whose only new
signed datum is the oriented wall-light commutator cannot exclude the literal pole first contact.
It does not assert a sign for the completed source.  A surviving mechanism must retain an
even, marked boundary datum that is not reduced to this reflection-odd jet.
-/

open Complex MeasureTheory

noncomputable section
namespace RHTower

/-- Reflection fixes the literal even pole vector. -/
theorem ccmArchimedeanFormReflection_polarParity_plus
    (a : SuzukiPositiveAperture) :
    ccmArchimedeanFormReflection a (ccmPolarParityFormVector a 1) =
      ccmPolarParityFormVector a 1 := by
  unfold ccmPolarParityFormVector
  rw [map_add, map_smul, ccmArchimedeanFormReflection_polar,
    ccmArchimedeanFormReflection_polar]
  norm_num
  module

/-- Reflection negates the literal odd pole vector. -/
theorem ccmArchimedeanFormReflection_polarParity_minus
    (a : SuzukiPositiveAperture) :
    ccmArchimedeanFormReflection a (ccmPolarParityFormVector a (-1)) =
      -ccmPolarParityFormVector a (-1) := by
  unfold ccmPolarParityFormVector
  rw [map_add, map_smul, ccmArchimedeanFormReflection_polar,
    ccmArchimedeanFormReflection_polar]
  norm_num

/-- The full completed restricted-Weil form has no even--odd cross channel. -/
theorem ccmRestrictedWeilForm_evenPart_oddPart_eq_zero
    (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a) :
    ccmRestrictedWeilForm a (ccmRestrictedWeilEvenPart a u)
      (ccmRestrictedWeilOddPart a u) = 0 := by
  have hreflection := ccmRestrictedWeilForm_reflection a
    (ccmRestrictedWeilEvenPart a u) (ccmRestrictedWeilOddPart a u)
  rw [ccmArchimedeanFormReflection_evenPart,
    ccmArchimedeanFormReflection_oddPart] at hreflection
  have hneg :
      ccmRestrictedWeilForm a (ccmRestrictedWeilEvenPart a u)
        (-ccmRestrictedWeilOddPart a u) =
      -ccmRestrictedWeilForm a (ccmRestrictedWeilEvenPart a u)
        (ccmRestrictedWeilOddPart a u) := by
    simp [ccmRestrictedWeilForm]
    ring
  rw [hneg] at hreflection
  linear_combination (-1 / 2 : ℂ) * hreflection

/-- The oriented wall-chord jet vanishes on the literal even pole. -/
theorem ccmActualHeadWallChordJetCurrent_polarParity_plus_zero
    (a : SuzukiPositiveAperture) (p : Nat.Primes) (e : ℕ) :
    ccmActualHeadWallChordJetCurrent p e
      (ccmArchimedeanWeightedToL2 (ccmPolarParityFormVector a 1).1) = 0 := by
  have hreflection := ccmActualHeadWallChordJetCurrent_formReflection a
    (ccmPolarParityFormVector a 1) p e
  rw [ccmArchimedeanFormReflection_polarParity_plus] at hreflection
  linarith

/-- The oriented wall-chord jet vanishes on the literal odd pole. -/
theorem ccmActualHeadWallChordJetCurrent_polarParity_minus_zero
    (a : SuzukiPositiveAperture) (p : Nat.Primes) (e : ℕ) :
    ccmActualHeadWallChordJetCurrent p e
      (ccmArchimedeanWeightedToL2 (ccmPolarParityFormVector a (-1)).1) = 0 := by
  have hreflection := ccmActualHeadWallChordJetCurrent_formReflection a
    (ccmPolarParityFormVector a (-1)) p e
  rw [ccmArchimedeanFormReflection_polarParity_minus] at hreflection
  have hneg :
      (↑(-ccmPolarParityFormVector a (-1)) : CCMArchimedeanFourierL2) =
        -↑(ccmPolarParityFormVector a (-1)) := rfl
  rw [hneg, map_neg, ccmActualHeadWallChordJetCurrent_neg] at hreflection
  linarith

/-- Every literal parity pole is invisible to the oriented wall-chord jet. -/
theorem ccmActualHeadWallChordJetCurrent_polarParity_zero
    (a : SuzukiPositiveAperture) (r : ℝ) (hr : r = 1 ∨ r = -1)
    (p : Nat.Primes) (e : ℕ) :
    ccmActualHeadWallChordJetCurrent p e
      (ccmArchimedeanWeightedToL2 (ccmPolarParityFormVector a r).1) = 0 := by
  rcases hr with rfl | rfl
  · exact ccmActualHeadWallChordJetCurrent_polarParity_plus_zero a p e
  · exact ccmActualHeadWallChordJetCurrent_polarParity_minus_zero a p e

/-- If the literal pole compression reaches its first zero, that zero is invisible to every
oriented wall-chord jet. -/
theorem exists_poleFirstContact_wallChordJet_zero
    (h : CCMPoleCompressionFirstContact) :
    ∃ (a : SuzukiPositiveAperture) (r : ℝ),
      (r = 1 ∨ r = -1) ∧
        ccmRestrictedWeilSourceQuadratic a (ccmPolarParityFormVector a r) = 0 ∧
        ∀ (p : Nat.Primes) (e : ℕ),
          ccmActualHeadWallChordJetCurrent p e
            (ccmArchimedeanWeightedToL2 (ccmPolarParityFormVector a r).1) = 0 := by
  rcases h with ⟨a, r, hr, hzero, _, _⟩
  exact ⟨a, r, hr, hzero, fun p e =>
    ccmActualHeadWallChordJetCurrent_polarParity_zero a r hr p e⟩

end RHTower
