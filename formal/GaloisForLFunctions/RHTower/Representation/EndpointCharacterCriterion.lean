import GaloisForLFunctions.RHTower.Representation.EndpointHankelReceiver
import GaloisForLFunctions.RHTower.Representation.EndpointCycleReality
import GaloisForLFunctions.HTGeometry.SymmetricCharacters.CycleCharacterCoherence
import GaloisForLFunctions.HTGeometry.RealPositiveConeDeterminantMonotone
import GaloisForLFunctions.RHTower.XiSquaredEulerAntiLownerHankelEndpoint

/-!
# The arithmetic symmetric-group character criterion

Completed arithmetic response jets define normalized central class functions coherent under
extension by fixed points. Their complex Gram matrices are positive at every rank exactly
when RH holds. The cycle values equal the full endpoint divisor moments. This identifies the
precise arithmetic positivity obligation without assuming a positive representation exists.
-/

noncomputable section
open scoped Classical ComplexOrder

namespace RHTower
open GaloisForLFunctions.SymmetricCharacters

/-- The complex cycle-product class function prescribed entirely by completed arithmetic jets. -/
def xiEndpointArithmeticCharacter {X : Type*} [Fintype X] (σ : Equiv.Perm X) : ℂ :=
  (cycleMomentCharacter xiEndpointArithmeticCycle σ : ℝ)

theorem xiEndpointArithmeticCharacter_one {X : Type*} [Fintype X] :
    xiEndpointArithmeticCharacter (1 : Equiv.Perm X) = 1 := by
  simp [xiEndpointArithmeticCharacter, cycleMomentCharacter_one]

theorem xiEndpointArithmeticCharacter_conj {X : Type*} [Fintype X]
    (σ τ : Equiv.Perm X) :
    xiEndpointArithmeticCharacter (τ * σ * τ⁻¹) = xiEndpointArithmeticCharacter σ := by
  simp only [xiEndpointArithmeticCharacter, cycleMomentCharacter_conj]

/-- A cycle evaluates to its prescribed arithmetic response jet. -/
theorem xiEndpointArithmeticCharacter_formPerm {X : Type*} [Fintype X]
    (l : List X) (hl : l.Nodup) (hne : l ≠ []) :
    xiEndpointArithmeticCharacter l.formPerm =
      (xiEndpointArithmeticCycle (l.length - 1) : ℂ) := by
  rw [xiEndpointArithmeticCharacter, cycleMomentCharacter_formPerm
    xiEndpointArithmeticCycle
    (by rw [xiEndpointArithmeticCycle_eq_source, xiEndpointSourceCycle_zero]) l hl hne]

/-- The same cycle value is the full normalized complex endpoint power sum. -/
theorem xiEndpointArithmeticCharacter_formPerm_eq_moment {X : Type*} [Fintype X]
    (l : List X) (hl : l.Nodup) (hne : l ≠ []) :
    xiEndpointArithmeticCharacter l.formPerm =
      (∑' q, xiStripEdgeWeight q ^ l.length) / (xiEndpointColorMass : ℂ) ^ l.length := by
  rw [xiEndpointArithmeticCharacter_formPerm l hl hne, xiEndpointArithmeticCycle_complex]
  have hlen : l.length - 1 + 1 = l.length := by
    cases l <;> simp_all
  rw [hlen]

/-- The same arithmetic class function restricts along every inclusion by fixed positions. -/
theorem xiEndpointArithmeticCharacter_extendDomain {X Y : Type*}
    [Fintype X] [Fintype Y] (s : Y → Prop) [DecidablePred s]
    (e : X ≃ Subtype s) (σ : Equiv.Perm X) :
    xiEndpointArithmeticCharacter (σ.extendDomain e) = xiEndpointArithmeticCharacter σ := by
  simp only [xiEndpointArithmeticCharacter, cycleMomentCharacter_extendDomain]

/-- Positivity of the actual arithmetic class functions, for complex test vectors, is RH. -/
theorem xiEndpointArithmeticCharacter_posSemidef_iff_rh :
    (∀ (X J : Type) [Fintype X] [Fintype J] (g : J → Equiv.Perm X),
      Matrix.PosSemidef (fun i j => xiEndpointArithmeticCharacter ((g i)⁻¹ * g j))) ↔
      RiemannHypothesis := by
  constructor
  · intro h
    apply positive_xiEndpointArithmeticCycleFamily_iff_rh.mp
    intro X J _ _ g
    exact realMatrix_posSemidef_of_complexification (h X J g)
  · intro hRH X J _ _ g
    exact GaloisForLFunctions.HTGeometry.realPosSemidef_complex
      (positive_xiEndpointArithmeticCycleFamily_iff_rh.mpr hRH X J g)

end RHTower
