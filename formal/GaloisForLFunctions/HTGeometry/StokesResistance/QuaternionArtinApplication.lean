import GaloisForLFunctions.HTGeometry.StokesResistance.FiniteGroupCharacter
import GaloisForLFunctions.RHTower.Deninger.DeningerQ8ActualGroupRepresentation

/-!
# Quaternionic Artin application of Stokes symmetry counting

This module mechanically applies Moreau's finite-group Reynolds, character-average, and stacked
defect formulas to the corpus's literal two-dimensional representation of `QuaternionGroup 2`.
The central involution acts by `-1`, so the fixed carrier is zero. Consequently the normalized
character sum and Reynolds average vanish, while the stacked invariance equations are injective.

Hydrodynamically, this is the same mechanism by which an order-two central symmetry removes a
vector response. Arithmetically, it says the quaternionic Artin carrier has no trivial summand.
-/

open scoped BigOperators

noncomputable section

namespace GaloisForLFunctions.HTGeometry.StokesResistance

open MonoidAlgebra Representation
open RHTower

/-- The literal quaternionic representation has no nonzero invariant vector. -/
theorem deningerQ8Representation_invariants_eq_bot :
    Representation.invariants deningerQ8Representation = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro v hv
  have hfix := hv (QuaternionGroup.a 2)
  rw [deningerQ8Representation_central_apply] at hfix
  apply Prod.ext
  · exact CharZero.neg_eq_self_iff.mp (by simpa using congrArg Prod.fst hfix)
  · exact CharZero.neg_eq_self_iff.mp (by simpa using congrArg Prod.snd hfix)

/-- Moreau's normalized character average vanishes for the literal `Q₈` representation. -/
theorem deningerQ8_character_average_eq_zero :
    (Fintype.card (QuaternionGroup 2) : ℂ)⁻¹ *
      ∑ g : QuaternionGroup 2,
        LinearMap.trace ℂ Q8Carrier (deningerQ8Representation g) = 0 := by
  rw [← finrank_invariants_eq_character_average deningerQ8Representation,
    deningerQ8Representation_invariants_eq_bot]
  simp

/-- Reynolds averaging annihilates the complete literal quaternionic carrier. -/
theorem finiteGroupAverage_deningerQ8Representation_eq_zero :
    finiteGroupAverage deningerQ8Representation = 0 := by
  apply LinearMap.ext
  intro v
  have hv := finiteGroupAverage_mem_invariants deningerQ8Representation v
  rw [deningerQ8Representation_invariants_eq_bot, Submodule.mem_bot] at hv
  simpa only [LinearMap.zero_apply] using hv

/-- The stacked `Q₈` invariance-defect system has trivial kernel. -/
theorem ker_deningerQ8_invarianceDefect_eq_bot :
    LinearMap.ker (invarianceDefect deningerQ8Representation) = ⊥ := by
  rw [ker_invarianceDefect, deningerQ8Representation_invariants_eq_bot]

end GaloisForLFunctions.HTGeometry.StokesResistance
