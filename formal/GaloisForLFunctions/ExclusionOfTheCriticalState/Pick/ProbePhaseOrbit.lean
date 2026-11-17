import GaloisForLFunctions.ExclusionOfTheCriticalState.Pick.ProbeSectorGrams
import Mathlib.Analysis.Complex.Circle

/-!
# Orbital phase symmetry of the Weil sectors

Multiplying the negative reflection sector by a unit complex number gives an
orbital circle action. Both the Hilbert pairing and the indefinite Weil
pairing are invariant. Orbit displacement measures exactly the negative
sector, whereas overlap records the masses of both sectors.

This is the two-frequency realization of orbital phase geometry in
Chen, *Underlying orbital U(1) symmetry in quantum limit cycles*, §IV.
-/

noncomputable section
namespace GaloisForLFunctions.ExclusionOfTheCriticalState.ProbeWalk
open scoped ComplexConjugate

theorem positivePart_add_negativePart (x : ZeroSpace) :
    positivePart x + negativePart x = x := by
  unfold positivePart negativePart
  module

theorem positivePart_add (x y : ZeroSpace) :
    positivePart (x + y) = positivePart x + positivePart y := by
  simp only [positivePart, map_add]
  module

theorem negativePart_add (x y : ZeroSpace) :
    negativePart (x + y) = negativePart x + negativePart y := by
  simp only [negativePart, map_add]
  module

theorem positivePart_smul (c : ℂ) (x : ZeroSpace) :
    positivePart (c • x) = c • positivePart x := by
  simp only [positivePart, map_smul]
  module

theorem negativePart_smul (c : ℂ) (x : ZeroSpace) :
    negativePart (c • x) = c • negativePart x := by
  simp only [negativePart, map_smul]
  module

theorem positivePart_idempotent (x : ZeroSpace) :
    positivePart (positivePart x) = positivePart x := by
  rw [positivePart, zeroReflection_positivePart]
  module

theorem negativePart_idempotent (x : ZeroSpace) :
    negativePart (negativePart x) = negativePart x := by
  rw [negativePart, zeroReflection_negativePart]
  module

theorem positivePart_negativePart (x : ZeroSpace) :
    positivePart (negativePart x) = 0 := by
  rw [positivePart, zeroReflection_negativePart, add_neg_cancel, smul_zero]

theorem negativePart_positivePart (x : ZeroSpace) :
    negativePart (positivePart x) = 0 := by
  rw [negativePart, zeroReflection_positivePart, sub_self, smul_zero]

/-- Opposite reflection sectors are orthogonal for the ordinary Hilbert pairing. -/
theorem sector_inner_orthogonal (x y : ZeroSpace) :
    inner ℂ (positivePart x) (negativePart y) = 0 := by
  have h := zeroReflection_inner_left (positivePart x) (negativePart y)
  rw [zeroReflection_positivePart, zeroReflection_negativePart, inner_neg_right] at h
  linear_combination (1 / 2 : ℂ) * h

theorem sector_inner_orthogonal_rev (x y : ZeroSpace) :
    inner ℂ (negativePart x) (positivePart y) = 0 := by
  rw [← inner_conj_symm, sector_inner_orthogonal, map_zero]

/-- Rotate only the negative Weil sector; this leaves the actual reflection fixed. -/
def phaseRotate (u : Circle) (x : ZeroSpace) : ZeroSpace :=
  positivePart x + (u : ℂ) • negativePart x

theorem positivePart_phaseRotate (u : Circle) (x : ZeroSpace) :
    positivePart (phaseRotate u x) = positivePart x := by
  rw [phaseRotate, positivePart_add, positivePart_idempotent,
    positivePart_smul, positivePart_negativePart, smul_zero, add_zero]

theorem negativePart_phaseRotate (u : Circle) (x : ZeroSpace) :
    negativePart (phaseRotate u x) = (u : ℂ) • negativePart x := by
  rw [phaseRotate, negativePart_add, negativePart_positivePart,
    negativePart_smul, negativePart_idempotent, zero_add]

/-- Sector phase rotations form an exact circle action on the actual zero space. -/
theorem phaseRotate_mul (u v : Circle) (x : ZeroSpace) :
    phaseRotate u (phaseRotate v x) = phaseRotate (u * v) x := by
  rw [phaseRotate, positivePart_phaseRotate, negativePart_phaseRotate,
    phaseRotate, Circle.coe_mul, mul_smul]

theorem phaseRotate_one (x : ZeroSpace) : phaseRotate 1 x = x := by
  rw [phaseRotate, Circle.coe_one, one_smul, positivePart_add_negativePart]

/-- All ordinary pairings survive a common sector phase rotation. -/
theorem inner_phaseRotate (u : Circle) (x y : ZeroSpace) :
    inner ℂ (phaseRotate u x) (phaseRotate u y) = inner ℂ x y := by
  simp only [phaseRotate, inner_add_left, inner_add_right,
    inner_smul_left, inner_smul_right, sector_inner_orthogonal,
    sector_inner_orthogonal_rev, mul_zero, zero_add, add_zero]
  rw [← mul_assoc, Complex.mul_conj, Circle.normSq_coe, Complex.ofReal_one, one_mul]
  exact sector_inner_sum y x

/-- The reflection commutes with orbital phase rotations. -/
theorem zeroReflection_phaseRotate (u : Circle) (x : ZeroSpace) :
    zeroReflection (phaseRotate u x) = phaseRotate u (zeroReflection x) := by
  simp only [phaseRotate, positivePart, negativePart, map_add, map_sub,
    map_smul, zeroReflection_involutive]

/-- Rotating sectors preserves the indefinite Weil pairing, not merely its norm bound. -/
theorem weil_inner_phaseRotate (u : Circle) (x y : ZeroSpace) :
    inner ℂ (zeroReflection (phaseRotate u x)) (phaseRotate u y) =
      inner ℂ (zeroReflection x) y := by
  rw [zeroReflection_phaseRotate, inner_phaseRotate]

/-- Relative phases see the two sector masses separately. -/
theorem phaseRotate_overlap (u v : Circle) (x y : ZeroSpace) :
    inner ℂ (phaseRotate u x) (phaseRotate v y) =
      inner ℂ (positivePart x) (positivePart y) +
        (conj (u : ℂ) * (v : ℂ)) * inner ℂ (negativePart x) (negativePart y) := by
  simp only [phaseRotate, inner_add_left, inner_add_right,
    inner_smul_left, inner_smul_right, sector_inner_orthogonal,
    sector_inner_orthogonal_rev, mul_zero, zero_add, add_zero]
  ring

/-- Orbit chords depend only on relative phase and negative-sector size. -/
theorem norm_phaseRotate_sub (u v : Circle) (x : ZeroSpace) :
    ‖phaseRotate u x - phaseRotate v x‖ =
      ‖(u : ℂ) - (v : ℂ)‖ * ‖negativePart x‖ := by
  have h : phaseRotate u x - phaseRotate v x =
      ((u : ℂ) - (v : ℂ)) • negativePart x := by
    unfold phaseRotate
    module
  rw [h, norm_smul]

/-- A stationary phase orbit is precisely the positive reflection sector. -/
theorem phaseRotate_all_fixed_iff (x : ZeroSpace) :
    (∀ u : Circle, phaseRotate u x = x) ↔ zeroReflection x = x := by
  constructor
  · intro h
    have hm := h (-1)
    have hr : phaseRotate (-1) x = zeroReflection x := by
      simp only [phaseRotate, positivePart, negativePart]
      norm_num
      module
    rwa [hr] at hm
  · intro h u
    have hn : negativePart x = 0 := by rw [negativePart, h, sub_self, smul_zero]
    rw [phaseRotate, hn, smul_zero, add_zero]
    simpa only [hn, add_zero] using positivePart_add_negativePart x

#print axioms phaseRotate_mul
#print axioms inner_phaseRotate
#print axioms weil_inner_phaseRotate
#print axioms phaseRotate_overlap
#print axioms norm_phaseRotate_sub
#print axioms phaseRotate_all_fixed_iff

end GaloisForLFunctions.ExclusionOfTheCriticalState.ProbeWalk
