import GaloisForLFunctions.ArithmeticPositiveDuality.AContinuousArchimedeanSpectrumIsSeenByTheSuccessor
import Mathlib.GroupTheory.Index

/-!
# The positive rational affine subgroup

Slope sign gives index two. Translations, positive dilations, and the slope map give its
canonical homomorphisms.
-/

open GaloisForLFunctions.ArithmeticPositiveDuality
noncomputable section
namespace GaloisForLFunctions.BiarithmeticGeometry

/-- Rational translations, regarded as positive-slope affine maps. -/
def posAffineTranslation (b : ℚ) : posAffine :=
  ⟨translation b, by change 0 < affSlope (translation b); rw [affSlope_translation]; exact one_pos⟩

/-- Positive rational dilations as elements of the positive affine group. -/
def posAffineDilation : posUnits →* posAffine where
  toFun u := ⟨dilation u, by change 0 < affSlope (dilation u); rw [affSlope_dilation]; exact u.property⟩
  map_one' := Subtype.ext (map_one dilation)
  map_mul' u v := Subtype.ext (map_mul dilation (u : ℚˣ) (v : ℚˣ))

/-- The positive slope homomorphism. -/
def posAffineSlope : posAffine →* posUnits where
  toFun g := ⟨Units.mk0 (affSlope g) (affSlope_ne_zero g), g.property⟩
  map_one' := Subtype.ext (Units.ext affSlope_one)
  map_mul' g h := Subtype.ext (Units.ext (affSlope_mul g h))

/-- Positive rational affine maps have exactly two cosets, distinguished by slope sign. -/
theorem posAffine_index : posAffine.index = 2 := by
  apply Subgroup.index_eq_two_iff.mpr
  refine ⟨dilation (-1), fun g => ?_⟩
  change Xor (0 < affSlope (g * dilation (-1))) (0 < affSlope g)
  rw [affSlope_mul, affSlope_dilation]
  change Xor (0 < affSlope g * (-1 : ℚ)) (0 < affSlope g)
  rw [xor_iff_iff_not]
  rcases lt_or_gt_of_ne (affSlope_ne_zero g) with hn | hp
  · constructor
    · exact fun _ => not_lt_of_ge hn.le
    · intro _
      linarith only [hn]
  · constructor
    · intro h
      linarith only [h, hp]
    · exact fun h => (h hp).elim

instance posAffine_finiteIndex : posAffine.FiniteIndex :=
  ⟨by rw [posAffine_index]; decide⟩

#print axioms posAffineDilation
#print axioms posAffineSlope
#print axioms posAffine_index
end GaloisForLFunctions.BiarithmeticGeometry
