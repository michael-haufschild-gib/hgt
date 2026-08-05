import GaloisForLFunctions.HTGeometry.GammaOrientedAlienCharge

/-!
# Both orientations of an affine Gamma factor occur

An oriented affine Gamma factor carries a nonzero slope, and the reflection normalization branches on
its sign.  Both branches are occupied: the unit slope gives a positive factor and the negated unit
slope a negative one, so neither branch of the normalization is vacuous.
-/

namespace GaloisForLFunctions.HTGeometry

/-- The affine Gamma factor of unit slope. -/
def unitOrientedAffineGammaFactor (offset : ℂ) (m : ℤ) : OrientedAffineGammaFactor where
  slope := 1
  offset := offset
  multiplicity := m
  slope_ne_zero := one_ne_zero

/-- The affine Gamma factor of negated unit slope. -/
def negUnitOrientedAffineGammaFactor (offset : ℂ) (m : ℤ) : OrientedAffineGammaFactor where
  slope := -1
  offset := offset
  multiplicity := m
  slope_ne_zero := neg_ne_zero.mpr one_ne_zero

@[simp] theorem unitOrientedAffineGammaFactor_slope (offset : ℂ) (m : ℤ) :
    (unitOrientedAffineGammaFactor offset m).slope = 1 := rfl

@[simp] theorem negUnitOrientedAffineGammaFactor_slope (offset : ℂ) (m : ℤ) :
    (negUnitOrientedAffineGammaFactor offset m).slope = -1 := rfl

/-- **The positive-orientation branch is occupied.** -/
theorem slope_pos_unitOrientedAffineGammaFactor (offset : ℂ) (m : ℤ) :
    0 < (unitOrientedAffineGammaFactor offset m).slope := by
  rw [unitOrientedAffineGammaFactor_slope]
  exact one_pos

/-- **The negative-orientation branch is occupied.** -/
theorem slope_neg_negUnitOrientedAffineGammaFactor (offset : ℂ) (m : ℤ) :
    ¬ 0 < (negUnitOrientedAffineGammaFactor offset m).slope := by
  rw [negUnitOrientedAffineGammaFactor_slope]
  norm_num

/-- So both orientations exist at every offset and multiplicity. -/
theorem exists_orientedAffineGammaFactor_slope_pos_and_not (offset : ℂ) (m : ℤ) :
    (∃ f : OrientedAffineGammaFactor, 0 < f.slope) ∧
      (∃ f : OrientedAffineGammaFactor, ¬ 0 < f.slope) :=
  ⟨⟨_, slope_pos_unitOrientedAffineGammaFactor offset m⟩,
    ⟨_, slope_neg_negUnitOrientedAffineGammaFactor offset m⟩⟩

end GaloisForLFunctions.HTGeometry
