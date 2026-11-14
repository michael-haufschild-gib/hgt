import GaloisForLFunctions.FamilyContinuationTheory.Quartic.GaussianPrimary

/-!
# The ramified sign of a primary Gaussian integer

Primary residues modulo `(1+i)^4` are represented by `1` and `1+(1+i)^3`.
Their signs are `1` and `-1`. The sign is multiplicative and disappears on
fourth powers, as required when a quartic twist is reduced to its fourth-power-free part.
-/

namespace GaloisForLFunctions.FamilyContinuationTheory.Quartic

open RHTower.GaussianTwoSquares

/-- The two primary residue classes modulo four, in Gaussian coordinates. -/
theorem primary_residue_dichotomy (z : primarySubmonoid) :
    (z.val.re % 4 = 1 ∧ z.val.im % 4 = 0) ∨
      (z.val.re % 4 = 3 ∧ z.val.im % 4 = 2) := by
  have h := (isPrimary_iff z.val).mp z.property
  simp only [Int.dvd_iff_emod_eq_zero] at h
  omega

/-- The sign distinguishing the two primary residues modulo `(1+i)^4`. -/
def primarySign (z : primarySubmonoid) : ℤ :=
  if z.val.im % 4 = 0 then 1 else -1

/-- A primary element in the nontrivial ramified residue class. -/
def primaryRamifiedGenerator : primarySubmonoid :=
  ⟨⟨-1, 2⟩, (isPrimary_iff _).mpr (by norm_num)⟩

/-- The ramified character is nontrivial. -/
theorem primarySign_generator : primarySign primaryRamifiedGenerator = -1 := by
  norm_num [primarySign, primaryRamifiedGenerator]

/-- The ramified sign is a multiplicative character on primary elements. -/
theorem primarySign_mul (z w : primarySubmonoid) :
    primarySign (z * w) = primarySign z * primarySign w := by
  have hmul : (z.val * w.val).im % 4 =
      ((z.val.re % 4) * (w.val.im % 4) + (z.val.im % 4) * (w.val.re % 4)) % 4 := by
    rw [Zsqrtd.im_mul, Int.add_emod, Int.mul_emod, Int.mul_emod]
    omega
  rcases primary_residue_dichotomy z with ⟨hr, hi⟩ | ⟨hr, hi⟩ <;>
    rcases primary_residue_dichotomy w with ⟨kr, ki⟩ | ⟨kr, ki⟩ <;>
    norm_num only [hr, hi, kr, ki] at hmul <;>
    simp only [primarySign, Submonoid.coe_mul, hmul, hi, ki] <;> norm_num

/-- Every ramified sign has order dividing two. -/
theorem primarySign_sq (z : primarySubmonoid) : primarySign z ^ 2 = 1 := by
  unfold primarySign
  split_ifs <;> norm_num

/-- The ramified character as a monoid homomorphism. -/
def primarySignHom : primarySubmonoid →* ℤ where
  toFun := primarySign
  map_one' := by norm_num [primarySign]
  map_mul' := primarySign_mul

/-- Fourth-power extraction leaves the ramified sign unchanged. -/
theorem primarySign_fourth (z : primarySubmonoid) : primarySign (z ^ 4) = 1 := by
  change primarySignHom (z ^ 4) = 1
  rw [map_pow]
  change primarySign z ^ 4 = 1
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, primarySign_sq, one_pow]

/-- The sign depends only on the fourth-power-free factor. -/
theorem primarySign_mul_fourth (z w : primarySubmonoid) :
    primarySign (z * w ^ 4) = primarySign z := by
  rw [primarySign_mul, primarySign_fourth, mul_one]

end GaloisForLFunctions.FamilyContinuationTheory.Quartic
