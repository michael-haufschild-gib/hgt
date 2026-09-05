import Mathlib

/-!
# Coprime block carry transgression

The Euler-deletion coefficient `1 - q * [q ∣ n]` has zero mass on a `q`-block.
This file studies the first genuinely mixed finite cell: pointwise fusion of the `2`- and
`3`-deletion coefficients on their common six-block.

Both orientations have zero mass, but their first moments are opposite and nonzero.  Thus CRT
fusion preserves primary cancellation while retaining a signed secondary datum.  Everything here
is finite arithmetic.  No analytic continuation, functional equation, spectral representation, or
positivity input is used.
-/

namespace RHTower

open scoped BigOperators

/-- Integer coefficient obtained by deleting the formal Euler factor at `q`. -/
def blockDeletionCoefficient (q n : ℕ) : ℤ :=
  1 - (q : ℤ) * (if q ∣ n then 1 else 0)

/-- Pointwise fusion of the dyadic and triadic Euler-deletion coefficients. -/
def coprimeBlockCarrier (n : ℕ) : ℤ :=
  blockDeletionCoefficient 2 n * blockDeletionCoefficient 3 n

/-- The mixed carrier is exactly pointwise fusion; no analytic operation enters its definition. -/
theorem coprimeBlockCarrier_fusion (n : ℕ) :
    coprimeBlockCarrier n =
      blockDeletionCoefficient 2 n * blockDeletionCoefficient 3 n := rfl

/-- Inclusion--exclusion exposes the mixed `2 × 3` corner explicitly. -/
theorem coprimeBlockCarrier_inclusionExclusion (n : ℕ) :
    coprimeBlockCarrier n =
      1 - 2 * (if 2 ∣ n then 1 else 0) - 3 * (if 3 ∣ n then 1 else 0) +
        6 * (if 6 ∣ n then 1 else 0) := by
  have hcop : Nat.Coprime 2 3 := by norm_num
  by_cases h2 : 2 ∣ n
  · by_cases h3 : 3 ∣ n
    · have h6 : 6 ∣ n := by
        have h23 : 2 * 3 ∣ n := hcop.mul_dvd_of_dvd_of_dvd h2 h3
        norm_num at h23 ⊢
        exact h23
      simp [coprimeBlockCarrier, blockDeletionCoefficient, h2, h3, h6]
    · have h6 : ¬6 ∣ n := by
        intro h
        exact h3 ((by norm_num : 3 ∣ 6).trans h)
      simp [coprimeBlockCarrier, blockDeletionCoefficient, h2, h3, h6]
  · have h6 : ¬6 ∣ n := by
      intro h
      exact h2 ((by norm_num : 2 ∣ 6).trans h)
    simp [coprimeBlockCarrier, blockDeletionCoefficient, h2, h6]

/-- Reverse the common six-cell while keeping its labels `1, ..., 6`. -/
def reverseCoprimeBlockCarrier (n : ℕ) : ℤ :=
  coprimeBlockCarrier (7 - n)

/-- Total charge of the forward common block. -/
def coprimeBlockMass : ℤ :=
  ∑ k ∈ Finset.range 6, coprimeBlockCarrier (k + 1)

/-- First labelled moment of the forward common block. -/
def coprimeBlockFirstMoment : ℤ :=
  ∑ k ∈ Finset.range 6, (k + 1 : ℤ) * coprimeBlockCarrier (k + 1)

/-- Total charge of the reversed common block. -/
def reverseCoprimeBlockMass : ℤ :=
  ∑ k ∈ Finset.range 6, reverseCoprimeBlockCarrier (k + 1)

/-- First labelled moment of the reversed common block. -/
def reverseCoprimeBlockFirstMoment : ℤ :=
  ∑ k ∈ Finset.range 6, (k + 1 : ℤ) * reverseCoprimeBlockCarrier (k + 1)

/-- Difference between the two oriented first moments. -/
def coprimeBlockOrientationCharge : ℤ :=
  coprimeBlockFirstMoment - reverseCoprimeBlockFirstMoment

/-- Cyclic residue of the apparent orientation charge. -/
def coprimeBlockOrientationResidue : ZMod 6 :=
  coprimeBlockOrientationCharge

/-- One cyclic change of block origin. -/
def rotateCoprimeBlockCarrier (n : ℕ) : ℤ :=
  coprimeBlockCarrier (n % 6 + 1)

/-- First moment after the cyclic origin change `1, ..., 6` to `2, ..., 6, 1`. -/
def rotateCoprimeBlockFirstMoment : ℤ :=
  ∑ k ∈ Finset.range 6, (k + 1 : ℤ) * rotateCoprimeBlockCarrier (k + 1)

/-- The literal fused `2 × 3` cell. -/
theorem coprimeBlockCarrier_table :
    coprimeBlockCarrier 1 = 1 ∧
    coprimeBlockCarrier 2 = -1 ∧
    coprimeBlockCarrier 3 = -2 ∧
    coprimeBlockCarrier 4 = -1 ∧
    coprimeBlockCarrier 5 = 1 ∧
    coprimeBlockCarrier 6 = 2 := by
  norm_num [coprimeBlockCarrier, blockDeletionCoefficient]

/-- Primary cancellation survives coprime pointwise fusion. -/
theorem coprimeBlockMass_eq_zero : coprimeBlockMass = 0 := by
  norm_num [coprimeBlockMass, coprimeBlockCarrier, blockDeletionCoefficient,
    Finset.sum_range_succ]

/-- The forward cell retains a positive first moment after its mass cancels. -/
theorem coprimeBlockFirstMoment_eq_six : coprimeBlockFirstMoment = 6 := by
  norm_num [coprimeBlockFirstMoment, coprimeBlockCarrier, blockDeletionCoefficient,
    Finset.sum_range_succ]

/-- Reversal preserves primary cancellation. -/
theorem reverseCoprimeBlockMass_eq_zero : reverseCoprimeBlockMass = 0 := by
  norm_num [reverseCoprimeBlockMass, reverseCoprimeBlockCarrier, coprimeBlockCarrier,
    blockDeletionCoefficient, Finset.sum_range_succ]

/-- Reversal flips the surviving first moment. -/
theorem reverseCoprimeBlockFirstMoment_eq_neg_six : reverseCoprimeBlockFirstMoment = -6 := by
  norm_num [reverseCoprimeBlockFirstMoment, reverseCoprimeBlockCarrier, coprimeBlockCarrier,
    blockDeletionCoefficient, Finset.sum_range_succ]

/-- The orientation charge is nonzero although both oriented cells have zero mass. -/
theorem coprimeBlockOrientationCharge_eq_twelve : coprimeBlockOrientationCharge = 12 := by
  rw [coprimeBlockOrientationCharge, coprimeBlockFirstMoment_eq_six,
    reverseCoprimeBlockFirstMoment_eq_neg_six]
  norm_num

/-- The apparent integer orientation changes when the block origin is rotated. -/
theorem rotateCoprimeBlockFirstMoment_eq_twelve : rotateCoprimeBlockFirstMoment = 12 := by
  norm_num [rotateCoprimeBlockFirstMoment, rotateCoprimeBlockCarrier, coprimeBlockCarrier,
    blockDeletionCoefficient, Finset.sum_range_succ]

/-- The only cyclically intrinsic residue of the apparent orientation charge is zero. -/
theorem coprimeBlockOrientationResidue_eq_zero : coprimeBlockOrientationResidue = 0 := by
  rw [coprimeBlockOrientationResidue, coprimeBlockOrientationCharge_eq_twelve]
  change ((12 : ℕ) : ZMod 6) = 0
  rw [show 12 = 2 * 6 by norm_num, Nat.cast_mul, ZMod.natCast_self, mul_zero]

/-- No-go certificate: the integer first moment is origin-sensitive and its cyclic residue dies. -/
theorem coprimeBlockMomentOrientation_noGo :
    rotateCoprimeBlockFirstMoment ≠ coprimeBlockFirstMoment ∧
      coprimeBlockOrientationResidue = 0 := by
  constructor
  · rw [rotateCoprimeBlockFirstMoment_eq_twelve, coprimeBlockFirstMoment_eq_six]
    norm_num
  · exact coprimeBlockOrientationResidue_eq_zero

/--
Closed finite capstone: CRT fusion has zero primary mass in both orientations, opposite surviving
first moments, and a nonzero orientation charge.
-/
theorem coprimeBlockCarryTransgression_closed :
    coprimeBlockMass = 0 ∧
    reverseCoprimeBlockMass = 0 ∧
    coprimeBlockFirstMoment = 6 ∧
    reverseCoprimeBlockFirstMoment = -6 ∧
    coprimeBlockOrientationCharge = 12 ∧
    coprimeBlockOrientationCharge ≠ 0 ∧
    rotateCoprimeBlockFirstMoment ≠ coprimeBlockFirstMoment ∧
    coprimeBlockOrientationResidue = 0 := by
  exact ⟨coprimeBlockMass_eq_zero, reverseCoprimeBlockMass_eq_zero,
    coprimeBlockFirstMoment_eq_six, reverseCoprimeBlockFirstMoment_eq_neg_six,
    coprimeBlockOrientationCharge_eq_twelve,
    coprimeBlockOrientationCharge_eq_twelve ▸ by norm_num,
    coprimeBlockMomentOrientation_noGo.1, coprimeBlockMomentOrientation_noGo.2⟩

end RHTower
