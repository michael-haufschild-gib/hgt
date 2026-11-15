import GaloisForLFunctions.BiScaleUncertainty.TropicalJensen
import GaloisForLFunctions.BiScaleUncertainty.ExponentialTentMoments
import GaloisForLFunctions.HTGeometry.CompactKernelRankOneDensity

/-!
# Tropical divisors of the existing tent sources

The causal exponential-source tent is a translated Jensen counting kernel.
The compact-kernel plateau cutoff is a difference of two such kernels.
These identities identify their root/pole locations and give exact
characteristics, rather than estimates by total variation.
-/

namespace GaloisForLFunctions.BiScaleUncertainty.TropicalJensen
noncomputable section

/-- The causal collar is a translated tropical counting kernel. -/
theorem causalTent_eq_tentCount (δ x : ℝ) :
    SignedPrimePolar.causalTent |δ| x = tentCount δ (x - |δ|) := by
  unfold SignedPrimePolar.causalTent tentCount
  congr 1
  by_cases h : x ≤ |δ|
  · rw [min_eq_left (by linarith only [h]), abs_of_nonpos (sub_nonpos.mpr h)]
    ring
  · rw [min_eq_right (by linarith only [h]),
      abs_of_nonneg (by linarith only [h] : 0 ≤ x - |δ|)]
    ring

/-- A unit-height plateau cutoff is the difference of its outer and inner counting kernels. -/
theorem tentReal_eq_count_difference (a x : ℝ) :
    HTGeometry.tentReal (|a| + 1) x = tentCount (|a| + 1) x - tentCount a x := by
  unfold HTGeometry.tentReal tentCount
  rw [abs_of_nonneg (by positivity : 0 ≤ |a| + 1)]
  simp only [min_def, max_def]
  split_ifs <;> linarith

/-- Boundary proximity plus the central counting term, including zero width. -/
theorem centeredTent_characteristic (a r : ℝ) :
    proximity r (fun x => tentCount a x) + |r| = max |a| |r| := by
  change (max 0 (max 0 (|a| - |r|)) + max 0 (max 0 (|a| - |-r|))) / 2 + |r| = _
  rw [abs_neg]
  rw [max_eq_right (le_max_left 0 (|a| - |r|))]
  by_cases h : |r| ≤ |a|
  · rw [max_eq_right (sub_nonneg.mpr h), max_eq_left h]
    ring
  · rw [max_eq_left (by linarith only [h]), max_eq_right (le_of_not_ge h)]
    ring

/-- At zero width the roots and central pole cancel, giving characteristic zero. -/
theorem centeredTent_characteristic_exact (a r : ℝ) :
    proximity r (fun x => tentCount a x) + (if a = 0 then 0 else |r|) =
      if a = 0 then 0 else max |a| |r| := by
  by_cases ha : a = 0
  · subst a
    have ht (x : ℝ) : tentCount 0 x = 0 := by
      rw [tentCount, abs_zero, zero_sub, max_eq_left (neg_nonpos.mpr (abs_nonneg x))]
    simp [ht, proximity]
  · simpa only [if_neg ha] using centeredTent_characteristic a r

/-- The existing compact-kernel cutoff has an explicit tropical characteristic. -/
theorem plateauTent_characteristic (a r : ℝ) :
    proximity r (HTGeometry.tentReal (|a| + 1)) + tentCount r a =
      max 1 (|r| - |a|) := by
  unfold proximity HTGeometry.tentReal tentCount
  rw [abs_neg]
  simp only [min_def, max_def]
  split_ifs <;> linarith

#print axioms causalTent_eq_tentCount
#print axioms tentReal_eq_count_difference
#print axioms centeredTent_characteristic
#print axioms centeredTent_characteristic_exact
#print axioms plateauTent_characteristic

end
end GaloisForLFunctions.BiScaleUncertainty.TropicalJensen
