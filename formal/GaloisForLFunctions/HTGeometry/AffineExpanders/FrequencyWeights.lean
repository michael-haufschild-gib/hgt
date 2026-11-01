import GaloisForLFunctions.HTGeometry.AffineExpanders.AffineWalk
import GaloisForLFunctions.HTGeometry.AffineExpanders.ResidueBounds
import GaloisForLFunctions.HTGeometry.ReciprocalSchurTest

/-!
# The weighted dual-shear bound

Reciprocal edge weights give a uniform correlation bound away from zero frequency.
The arithmetic estimate uses natural representatives; the sums and shears live on
the residue torus itself.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace GaloisForLFunctions.HTGeometry
variable {n : ℕ} [NeZero n]

/-- Reciprocal shear weights compare the distances of both coordinates from zero. -/
def mggFrequencyWeight (a b : ZMod n × ZMod n) : ℝ :=
  MGGResidueBounds.psiWeight n a.1.val a.2.val b.1.val b.2.val

/-- The absolute half-angle phase factor of a cyclic frequency. -/
def mggCosineWeight (a : ZMod n) : ℝ := |Real.cos (Real.pi * a.val / n)|

omit [NeZero n] in
theorem mggFrequencyWeight_pos (a b : ZMod n × ZMod n) :
    0 < mggFrequencyWeight a b :=
  MGGResidueBounds.psiWeight_pos n a.1.val a.2.val b.1.val b.2.val

omit [NeZero n] in
theorem mggFrequencyWeight_reciprocal (a b : ZMod n × ZMod n) :
    mggFrequencyWeight a b * mggFrequencyWeight b a = 1 :=
  MGGResidueBounds.psiWeight_mul_comm n a.1.val a.2.val b.1.val b.2.val

private theorem val_sub_mod (a b : ZMod n) :
    (a - b).val = (a.val + n - b.val) % n := by
  rw [sub_eq_add_neg, ZMod.val_add, ZMod.neg_val', Nat.add_mod_mod,
    Nat.add_sub_assoc b.val_le]

private theorem val_two_mul (a : ZMod n) : (2 * a).val = (2 * a.val) % n := by
  rw [two_mul, ZMod.val_add, two_mul]

/-- The four dual shear weights satisfy the uniform MGG row bound off zero. -/
theorem mggFrequencyWeight_row (hn : 3 ≤ n) (a : ZMod n × ZMod n) (ha : a ≠ 0) :
    mggCosineWeight a.1 *
        (mggFrequencyWeight a (a.1, a.2 - 2 * a.1) +
         mggFrequencyWeight a (a.1, a.2 + 2 * a.1)) +
      mggCosineWeight a.2 *
        (mggFrequencyWeight a (a.1 - 2 * a.2, a.2) +
         mggFrequencyWeight a (a.1 + 2 * a.2, a.2)) ≤ 5 * Real.sqrt 2 / 2 := by
  have hne : ¬(a.1.val = 0 ∧ a.2.val = 0) := by
    rintro ⟨h₁, h₂⟩
    apply ha
    exact Prod.ext ((ZMod.val_eq_zero _).mp h₁) ((ZMod.val_eq_zero _).mp h₂)
  have h := MGGResidueBounds.pointwiseCondition_forall n a.1.val a.2.val hn
    a.1.val_lt a.2.val_lt hne
  simpa only [mggCosineWeight, mggFrequencyWeight, val_sub_mod, ZMod.val_add,
    val_two_mul, MGGResidueBounds.pointwiseCondition, MGGResidueBounds.shearS1,
    MGGResidueBounds.shearS2, MGGResidueBounds.shearS1Inv,
    MGGResidueBounds.shearS2Inv] using h

/-- The dual-shear correlation bound follows from the reciprocal row estimate.
Vanishing at the zero frequency is the only centering condition. -/
theorem mgg_frequency_correlation_le (hn : 3 ≤ n) (g : ZMod n × ZMod n → ℝ)
    (hg : g 0 = 0) :
    (∑ a, mggCosineWeight a.1 * g a * g (a.1, a.2 - 2 * a.1)) +
      (∑ a, mggCosineWeight a.2 * g a * g (a.1 - 2 * a.2, a.2)) ≤
        5 * Real.sqrt 2 / 4 * ∑ a, g a ^ 2 := by
  have hx := permutation_correlation_le_reciprocal_weights
    (mggShearY n 0).symm g (fun a => mggCosineWeight a.1) mggFrequencyWeight
    (fun a => abs_nonneg _) (fun a => rfl)
    mggFrequencyWeight_pos mggFrequencyWeight_reciprocal
  have hy := permutation_correlation_le_reciprocal_weights
    (mggShearX n 0).symm g (fun a => mggCosineWeight a.2) mggFrequencyWeight
    (fun a => abs_nonneg _) (fun a => rfl)
    mggFrequencyWeight_pos mggFrequencyWeight_reciprocal
  simp only [mggShearX, mggShearY, Equiv.symm,
    Equiv.coe_fn_mk, sub_zero, add_zero] at hx hy
  have hr : (∑ a, g a ^ 2 * mggCosineWeight a.1 *
      (mggFrequencyWeight a (a.1, a.2 - 2 * a.1) +
       mggFrequencyWeight a (a.1, a.2 + 2 * a.1))) +
      (∑ a, g a ^ 2 * mggCosineWeight a.2 *
      (mggFrequencyWeight a (a.1 - 2 * a.2, a.2) +
       mggFrequencyWeight a (a.1 + 2 * a.2, a.2))) ≤
      (5 * Real.sqrt 2 / 2) * ∑ a, g a ^ 2 := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro a _
    by_cases ha : a = 0
    · simp only [ha, hg, zero_pow (by decide : 2 ≠ 0), zero_mul, add_zero, mul_zero]
      exact le_rfl
    · have h := mul_le_mul_of_nonneg_left (mggFrequencyWeight_row hn a ha) (sq_nonneg (g a))
      convert h using 1 <;> ring
  linarith only [hx, hy, hr]

end GaloisForLFunctions.HTGeometry
