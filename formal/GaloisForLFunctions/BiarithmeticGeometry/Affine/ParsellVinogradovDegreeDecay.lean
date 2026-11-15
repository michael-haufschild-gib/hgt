import GaloisForLFunctions.BiarithmeticGeometry.Affine.ParsellVinogradovEuclideanOverlap

/-!
# The dimension-plus-one overlap bound in every degree at least two

The sharp chain exponent increases with the maximal polynomial degree.
At degree two it is exactly the physical dimension plus one. Thus the
Euclidean estimate implies the dimension-plus-one power in every higher
degree, uniformly over all real directions, shifts, and cube centers.
-/

open MeasureTheory
open scoped BigOperators
open GaloisForLFunctions.BiarithmeticGeometry.MixedCoordinateVolume
open GaloisForLFunctions.BiarithmeticGeometry.FiniteCoordinateNorms

namespace GaloisForLFunctions.BiarithmeticGeometry.ParsellVinogradov
noncomputable section

/-- Adding polynomial degrees can only increase the sharp chain exponent. -/
theorem axisExponent_monotone (r : ℕ) : Monotone (axisExponent r) := by
  intro a b hab
  exact Finset.sum_le_sum_of_subset (f := fun d => homogeneousAxisExponent r (d + 1))
    (Finset.range_mono hab)

/-- Quadratic moments attain exactly the physical dimension plus one. -/
theorem axisExponent_two (r : ℕ) : axisExponent r 2 = r + 3 := by
  calc
    axisExponent r 2 = (r + 3).choose (r + 2) := by
      simpa only [axisExponent_zero, Nat.add_zero, zero_add] using axisExponent_two_step r 0
    _ = r + 3 := by
      simpa only [Nat.add_assoc] using Nat.choose_succ_self_right (r + 2)

/-- Every degree at least two has the summable dimension-plus-one overlap exponent. -/
theorem dimension_add_one_le_axisExponent (r k : ℕ) : r + 3 ≤ axisExponent r (k + 2) := by
  simpa only [axisExponent_two] using axisExponent_monotone r (show 2 ≤ k + 2 by omega)

/-- The dimension-plus-one weighted overlap bound holds in every degree at least two. -/
theorem exists_regularized_vectorAffine_dimension_upper (r k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (δ : Fin (r + 1) → ℝ) (t : ℝ)
      (a b : AffineAxisSpace r (k + 2)),
      (1 + euclideanNorm δ) ^ (r + 3) *
        (volume (vectorAffineOverlap r (k + 2) δ t a b)).toReal ≤ C := by
  obtain ⟨C, hC, h⟩ := exists_regularized_vectorAffine_euclidean_upper r (k + 2)
  refine ⟨C, hC, fun δ t a b => ?_⟩
  have hp : ((r + 3 : ℕ) : ℝ) ≤ (axisExponent r (k + 2) : ℝ) := by
    exact_mod_cast dimension_add_one_le_axisExponent r k
  have hb : 1 ≤ 1 + euclideanNorm δ := by linarith only [euclideanNorm_nonneg δ]
  have hpow : (1 + euclideanNorm δ) ^ (r + 3) ≤
      (1 + euclideanNorm δ) ^ axisExponent r (k + 2) := by
    simpa only [Real.rpow_natCast] using Real.rpow_le_rpow_of_exponent_le hb hp
  exact (mul_le_mul_of_nonneg_right hpow ENNReal.toReal_nonneg).trans (h δ t a b)

/-- The dimension-plus-one decay power holds for every complete affine overlap. -/
theorem exists_uniform_vectorAffine_dimension_overlap_decay (r k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (δ : Fin (r + 1) → ℝ) (t : ℝ)
      (a b : AffineAxisSpace r (k + 2)),
      volume (vectorAffineOverlap r (k + 2) δ t a b) ≤
        ENNReal.ofReal (C / (1 + euclideanNorm δ) ^ (r + 3)) := by
  obtain ⟨C, hC, h⟩ := exists_regularized_vectorAffine_dimension_upper r k
  refine ⟨C, hC, ?_⟩
  intro δ t a b
  have hf : volume (vectorAffineOverlap r (k + 2) δ t a b) ≠ ⊤ :=
    ne_top_of_le_ne_top (by finiteness)
      (volume_matrixUnitOverlap_le (vectorAffineMatrix r (k + 2) δ t) a b)
  have he := euclideanNorm_nonneg δ
  rw [← ENNReal.ofReal_toReal hf]
  apply ENNReal.ofReal_le_ofReal
  apply (le_div_iff₀ (by positivity : 0 < (1 + euclideanNorm δ) ^ (r + 3))).mpr
  simpa only [mul_comm] using h δ t a b

/-- Affine cube images satisfy the Euclidean dimension-plus-one estimate of the covering argument. -/
theorem exists_uniform_vectorAffine_dimension_image_decay (r k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (δ : Fin (r + 1) → ℝ) (t : ℝ)
      (a b : AffineAxisSpace r (k + 2)),
      volume (centeredCube a 1 ∩
        (Matrix.toLin' (vectorAffineMatrix r (k + 2) δ t)) '' centeredCube b 1) ≤
          ENNReal.ofReal (C / (1 + euclideanNorm δ) ^ (r + 3)) := by
  obtain ⟨C, hC, h⟩ := exists_uniform_vectorAffine_dimension_overlap_decay r k
  refine ⟨C, hC, fun δ t a b => ?_⟩
  rw [volume_cube_inter_vectorAffine_image]
  exact h δ t b a

#print axioms axisExponent_monotone
#print axioms axisExponent_two
#print axioms dimension_add_one_le_axisExponent
#print axioms exists_regularized_vectorAffine_dimension_upper
#print axioms exists_uniform_vectorAffine_dimension_overlap_decay
#print axioms exists_uniform_vectorAffine_dimension_image_decay

end
end GaloisForLFunctions.BiarithmeticGeometry.ParsellVinogradov
