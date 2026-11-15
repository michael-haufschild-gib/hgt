import GaloisForLFunctions.BiarithmeticGeometry.Affine.ParsellVinogradovNormOverlap

/-!
# Sharp affine moment overlap in the Euclidean direction norm

The maximum-norm overlap estimate transfers to the Euclidean norm with an
explicit dimension factor in its constant. On coordinate-axis directions
both norms agree exactly, so the full binomial decay exponent remains
optimal for the Euclidean norm as well.
-/

open MeasureTheory
open scoped BigOperators
open GaloisForLFunctions.BiarithmeticGeometry.MixedCoordinateVolume
open GaloisForLFunctions.BiarithmeticGeometry.FiniteCoordinateNorms

namespace GaloisForLFunctions.BiarithmeticGeometry.ParsellVinogradov
noncomputable section

/-- The exact chain exponent bounds Euclidean-weighted overlap volume uniformly in every affine parameter. -/
theorem exists_regularized_vectorAffine_euclidean_upper (r k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (δ : Fin (r + 1) → ℝ) (t : ℝ) (a b : AffineAxisSpace r k),
      (1 + euclideanNorm δ) ^ axisExponent r k *
        (volume (vectorAffineOverlap r k δ t a b)).toReal ≤ C := by
  obtain ⟨C, hC, h⟩ := exists_regularized_vectorAffine_norm_upper r k
  refine ⟨((r + 1 : ℕ) : ℝ) ^ axisExponent r k * C, by positivity, ?_⟩
  intro δ t a b
  have hd : (1 : ℝ) ≤ ((r + 1 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ r + 1 by omega)
  have hb : 1 + euclideanNorm δ ≤ ((r + 1 : ℕ) : ℝ) * (1 + ‖δ‖) := by
    calc
      _ ≤ ((r + 1 : ℕ) : ℝ) + ((r + 1 : ℕ) : ℝ) * ‖δ‖ :=
        add_le_add hd (euclideanNorm_le_card_mul_norm r δ)
      _ = _ := by ring
  have hp := pow_le_pow_left₀ (add_nonneg zero_le_one (euclideanNorm_nonneg δ)) hb (axisExponent r k)
  calc
    _ ≤ (((r + 1 : ℕ) : ℝ) * (1 + ‖δ‖)) ^ axisExponent r k *
        (volume (vectorAffineOverlap r k δ t a b)).toReal :=
      mul_le_mul_of_nonneg_right hp ENNReal.toReal_nonneg
    _ = ((r + 1 : ℕ) : ℝ) ^ axisExponent r k *
        ((1 + ‖δ‖) ^ axisExponent r k * (volume (vectorAffineOverlap r k δ t a b)).toReal) := by
      rw [mul_pow, mul_assoc]
    _ ≤ _ := mul_le_mul_of_nonneg_left (h δ t a b) (pow_nonneg (Nat.cast_nonneg (r + 1)) _)

/-- Euclidean direction decay has the complete proposed binomial power, uniformly over shifts and centers. -/
theorem exists_uniform_vectorAffine_euclidean_overlap_decay (r k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (δ : Fin (r + 1) → ℝ) (t : ℝ) (a b : AffineAxisSpace r k),
      volume (vectorAffineOverlap r k δ t a b) ≤
        ENNReal.ofReal (C / (1 + euclideanNorm δ) ^ axisExponent r k) := by
  obtain ⟨C, hC, h⟩ := exists_regularized_vectorAffine_euclidean_upper r k
  refine ⟨C, hC, ?_⟩
  intro δ t a b
  have hf : volume (vectorAffineOverlap r k δ t a b) ≠ ⊤ :=
    ne_top_of_le_ne_top (by finiteness) (volume_matrixUnitOverlap_le (vectorAffineMatrix r k δ t) a b)
  have he := euclideanNorm_nonneg δ
  rw [← ENNReal.ofReal_toReal hf]
  apply ENNReal.ofReal_le_ofReal
  apply (le_div_iff₀ (by positivity : 0 < (1 + euclideanNorm δ) ^ axisExponent r k)).mpr
  simpa only [mul_comm] using h δ t a b

/-- Actual affine cube images satisfy the full sharp Euclidean-direction estimate. -/
theorem exists_uniform_vectorAffine_euclidean_image_decay (r k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (δ : Fin (r + 1) → ℝ) (t : ℝ) (a b : AffineAxisSpace r k),
      volume (centeredCube a 1 ∩ (Matrix.toLin' (vectorAffineMatrix r k δ t)) '' centeredCube b 1) ≤
        ENNReal.ofReal (C / (1 + euclideanNorm δ) ^ axisExponent r k) := by
  obtain ⟨C, hC, h⟩ := exists_uniform_vectorAffine_euclidean_overlap_decay r k
  refine ⟨C, hC, fun δ t a b => ?_⟩
  rw [volume_cube_inter_vectorAffine_image]
  exact h δ t b a

/-- The proposed binomial sum is exactly the admissible Euclidean power range. -/
theorem bounded_vectorAffine_euclidean_overlap_iff (r k : ℕ) (p : ℝ) :
    (∃ C : ℝ, ∀ (δ : Fin (r + 1) → ℝ) (t : ℝ) (a b : AffineAxisSpace r k),
      (1 + euclideanNorm δ) ^ p * (volume (vectorAffineOverlap r k δ t a b)).toReal ≤ C) ↔
      p ≤ (∑ j ∈ Finset.range ((k + 1) / 2), (r + k + 1 - 2 * j).choose (r + 2) : ℕ) := by
  constructor
  · rintro ⟨C, h⟩
    apply (bounded_affineAxis_overlap_uniform_iff r k p).mp
    refine ⟨C, fun θ t a b => ?_⟩
    simpa only [euclideanNorm_cons_zero, vectorAffineOverlap,
      vectorAffineMatrix_cons_zero, affineAxisOverlap] using
      h (Fin.cons θ (0 : Fin r → ℝ)) t a b
  · intro hp
    have hp' : p ≤ (axisExponent r k : ℝ) := by
      simpa only [axisExponent_eq_binomial_sum] using hp
    obtain ⟨C, _, h⟩ := exists_regularized_vectorAffine_euclidean_upper r k
    refine ⟨C, fun δ t a b => ?_⟩
    have hb : 1 ≤ 1 + euclideanNorm δ := by linarith only [euclideanNorm_nonneg δ]
    have hpow : (1 + euclideanNorm δ) ^ p ≤ (1 + euclideanNorm δ) ^ axisExponent r k := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le hb hp'
    exact (mul_le_mul_of_nonneg_right hpow ENNReal.toReal_nonneg).trans (h δ t a b)

/-- Actual image intersections have the same exact sharp exponent in the Euclidean norm. -/
theorem bounded_vectorAffine_euclidean_image_iff (r k : ℕ) (p : ℝ) :
    (∃ C : ℝ, ∀ (δ : Fin (r + 1) → ℝ) (t : ℝ) (a b : AffineAxisSpace r k),
      (1 + euclideanNorm δ) ^ p * (volume (centeredCube a 1 ∩
        (Matrix.toLin' (vectorAffineMatrix r k δ t)) '' centeredCube b 1)).toReal ≤ C) ↔
      p ≤ (∑ j ∈ Finset.range ((k + 1) / 2), (r + k + 1 - 2 * j).choose (r + 2) : ℕ) := by
  rw [← bounded_vectorAffine_euclidean_overlap_iff]
  simp only [volume_cube_inter_vectorAffine_image]
  constructor
  · rintro ⟨C, h⟩
    exact ⟨C, fun δ t a b => h δ t b a⟩
  · rintro ⟨C, h⟩
    exact ⟨C, fun δ t a b => h δ t b a⟩

#print axioms exists_regularized_vectorAffine_euclidean_upper
#print axioms exists_uniform_vectorAffine_euclidean_overlap_decay
#print axioms exists_uniform_vectorAffine_euclidean_image_decay
#print axioms bounded_vectorAffine_euclidean_overlap_iff
#print axioms bounded_vectorAffine_euclidean_image_iff

end
end GaloisForLFunctions.BiarithmeticGeometry.ParsellVinogradov
