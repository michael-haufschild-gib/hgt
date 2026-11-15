import GaloisForLFunctions.BiarithmeticGeometry.Affine.ParsellVinogradovSymmetricFrames
import GaloisForLFunctions.BiarithmeticGeometry.Affine.ParsellVinogradovDirectionalOverlap
import GaloisForLFunctions.BiarithmeticGeometry.Affine.FiniteCoordinateNorms

/-!
# Sharp overlap decay in the complete direction norm

The maximum-coordinate norm is attained by one horizontal coefficient.
Move that coefficient to the distinguished position by a permutation.
The induced permutation preserves moment-coordinate cubes and their overlap
volume, so the distinguished determinant bound gives the complete norm
bound with the same constant. The coordinate-axis slice proves optimality.
-/

open MeasureTheory
open scoped BigOperators
open GaloisForLFunctions.BiarithmeticGeometry.MixedCoordinateVolume
open GaloisForLFunctions.BiarithmeticGeometry.FiniteCoordinateNorms

namespace GaloisForLFunctions.BiarithmeticGeometry.ParsellVinogradov
noncomputable section

/-- A direction supported on the first coordinate is exactly the coordinate-axis affine frame. -/
theorem vectorAffineMatrix_cons_zero (r k : ℕ) (θ t : ℝ) :
    vectorAffineMatrix r k (Fin.cons θ (0 : Fin r → ℝ)) t = affineAxisMatrix r k θ t := by
  simpa only [vectorAffineMatrix, Fin.cons_zero, Fin.cons_succ, Pi.zero_apply, Pi.zero_def] using
    directionalAffine_zero_tail r k θ t

/-- The full direction norm has the sharp uniform weighted-volume bound. -/
theorem exists_regularized_vectorAffine_norm_upper (r k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (δ : Fin (r + 1) → ℝ) (t : ℝ) (a b : AffineAxisSpace r k),
      (1 + ‖δ‖) ^ axisExponent r k * (volume (vectorAffineOverlap r k δ t a b)).toReal ≤ C := by
  obtain ⟨C, hC, h⟩ := exists_regularized_directionalAffine_volume_upper r k
  refine ⟨C, hC, ?_⟩
  intro δ t a b
  obtain ⟨i, hi⟩ := exists_norm_eq_abs_coordinate δ
  let σ : Equiv.Perm (Fin (r + 1)) := Equiv.swap 0 i
  have hs : σ.symm 0 = i := by
    apply σ.injective
    rw [σ.apply_symm_apply]
    exact (Equiv.swap_apply_right 0 i).symm
  have hb := h (δ (σ.symm 0)) (fun j => δ (σ.symm j.succ)) t
    (coordinatePermutation (horizontalIndexPermutation r k σ) a)
    (coordinatePermutation (horizontalIndexPermutation r k σ) b)
  change (1 + |δ (σ.symm 0)|) ^ axisExponent r k *
    (volume (vectorAffineOverlap r k (fun j => δ (σ.symm j)) t
      (coordinatePermutation (horizontalIndexPermutation r k σ) a)
      (coordinatePermutation (horizontalIndexPermutation r k σ) b))).toReal ≤ C at hb
  rw [volume_vectorAffineOverlap_permutation, hs, ← hi] at hb
  exact hb

/-- The proposed binomial power controls the entire shear direction, uniformly in shift and centers. -/
theorem exists_uniform_vectorAffine_norm_overlap_decay (r k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (δ : Fin (r + 1) → ℝ) (t : ℝ) (a b : AffineAxisSpace r k),
      volume (vectorAffineOverlap r k δ t a b) ≤
        ENNReal.ofReal (C / (1 + ‖δ‖) ^ axisExponent r k) := by
  obtain ⟨C, hC, h⟩ := exists_regularized_vectorAffine_norm_upper r k
  refine ⟨C, hC, ?_⟩
  intro δ t a b
  have hf : volume (vectorAffineOverlap r k δ t a b) ≠ ⊤ :=
    ne_top_of_le_ne_top (by finiteness) (volume_matrixUnitOverlap_le (vectorAffineMatrix r k δ t) a b)
  rw [← ENNReal.ofReal_toReal hf]
  apply ENNReal.ofReal_le_ofReal
  apply (le_div_iff₀ (by positivity : 0 < (1 + ‖δ‖) ^ axisExponent r k)).mpr
  simpa only [mul_comm] using h δ t a b

theorem volume_cube_inter_vectorAffine_image (r k : ℕ) (δ : Fin (r + 1) → ℝ)
    (t : ℝ) (a b : AffineAxisSpace r k) :
    volume (centeredCube a 1 ∩ (Matrix.toLin' (vectorAffineMatrix r k δ t)) '' centeredCube b 1) =
      volume (vectorAffineOverlap r k δ t b a) := by
  simpa only [vectorAffineOverlap, det_vectorAffineMatrix, abs_one, ENNReal.ofReal_one, one_mul] using
    volume_cube_inter_matrix_image (vectorAffineMatrix r k δ t) a b

/-- Actual affine images of coordinate cubes satisfy the sharp complete-direction norm bound. -/
theorem exists_uniform_vectorAffine_norm_image_decay (r k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (δ : Fin (r + 1) → ℝ) (t : ℝ) (a b : AffineAxisSpace r k),
      volume (centeredCube a 1 ∩ (Matrix.toLin' (vectorAffineMatrix r k δ t)) '' centeredCube b 1) ≤
        ENNReal.ofReal (C / (1 + ‖δ‖) ^ axisExponent r k) := by
  obtain ⟨C, hC, h⟩ := exists_uniform_vectorAffine_norm_overlap_decay r k
  refine ⟨C, hC, fun δ t a b => ?_⟩
  rw [volume_cube_inter_vectorAffine_image]
  exact h δ t b a

/-- The proposed binomial sum is the exact uniform power threshold for the complete direction norm. -/
theorem bounded_vectorAffine_norm_overlap_iff (r k : ℕ) (p : ℝ) :
    (∃ C : ℝ, ∀ (δ : Fin (r + 1) → ℝ) (t : ℝ) (a b : AffineAxisSpace r k),
      (1 + ‖δ‖) ^ p * (volume (vectorAffineOverlap r k δ t a b)).toReal ≤ C) ↔
      p ≤ (∑ j ∈ Finset.range ((k + 1) / 2), (r + k + 1 - 2 * j).choose (r + 2) : ℕ) := by
  constructor
  · rintro ⟨C, h⟩
    apply (bounded_affineAxis_overlap_uniform_iff r k p).mp
    refine ⟨C, fun θ t a b => ?_⟩
    simpa only [norm_cons_zero, vectorAffineOverlap, vectorAffineMatrix_cons_zero, affineAxisOverlap] using
      h (Fin.cons θ (0 : Fin r → ℝ)) t a b
  · intro hp
    have hp' : p ≤ (axisExponent r k : ℝ) := by
      simpa only [axisExponent_eq_binomial_sum] using hp
    obtain ⟨C, _, h⟩ := exists_regularized_vectorAffine_norm_upper r k
    refine ⟨C, fun δ t a b => ?_⟩
    have hb : 1 ≤ 1 + ‖δ‖ := by linarith only [norm_nonneg δ]
    have hpow : (1 + ‖δ‖) ^ p ≤ (1 + ‖δ‖) ^ axisExponent r k := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le hb hp'
    exact (mul_le_mul_of_nonneg_right hpow ENNReal.toReal_nonneg).trans (h δ t a b)

/-- Actual affine cube intersections have exactly the same sharp full-direction threshold. -/
theorem bounded_vectorAffine_norm_image_iff (r k : ℕ) (p : ℝ) :
    (∃ C : ℝ, ∀ (δ : Fin (r + 1) → ℝ) (t : ℝ) (a b : AffineAxisSpace r k),
      (1 + ‖δ‖) ^ p * (volume (centeredCube a 1 ∩
        (Matrix.toLin' (vectorAffineMatrix r k δ t)) '' centeredCube b 1)).toReal ≤ C) ↔
      p ≤ (∑ j ∈ Finset.range ((k + 1) / 2), (r + k + 1 - 2 * j).choose (r + 2) : ℕ) := by
  rw [← bounded_vectorAffine_norm_overlap_iff]
  simp only [volume_cube_inter_vectorAffine_image]
  constructor
  · rintro ⟨C, h⟩
    exact ⟨C, fun δ t a b => h δ t b a⟩
  · rintro ⟨C, h⟩
    exact ⟨C, fun δ t a b => h δ t b a⟩

#print axioms vectorAffineMatrix_cons_zero
#print axioms exists_regularized_vectorAffine_norm_upper
#print axioms exists_uniform_vectorAffine_norm_overlap_decay
#print axioms volume_cube_inter_vectorAffine_image
#print axioms exists_uniform_vectorAffine_norm_image_decay
#print axioms bounded_vectorAffine_norm_overlap_iff
#print axioms bounded_vectorAffine_norm_image_iff

end
end GaloisForLFunctions.BiarithmeticGeometry.ParsellVinogradov
