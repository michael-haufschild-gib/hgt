import GaloisForLFunctions.BiarithmeticGeometry.Affine.ParsellVinogradovAffineAxisOverlap
import GaloisForLFunctions.BiarithmeticGeometry.Affine.ParsellVinogradovAxisFrames
import GaloisForLFunctions.BiarithmeticGeometry.Affine.SigmaBlockVolume

/-!
# Sharp affine coordinate-direction exponents in every dimension

At zero vertical shift, regrouping the scalar coordinates factors overlap
volume into the binary chain volumes. Their matching lower bound proves
that the translation-uniform upper exponent cannot be improved. The exact
threshold is the proposed binomial sum in every dimension and degree.
-/

open MeasureTheory
open scoped BigOperators
open GaloisForLFunctions.BiarithmeticGeometry.MixedCoordinateVolume
open GaloisForLFunctions.BiarithmeticGeometry.SigmaBlockMatrix

namespace GaloisForLFunctions.BiarithmeticGeometry.ParsellVinogradov
noncomputable section

/-- Flatten the binary-chain grouping into scalar coordinates ordered by total degree. -/
def flattenAxis (r k : ℕ) (x : AxisMomentSpace r k) : AffineAxisSpace r k :=
  fun a => x ⟨a.1, a.2.1⟩ a.2.2

theorem flattenAxis_moment (r k : ℕ) (y : Fin r → ℝ) (x z : ℝ) :
    flattenAxis r k (axisMoment r k y x z) = affineAxisMoment r k y x z := rfl

/-- At zero shift, the affine overlap is exactly the product-chain overlap in volume. -/
theorem volume_affineAxisOverlap_zero_translation (r k : ℕ) (θ : ℝ) (a b : AxisMomentSpace r k) :
    volume (affineAxisOverlap r k θ 0 (flattenAxis r k a) (flattenAxis r k b)) =
      volume (axisOverlap r k θ a b) := by
  unfold affineAxisOverlap matrixUnitOverlap
  rw [affineAxisMatrix_zero_translation, volume_blockDiagonal_overlap]
  simp only [homogeneousAxisShearMatrix, volume_blockDiagonal_overlap]
  change _ = volume (blockOverlap (axisChainSize r k) θ a b)
  rw [volume_blockOverlap, Fintype.prod_sigma]
  rfl

/-- Zero vertical shift and zero centers attain the complete proposed power in every dimension. -/
theorem exists_affineAxis_zero_shift_two_sided (r k : ℕ) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ θ : ℝ,
      ENNReal.ofReal (c / (1 + |θ|) ^ axisExponent r k) ≤
        volume (affineAxisOverlap r k θ 0 0 0) ∧
      volume (affineAxisOverlap r k θ 0 0 0) ≤
        ENNReal.ofReal (C / (1 + |θ|) ^ axisExponent r k) := by
  obtain ⟨c, C, hc, hC, h⟩ := exists_axis_overlap_two_sided r k
  refine ⟨c, C, hc, hC, ?_⟩
  intro θ
  have hv := volume_affineAxisOverlap_zero_translation r k θ 0 0
  change volume (affineAxisOverlap r k θ 0 0 0) = _ at hv
  rw [hv]
  exact h θ

/-- The binomial sum is the exact uniform affine exponent for coordinate-direction shears. -/
theorem bounded_affineAxis_overlap_uniform_iff (r k : ℕ) (p : ℝ) :
    (∃ C : ℝ, ∀ (θ t : ℝ) (a b : AffineAxisSpace r k),
      (1 + |θ|) ^ p * (volume (affineAxisOverlap r k θ t a b)).toReal ≤ C) ↔
      p ≤ (∑ j ∈ Finset.range ((k + 1) / 2), (r + k + 1 - 2 * j).choose (r + 2) : ℕ) := by
  constructor
  · rintro ⟨C, hC⟩
    apply (bounded_axis_overlap_uniform_centers_iff r k p).mp
    refine ⟨C, fun θ a b => ?_⟩
    rw [← volume_affineAxisOverlap_zero_translation]
    exact hC θ 0 (flattenAxis r k a) (flattenAxis r k b)
  · intro hp
    have hp' : p ≤ (axisExponent r k : ℝ) := by
      simpa only [axisExponent_eq_binomial_sum] using hp
    obtain ⟨C, _, hC⟩ := exists_regularized_affineAxis_volume_upper r k
    refine ⟨C, fun θ t a b => ?_⟩
    have hb : 1 ≤ 1 + |θ| := by linarith only [abs_nonneg θ]
    have hpow : (1 + |θ|) ^ p ≤ (1 + |θ|) ^ axisExponent r k := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le hb hp'
    exact (mul_le_mul_of_nonneg_right hpow ENNReal.toReal_nonneg).trans (hC θ t a b)

/-- Actual image intersections have the same sharp dimension-degree threshold. -/
theorem bounded_affineAxis_image_overlap_uniform_iff (r k : ℕ) (p : ℝ) :
    (∃ C : ℝ, ∀ (θ t : ℝ) (a b : AffineAxisSpace r k),
      (1 + |θ|) ^ p * (volume (centeredCube a 1 ∩
        (Matrix.toLin' (affineAxisMatrix r k θ t)) '' centeredCube b 1)).toReal ≤ C) ↔
      p ≤ (∑ j ∈ Finset.range ((k + 1) / 2), (r + k + 1 - 2 * j).choose (r + 2) : ℕ) := by
  rw [← bounded_affineAxis_overlap_uniform_iff]
  simp only [volume_cube_inter_affineAxis_image]
  constructor
  · rintro ⟨C, hC⟩
    exact ⟨C, fun θ t a b => hC θ t b a⟩
  · rintro ⟨C, hC⟩
    exact ⟨C, fun θ t a b => hC θ t b a⟩

#print axioms flattenAxis_moment
#print axioms volume_affineAxisOverlap_zero_translation
#print axioms exists_affineAxis_zero_shift_two_sided
#print axioms bounded_affineAxis_overlap_uniform_iff
#print axioms bounded_affineAxis_image_overlap_uniform_iff

end
end GaloisForLFunctions.BiarithmeticGeometry.ParsellVinogradov
