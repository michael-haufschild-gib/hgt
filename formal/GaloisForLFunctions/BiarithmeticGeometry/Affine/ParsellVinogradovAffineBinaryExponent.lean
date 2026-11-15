import GaloisForLFunctions.BiarithmeticGeometry.Affine.ParsellVinogradovAffineBinaryOverlap
import GaloisForLFunctions.BiarithmeticGeometry.Affine.ParsellVinogradovBinaryFrames
import GaloisForLFunctions.BiarithmeticGeometry.Affine.SigmaProductVolume

/-!
# The sharp binary overlap exponent for arbitrary vertical shifts

Flattening the homogeneous blocks preserves Lebesgue volume. At zero
vertical shift, the affine overlap therefore has the already sharp pure
shear lower bound. Combined with the translation-uniform determinant upper
bound, this identifies the exact exponent for all affine binary frames.
-/

open MeasureTheory Matrix
open scoped BigOperators
open GaloisForLFunctions.BiarithmeticGeometry.MixedCoordinateVolume
open GaloisForLFunctions.BiarithmeticGeometry.SigmaBlockMatrix
open GaloisForLFunctions.BiarithmeticGeometry.SigmaProductVolume

namespace GaloisForLFunctions.BiarithmeticGeometry.ParsellVinogradov
noncomputable section

/-- Regard the homogeneous blocks as one scalar-coordinate vector. -/
def flattenBinary (k : ℕ) (x : BinaryMomentSpace k) : FlatBinarySpace k :=
  fun a => x a.1 a.2

private theorem flattenBinary_mem_cube (k : ℕ) (x a : BinaryMomentSpace k) :
    flattenBinary k x ∈ centeredCube (flattenBinary k a) 1 ↔
      x ∈ blockCube (fun d : Fin k => d.val + 2) a := by
  constructor
  · rintro ⟨hl, hu⟩ d _
    exact ⟨fun i => hl ⟨d, i⟩, fun i => hu ⟨d, i⟩⟩
  · intro h
    exact ⟨fun p => (h p.1 (Set.mem_univ _)).1 p.2,
      fun p => (h p.1 (Set.mem_univ _)).2 p.2⟩

/-- Flattening conjugates the pure block shear to the zero-shift affine matrix. -/
theorem affineBinaryMatrix_flatten (k : ℕ) (θ : ℝ) (x : BinaryMomentSpace k) :
    affineBinaryMatrix k θ 0 *ᵥ flattenBinary k x = flattenBinary k (binaryFrame k θ x) := by
  rw [affineBinaryMatrix_zero_translation]
  funext a
  rcases a with ⟨d, i⟩
  rw [blockDiagonal_mulVec]
  rfl

/-- At zero vertical shift the scalar-coordinate and homogeneous-block overlaps have equal volume. -/
theorem volume_affineBinaryOverlap_zero_translation (k : ℕ) (θ : ℝ) (a b : BinaryMomentSpace k) :
    volume (affineBinaryOverlap k θ 0 (flattenBinary k a) (flattenBinary k b)) =
      volume (binaryOverlap k θ a b) := by
  have hpre : (MeasurableEquiv.piCurry (fun (d : Fin k) (_ : Fin (d.val + 2)) => ℝ)).symm ⁻¹'
      affineBinaryOverlap k θ 0 (flattenBinary k a) (flattenBinary k b) =
        binaryOverlap k θ a b := by
    ext x
    change (flattenBinary k x ∈ centeredCube (flattenBinary k a) 1 ∧
      affineBinaryMatrix k θ 0 *ᵥ flattenBinary k x ∈ centeredCube (flattenBinary k b) 1) ↔ _
    rw [affineBinaryMatrix_flatten, flattenBinary_mem_cube, flattenBinary_mem_cube]
    rfl
  rw [← hpre]
  exact (volume_preimage_uncurry (fun (d : Fin k) (_ : Fin (d.val + 2)) => ℝ) _).symm

/-- The zero-shift slice retains matching lower and upper bounds with the binary exponent. -/
theorem exists_affineBinary_zero_shift_two_sided (k : ℕ) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ θ : ℝ,
      ENNReal.ofReal (c / (1 + |θ|) ^ binaryExponent k) ≤
        volume (affineBinaryOverlap k θ 0 0 0) ∧
      volume (affineBinaryOverlap k θ 0 0 0) ≤
        ENNReal.ofReal (C / (1 + |θ|) ^ binaryExponent k) := by
  obtain ⟨c, C, hc, hC, h⟩ := exists_binary_overlap_two_sided k
  refine ⟨c, C, hc, hC, ?_⟩
  intro θ
  have hv := volume_affineBinaryOverlap_zero_translation k θ 0 0
  change volume (affineBinaryOverlap k θ 0 0 0) = _ at hv
  rw [hv]
  exact h θ

/-- The proposed binomial sum is the exact uniform exponent, including every vertical shift. -/
theorem bounded_affineBinary_overlap_uniform_iff (k : ℕ) (p : ℝ) :
    (∃ C : ℝ, ∀ (θ t : ℝ) (a b : FlatBinarySpace k),
      (1 + |θ|) ^ p * (volume (affineBinaryOverlap k θ t a b)).toReal ≤ C) ↔
        p ≤ (∑ j ∈ Finset.range ((k + 1) / 2), (k + 1 - 2 * j).choose 2 : ℕ) := by
  constructor
  · rintro ⟨C, hC⟩
    apply (bounded_binary_overlap_uniform_centers_iff k p).mp
    refine ⟨C, fun θ a b => ?_⟩
    rw [← volume_affineBinaryOverlap_zero_translation]
    exact hC θ 0 (flattenBinary k a) (flattenBinary k b)
  · intro hp
    have hp' : p ≤ (binaryExponent k : ℝ) := by
      simpa only [binaryExponent_eq_binomial_sum] using hp
    obtain ⟨C, _, hC⟩ := exists_regularized_affineBinary_volume_upper k
    refine ⟨C, fun θ t a b => ?_⟩
    have hb : 1 ≤ 1 + |θ| := by linarith only [abs_nonneg θ]
    have hpow : (1 + |θ|) ^ p ≤ (1 + |θ|) ^ binaryExponent k := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le hb hp'
    exact (mul_le_mul_of_nonneg_right hpow ENNReal.toReal_nonneg).trans (hC θ t a b)

/-- The same exact threshold governs intersections with actual affine images of coordinate cubes. -/
theorem bounded_affineBinary_image_overlap_uniform_iff (k : ℕ) (p : ℝ) :
    (∃ C : ℝ, ∀ (θ t : ℝ) (a b : FlatBinarySpace k),
      (1 + |θ|) ^ p * (volume (centeredCube a 1 ∩
        (Matrix.toLin' (affineBinaryMatrix k θ t)) '' centeredCube b 1)).toReal ≤ C) ↔
      p ≤ (∑ j ∈ Finset.range ((k + 1) / 2), (k + 1 - 2 * j).choose 2 : ℕ) := by
  rw [← bounded_affineBinary_overlap_uniform_iff]
  simp only [volume_cube_inter_affineBinary_image]
  constructor
  · rintro ⟨C, hC⟩
    exact ⟨C, fun θ t a b => hC θ t b a⟩
  · rintro ⟨C, hC⟩
    exact ⟨C, fun θ t a b => hC θ t b a⟩

#print axioms affineBinaryMatrix_flatten
#print axioms volume_affineBinaryOverlap_zero_translation
#print axioms exists_affineBinary_zero_shift_two_sided
#print axioms bounded_affineBinary_overlap_uniform_iff
#print axioms bounded_affineBinary_image_overlap_uniform_iff

end
end GaloisForLFunctions.BiarithmeticGeometry.ParsellVinogradov
