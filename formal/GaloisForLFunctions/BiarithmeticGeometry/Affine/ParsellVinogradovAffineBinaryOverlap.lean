import GaloisForLFunctions.BiarithmeticGeometry.Affine.ParsellVinogradovAffineBinaryFrames
import GaloisForLFunctions.BiarithmeticGeometry.Affine.ParsellVinogradovShearOverlap
import GaloisForLFunctions.BiarithmeticGeometry.Affine.ParsellVinogradovBinaryExponent

/-!
# Binary moment overlap decay uniform in vertical translation

Balanced row selections give one sharp power of the shear parameter in
each homogeneous degree. Lower-degree translation terms do not change
their product determinant. Consequently the summed binary exponent holds
uniformly in vertical translation and in both coordinate-cube centers.
-/

open MeasureTheory
open scoped BigOperators ENNReal
open GaloisForLFunctions.BiarithmeticGeometry.MixedCoordinateVolume
open GaloisForLFunctions.BiarithmeticGeometry.SigmaBlockMatrix

namespace GaloisForLFunctions.BiarithmeticGeometry.ParsellVinogradov
noncomputable section

/-- A balanced row selection certifies the quarter-square power in every block size. -/
theorem exists_shear_determinant_certificate (m : ℕ) :
    ∃ s : Fin m → Fin m ⊕ Fin m, ∃ c : ℝ, c ≠ 0 ∧ ∀ θ : ℝ,
      (selectedMatrix (shearBlock m θ) s).det = c * θ ^ (m ^ 2 / 4) := by
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r : ℕ, r ≤ 1 ∧ m = 2 * q + r := by
    refine ⟨m / 2, m % 2, ?_, ?_⟩ <;> omega
  have he : (2 * q + r) ^ 2 / 4 = q * (q + r) := by
    have hr' : r = 0 ∨ r = 1 := by omega
    rcases hr' with rfl | rfl
    · have h : (2 * q + 0) ^ 2 = 4 * (q * (q + 0)) := by ring
      rw [h]; omega
    · have h : (2 * q + 1) ^ 2 = 4 * (q * (q + 1)) + 1 := by ring
      rw [h]; omega
  refine ⟨shearSelector q r, shearMinorConstant q r, shearMinorConstant_ne_zero q r, ?_⟩
  intro θ
  rw [he]
  exact det_shear_selectedMatrix q r θ

/-- One row selection certifies the full binary exponent for every vertical translation. -/
theorem exists_affineBinary_determinant_certificate (k : ℕ) :
    ∃ s : BinaryIndex k → BinaryIndex k ⊕ BinaryIndex k, ∃ c : ℝ, c ≠ 0 ∧
      ∀ θ t : ℝ, (selectedMatrix (affineBinaryMatrix k θ t) s).det =
        c * θ ^ binaryExponent k := by
  classical
  have hs (d : Fin k) := exists_shear_determinant_certificate (d.val + 2)
  choose s c hc hd using hs
  refine ⟨blockSelector s, ∏ d, c d, ?_, ?_⟩
  · exact Finset.prod_ne_zero_iff.mpr (fun d _ => hc d)
  · intro θ t
    rw [det_selectedMatrix_of_lower _ (affineBinaryMatrix_lower k θ t)]
    simp only [affineBinaryMatrix_diagonalBlock, hd]
    rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
    congr 2
    exact Fin.sum_univ_eq_sum_range (fun d : ℕ => (d + 2) ^ 2 / 4) k

/-- Coordinate-cube overlap for the genuine centered affine binary moment frame. -/
def affineBinaryOverlap (k : ℕ) (θ t : ℝ) (a b : FlatBinarySpace k) : Set (FlatBinarySpace k) :=
  centeredCube a 1 ∩ (Matrix.toLin' (affineBinaryMatrix k θ t)) ⁻¹' centeredCube b 1

theorem volume_affineBinaryOverlap_le (k : ℕ) (θ t : ℝ) (a b : FlatBinarySpace k) :
    volume (affineBinaryOverlap k θ t a b) ≤ (2 : ℝ≥0∞) ^ Fintype.card (BinaryIndex k) := by
  calc
    _ ≤ volume (centeredCube a 1) := measure_mono Set.inter_subset_left
    _ = _ := by rw [volume_centeredCube]; norm_num

private theorem regularize_power_bound (x c v : ℝ) (m d : ℕ)
    (hx : 0 ≤ x) (hv : 0 ≤ v) (h0 : v ≤ 2 ^ m) (h1 : c * x ^ d * v ≤ 2 ^ m) :
    min 1 c * (1 + x) ^ d * v ≤ 2 ^ (m + d) := by
  by_cases hc : c ≤ 0
  · have hn : min 1 c * (1 + x) ^ d * v ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg ((min_le_right 1 c).trans hc) (by positivity)) hv
    exact hn.trans (by positivity)
  have hcpos : 0 < c := lt_of_not_ge hc
  by_cases hsmall : x ≤ 1
  · have hp : (1 + x) ^ d ≤ (2 : ℝ) ^ d := by gcongr; linarith only [hsmall]
    calc
      _ ≤ 1 * (2 : ℝ) ^ d * v := by gcongr; exact min_le_left 1 c
      _ ≤ 2 ^ d * 2 ^ m := by simpa only [one_mul] using mul_le_mul_of_nonneg_left h0 (by positivity)
      _ = _ := by rw [pow_add]; ring
  · have hp : (1 + x) ^ d ≤ (2 * x) ^ d := by gcongr; linarith only [hsmall]
    calc
      _ ≤ c * (2 * x) ^ d * v := by gcongr; exact min_le_right 1 c
      _ = 2 ^ d * (c * x ^ d * v) := by rw [mul_pow]; ring
      _ ≤ 2 ^ d * 2 ^ m := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = _ := by rw [pow_add]; ring

/-- The sharp binary power stays bounded uniformly over both affine parameters and cube centers. -/
theorem exists_regularized_affineBinary_volume_upper (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (θ t : ℝ) (a b : FlatBinarySpace k),
      (1 + |θ|) ^ binaryExponent k * (volume (affineBinaryOverlap k θ t a b)).toReal ≤ C := by
  obtain ⟨s, c, hc, hd⟩ := exists_affineBinary_determinant_certificate k
  have hc' : 0 < min 1 |c| := lt_min (by norm_num) (abs_pos.mpr hc)
  refine ⟨2 ^ (Fintype.card (BinaryIndex k) + binaryExponent k) / min 1 |c|, by positivity, ?_⟩
  intro θ t a b
  have h0 : (volume (affineBinaryOverlap k θ t a b)).toReal ≤
      (2 : ℝ) ^ Fintype.card (BinaryIndex k) := by
    have h := ENNReal.toReal_mono (by finiteness) (volume_affineBinaryOverlap_le k θ t a b)
    simpa using h
  have hdet := selectedMatrix_det_mul_volume_overlap_le (affineBinaryMatrix k θ t) s a b 1
  rw [hd, abs_mul, abs_pow] at hdet
  have h1 : |c| * |θ| ^ binaryExponent k * (volume (affineBinaryOverlap k θ t a b)).toReal ≤
      (2 : ℝ) ^ Fintype.card (BinaryIndex k) := by
    have h := ENNReal.toReal_mono (by finiteness) hdet
    simpa only [affineBinaryOverlap, mul_one, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (mul_nonneg (abs_nonneg _) (pow_nonneg (abs_nonneg _) _)),
      ENNReal.toReal_pow, ENNReal.toReal_ofReal (show (0 : ℝ) ≤ 2 by norm_num)] using h
  apply (le_div_iff₀ hc').mpr
  simpa only [mul_assoc, mul_comm, mul_left_comm] using
    regularize_power_bound |θ| |c| _ _ _ (abs_nonneg θ) ENNReal.toReal_nonneg h0 h1

/-- Every binary affine moment frame has the proposed decay power, uniformly in vertical shift. -/
theorem exists_uniform_affineBinary_overlap_decay (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (θ t : ℝ) (a b : FlatBinarySpace k),
      volume (affineBinaryOverlap k θ t a b) ≤
        ENNReal.ofReal (C / (1 + |θ|) ^ binaryExponent k) := by
  obtain ⟨C, hC, h⟩ := exists_regularized_affineBinary_volume_upper k
  refine ⟨C, hC, ?_⟩
  intro θ t a b
  have hfinite : volume (affineBinaryOverlap k θ t a b) ≠ ⊤ :=
    ne_top_of_le_ne_top (by finiteness) (volume_affineBinaryOverlap_le k θ t a b)
  rw [← ENNReal.ofReal_toReal hfinite]
  apply ENNReal.ofReal_le_ofReal
  apply (le_div_iff₀ (by positivity : 0 < (1 + |θ|) ^ binaryExponent k)).mpr
  simpa only [mul_comm] using h θ t a b

/-- Determinant one converts actual image intersections into inverse-image overlaps. -/
theorem volume_cube_inter_affineBinary_image (k : ℕ) (θ t : ℝ) (a b : FlatBinarySpace k) :
    volume (centeredCube a 1 ∩ (Matrix.toLin' (affineBinaryMatrix k θ t)) '' centeredCube b 1) =
      volume (affineBinaryOverlap k θ t b a) := by
  have hset : (Matrix.toLin' (affineBinaryMatrix k θ t)) '' affineBinaryOverlap k θ t b a =
      centeredCube a 1 ∩ (Matrix.toLin' (affineBinaryMatrix k θ t)) '' centeredCube b 1 := by
    ext y
    constructor
    · rintro ⟨x, ⟨hx, hTx⟩, rfl⟩
      exact ⟨hTx, ⟨x, hx, rfl⟩⟩
    · rintro ⟨hy, ⟨x, hx, rfl⟩⟩
      exact ⟨x, ⟨hx, hy⟩, rfl⟩
  rw [← hset]
  simpa only [LinearMap.det_toLin', det_affineBinaryMatrix, abs_one,
    ENNReal.ofReal_one, one_mul] using
    Measure.addHaar_image_linearMap volume (Matrix.toLin' (affineBinaryMatrix k θ t))
      (affineBinaryOverlap k θ t b a)

/-- Actual affine cube intersections satisfy the binary decay bound uniformly in vertical shift. -/
theorem exists_uniform_affineBinary_image_overlap_decay (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (θ t : ℝ) (a b : FlatBinarySpace k),
      volume (centeredCube a 1 ∩ (Matrix.toLin' (affineBinaryMatrix k θ t)) '' centeredCube b 1) ≤
        ENNReal.ofReal (C / (1 + |θ|) ^ binaryExponent k) := by
  obtain ⟨C, hC, h⟩ := exists_uniform_affineBinary_overlap_decay k
  refine ⟨C, hC, fun θ t a b => ?_⟩
  rw [volume_cube_inter_affineBinary_image]
  exact h θ t b a

#print axioms exists_shear_determinant_certificate
#print axioms exists_affineBinary_determinant_certificate
#print axioms volume_affineBinaryOverlap_le
#print axioms exists_regularized_affineBinary_volume_upper
#print axioms exists_uniform_affineBinary_overlap_decay
#print axioms volume_cube_inter_affineBinary_image
#print axioms exists_uniform_affineBinary_image_overlap_decay

end
end GaloisForLFunctions.BiarithmeticGeometry.ParsellVinogradov
