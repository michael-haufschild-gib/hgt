import GaloisForLFunctions.BiarithmeticGeometry.Affine.MixedMatrixOverlap
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# Polynomial selected determinants give uniform overlap decay

A selected determinant `c θ^d`, with fixed nonzero `c`, gives power decay
uniformly over all additional parameters and cube centers. Combining its
determinant bound with the trivial cube-volume bound regularizes the weight
from `|θ|` to `1+|θ|` without any restriction near zero.
-/

open MeasureTheory
open scoped ENNReal

namespace GaloisForLFunctions.BiarithmeticGeometry.MixedCoordinateVolume
noncomputable section
variable {ι τ : Type*} [Fintype ι] [DecidableEq ι]

/-- Unit-radius coordinate-cube overlap under a matrix. -/
def matrixUnitOverlap (M : Matrix ι ι ℝ) (a b : ι → ℝ) : Set (ι → ℝ) :=
  centeredCube a 1 ∩ (Matrix.toLin' M) ⁻¹' centeredCube b 1

theorem volume_matrixUnitOverlap_le (M : Matrix ι ι ℝ) (a b : ι → ℝ) :
    volume (matrixUnitOverlap M a b) ≤ (2 : ℝ≥0∞) ^ Fintype.card ι := by
  calc
    _ ≤ volume (centeredCube a 1) := measure_mono Set.inter_subset_left
    _ = _ := by rw [volume_centeredCube]; norm_num

/-- Image intersections have the determinant-scaled inverse-image overlap volume. -/
theorem volume_cube_inter_matrix_image (M : Matrix ι ι ℝ) (a b : ι → ℝ) :
    volume (centeredCube a 1 ∩ (Matrix.toLin' M) '' centeredCube b 1) =
      ENNReal.ofReal |M.det| * volume (matrixUnitOverlap M b a) := by
  have hset : (Matrix.toLin' M) '' matrixUnitOverlap M b a =
      centeredCube a 1 ∩ (Matrix.toLin' M) '' centeredCube b 1 := by
    ext y
    constructor
    · rintro ⟨x, ⟨hx, hTx⟩, rfl⟩
      exact ⟨hTx, ⟨x, hx, rfl⟩⟩
    · rintro ⟨hy, ⟨x, hx, rfl⟩⟩
      exact ⟨x, ⟨hx, hy⟩, rfl⟩
  rw [← hset]
  simpa only [LinearMap.det_toLin'] using
    Measure.addHaar_image_linearMap volume (Matrix.toLin' M) (matrixUnitOverlap M b a)

private theorem regularize_positive_power_bound (x c v : ℝ) (m d : ℕ)
    (hx : 0 ≤ x) (hc : 0 < c) (hv : 0 ≤ v)
    (h0 : v ≤ 2 ^ m) (h1 : c * x ^ d * v ≤ 2 ^ m) :
    min 1 c * (1 + x) ^ d * v ≤ 2 ^ (m + d) := by
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

/-- A fixed polynomial determinant certificate bounds the regularized weighted real volume. -/
theorem exists_regularized_matrixUnitOverlap_bound
    (M : ℝ → τ → Matrix ι ι ℝ) (d : ℕ) (s : ι → ι ⊕ ι) (c : ℝ) (hc : c ≠ 0)
    (hdet : ∀ (θ : ℝ) (u : τ), (selectedMatrix (M θ u) s).det = c * θ ^ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (θ : ℝ) (u : τ) (a b : ι → ℝ),
      (1 + |θ|) ^ d * (volume (matrixUnitOverlap (M θ u) a b)).toReal ≤ C := by
  have hc' : 0 < min 1 |c| := lt_min (by norm_num) (abs_pos.mpr hc)
  refine ⟨2 ^ (Fintype.card ι + d) / min 1 |c|, by positivity, ?_⟩
  intro θ u a b
  have h0 : (volume (matrixUnitOverlap (M θ u) a b)).toReal ≤ (2 : ℝ) ^ Fintype.card ι := by
    have h := ENNReal.toReal_mono (by finiteness) (volume_matrixUnitOverlap_le (M θ u) a b)
    simpa using h
  have hdet' := selectedMatrix_det_mul_volume_overlap_le (M θ u) s a b 1
  rw [hdet, abs_mul, abs_pow] at hdet'
  have h1 : |c| * |θ| ^ d * (volume (matrixUnitOverlap (M θ u) a b)).toReal ≤
      (2 : ℝ) ^ Fintype.card ι := by
    have h := ENNReal.toReal_mono (by finiteness) hdet'
    simpa only [matrixUnitOverlap, mul_one, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (mul_nonneg (abs_nonneg _) (pow_nonneg (abs_nonneg _) _)),
      ENNReal.toReal_pow, ENNReal.toReal_ofReal (show (0 : ℝ) ≤ 2 by norm_num)] using h
  apply (le_div_iff₀ hc').mpr
  simpa only [mul_assoc, mul_comm, mul_left_comm] using
    regularize_positive_power_bound |θ| |c| _ _ _ (abs_nonneg θ) (abs_pos.mpr hc)
      ENNReal.toReal_nonneg h0 h1

/-- Polynomial selected determinants give uniform power decay of outer overlap volume. -/
theorem exists_matrixUnitOverlap_decay
    (M : ℝ → τ → Matrix ι ι ℝ) (d : ℕ) (s : ι → ι ⊕ ι) (c : ℝ) (hc : c ≠ 0)
    (hdet : ∀ (θ : ℝ) (u : τ), (selectedMatrix (M θ u) s).det = c * θ ^ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (θ : ℝ) (u : τ) (a b : ι → ℝ),
      volume (matrixUnitOverlap (M θ u) a b) ≤ ENNReal.ofReal (C / (1 + |θ|) ^ d) := by
  obtain ⟨C, hC, h⟩ := exists_regularized_matrixUnitOverlap_bound M d s c hc hdet
  refine ⟨C, hC, ?_⟩
  intro θ u a b
  have hfinite : volume (matrixUnitOverlap (M θ u) a b) ≠ ⊤ :=
    ne_top_of_le_ne_top (by finiteness) (volume_matrixUnitOverlap_le (M θ u) a b)
  rw [← ENNReal.ofReal_toReal hfinite]
  apply ENNReal.ofReal_le_ofReal
  apply (le_div_iff₀ (by positivity : 0 < (1 + |θ|) ^ d)).mpr
  simpa only [mul_comm] using h θ u a b

#print axioms volume_matrixUnitOverlap_le
#print axioms volume_cube_inter_matrix_image
#print axioms exists_regularized_matrixUnitOverlap_bound
#print axioms exists_matrixUnitOverlap_decay

end
end GaloisForLFunctions.BiarithmeticGeometry.MixedCoordinateVolume
