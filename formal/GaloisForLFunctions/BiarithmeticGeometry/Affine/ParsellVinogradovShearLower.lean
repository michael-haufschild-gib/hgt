import GaloisForLFunctions.BiarithmeticGeometry.Affine.ParsellVinogradovBalancedInverse

/-!
# Matching lower overlap bounds for balanced homogeneous shears

At small shear a fixed cube remains in the overlap. At large shear the
uniformly bounded selected-coordinate inverse places a fixed cube in the
selected image. The determinant of that image contributes precisely the
power `q(q+r)` for `r ≤ 1`.
-/

open MeasureTheory Matrix
open scoped ENNReal
open GaloisForLFunctions.BiarithmeticGeometry
open MixedCoordinateVolume MatrixCubeBounds

namespace GaloisForLFunctions.BiarithmeticGeometry.ParsellVinogradov
noncomputable section

private theorem centeredCube_zero {ι : Type*} (ρ : ℝ) :
    centeredCube (0 : ι → ℝ) ρ = cube ι ρ := by
  simp only [centeredCube, cube, Pi.zero_apply, zero_sub, zero_add]

/-- A fixed radius for the original-coordinate cube at small shear. -/
def shearSmallRadius (q r : ℕ) : ℝ := safeRadius 0 (shearBlock (2 * q + r) 1)

/-- A fixed radius for the selected-coordinate cube at large shear. -/
def shearLargeRadius (q r : ℕ) : ℝ :=
  safeRadius (shearSelected q r 1)⁻¹
    (shearBlock (2 * q + r) 1 * (shearSelected q r 1)⁻¹)

private theorem small_shear_entryMass_le (m : ℕ) (θ : ℝ) (hθ : |θ| ≤ 1) :
    entryMass (shearBlock m θ) ≤ entryMass (shearBlock m 1) := by
  apply entryMass_le
  intro i j
  simp only [shearBlock, abs_mul, abs_pow, one_pow, mul_one]
  have hp : |θ| ^ (i.val - j.val) ≤ (1 : ℝ) ^ (i.val - j.val) := by gcongr
  simpa only [one_pow, mul_one] using
    mul_le_mul_of_nonneg_left hp (abs_nonneg (Nat.choose i.val j.val : ℝ))

/-- A fixed positive cube remains inside the overlap for absolute shear at most one. -/
theorem small_cube_subset_shearOverlap (q r : ℕ) (θ : ℝ) (hθ : |θ| ≤ 1) :
    cube (Fin (2 * q + r)) (shearSmallRadius q r) ⊆ shearCubeOverlap q r θ 0 0 := by
  intro x hx
  have hrad : 0 ≤ shearSmallRadius q r := (safeRadius_pos _ _).le
  have hx' := (mem_cube_iff x (shearSmallRadius q r)).mp hx
  rw [shearCubeOverlap, centeredCube_zero]
  constructor
  · rw [mem_cube_iff]
    intro i
    exact (hx' i).trans (safeRadius_le_one _ _)
  · change Matrix.toLin' (shearBlock (2 * q + r) θ) x ∈ cube _ 1
    rw [Matrix.toLin'_apply, mem_cube_iff]
    intro i
    calc
      _ ≤ entryMass (shearBlock (2 * q + r) θ) * shearSmallRadius q r :=
        abs_mulVec_le _ x _ hrad hx' i
      _ ≤ entryMass (shearBlock (2 * q + r) 1) * shearSmallRadius q r :=
        mul_le_mul_of_nonneg_right (small_shear_entryMass_le _ θ hθ) hrad
      _ ≤ 1 := entryMass_mul_safeRadius_right _ _

/-- At large shear, a fixed cube lies in the image of the overlap under selected coordinates. -/
theorem large_cube_subset_selected_overlap (q r : ℕ) (hr : r ≤ 1)
    (θ : ℝ) (hθ : 1 ≤ |θ|) :
    cube (Fin (2 * q + r)) (shearLargeRadius q r) ⊆
      (Matrix.toLin' (shearSelected q r θ)) '' shearCubeOverlap q r θ 0 0 := by
  have hn : θ ≠ 0 := by intro hz; rw [hz, abs_zero] at hθ; norm_num at hθ
  have hrad : 0 ≤ shearLargeRadius q r := (safeRadius_pos _ _).le
  rw [shearCubeOverlap, centeredCube_zero]
  apply cube_subset_image_overlap _ _ (shearSelectedInverse q r θ)
    (shearSelected_mul_inverse q r θ hn) _ hrad
  · calc
      _ ≤ entryMass (shearSelected q r 1)⁻¹ * shearLargeRadius q r :=
        mul_le_mul_of_nonneg_right
          (entryMass_le _ _ (abs_shearSelectedInverse_le q r θ hθ)) hrad
      _ ≤ 1 := entryMass_mul_safeRadius_left _ _
  · calc
      _ ≤ entryMass (shearBlock (2 * q + r) 1 * (shearSelected q r 1)⁻¹) *
          shearLargeRadius q r :=
        mul_le_mul_of_nonneg_right
          (entryMass_le _ _ (abs_shearBlock_mul_selectedInverse_le q r hr θ hθ)) hrad
      _ ≤ 1 := entryMass_mul_safeRadius_right _ _

private theorem volume_shearOverlap_ne_top (q r : ℕ) (θ : ℝ) :
    volume (shearCubeOverlap q r θ 0 0) ≠ ⊤ :=
  ne_top_of_le_ne_top (by finiteness) (volume_shearCubeOverlap_le q r θ 0 0)

/-- Small shear gives a positive lower bound independent of the parameter. -/
theorem small_shear_real_volume_ge (q r : ℕ) (θ : ℝ) (hθ : |θ| ≤ 1) :
    (2 * shearSmallRadius q r) ^ (2 * q + r) ≤
      (volume (shearCubeOverlap q r θ 0 0)).toReal := by
  have h : volume (cube (Fin (2 * q + r)) (shearSmallRadius q r)) ≤
      volume (shearCubeOverlap q r θ 0 0) :=
    measure_mono (small_cube_subset_shearOverlap q r θ hθ)
  rw [volume_cube] at h
  have ht := ENNReal.toReal_mono (volume_shearOverlap_ne_top q r θ) h
  have hrad : 0 ≤ 2 * shearSmallRadius q r :=
    mul_nonneg (by norm_num) (safeRadius_pos _ _).le
  simpa only [ENNReal.toReal_pow, Fintype.card_fin,
    ENNReal.toReal_ofReal hrad] using ht

/-- Large shear gives a positive lower bound after multiplication by the exact determinant power. -/
theorem large_shear_real_volume_ge (q r : ℕ) (hr : r ≤ 1) (θ : ℝ) (hθ : 1 ≤ |θ|) :
    (2 * shearLargeRadius q r) ^ (2 * q + r) ≤
      |shearMinorConstant q r| * |θ| ^ (q * (q + r)) *
        (volume (shearCubeOverlap q r θ 0 0)).toReal := by
  have h : volume (cube (Fin (2 * q + r)) (shearLargeRadius q r)) ≤
      volume ((Matrix.toLin' (shearSelected q r θ)) '' shearCubeOverlap q r θ 0 0) :=
    measure_mono (large_cube_subset_selected_overlap q r hr θ hθ)
  rw [volume_cube, Measure.addHaar_image_linearMap, LinearMap.det_toLin',
    shearSelected, det_shear_selectedMatrix, abs_mul, abs_pow] at h
  have hfinite : ENNReal.ofReal (|shearMinorConstant q r| * |θ| ^ (q * (q + r))) *
      volume (shearCubeOverlap q r θ 0 0) ≠ ⊤ := by
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (volume_shearOverlap_ne_top q r θ)
  have ht := ENNReal.toReal_mono hfinite h
  have hrad : 0 ≤ 2 * shearLargeRadius q r :=
    mul_nonneg (by norm_num) (safeRadius_pos _ _).le
  have hcoeff : 0 ≤ |shearMinorConstant q r| * |θ| ^ (q * (q + r)) := by positivity
  simpa only [ENNReal.toReal_pow, ENNReal.toReal_mul, Fintype.card_fin,
    ENNReal.toReal_ofReal hrad, ENNReal.toReal_ofReal hcoeff] using ht

/-- Balanced blocks have a positive regularized lower bound with the same exponent as the upper bound. -/
theorem exists_regularized_shear_volume_lower (q r : ℕ) (hr : r ≤ 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ θ : ℝ,
      c ≤ (1 + |θ|) ^ (q * (q + r)) * (volume (shearCubeOverlap q r θ 0 0)).toReal := by
  let a := (2 * shearSmallRadius q r) ^ (2 * q + r)
  let b := (2 * shearLargeRadius q r) ^ (2 * q + r) / |shearMinorConstant q r|
  have hc : 0 < |shearMinorConstant q r| := abs_pos.mpr (shearMinorConstant_ne_zero q r)
  have ha : 0 < a := by
    have hradius : 0 < shearSmallRadius q r := safeRadius_pos _ _
    dsimp [a]; positivity
  have hb : 0 < b := by
    have hradius : 0 < shearLargeRadius q r := safeRadius_pos _ _
    dsimp [b]; positivity
  refine ⟨min a b, lt_min ha hb, ?_⟩
  intro θ
  have hv : 0 ≤ (volume (shearCubeOverlap q r θ 0 0)).toReal := ENNReal.toReal_nonneg
  by_cases hθ : |θ| ≤ 1
  · have hp : (1 : ℝ) ^ (q * (q + r)) ≤ (1 + |θ|) ^ (q * (q + r)) := by
      gcongr; exact le_add_of_nonneg_right (abs_nonneg θ)
    calc
      _ ≤ a := min_le_left _ _
      _ ≤ (volume (shearCubeOverlap q r θ 0 0)).toReal := small_shear_real_volume_ge q r θ hθ
      _ ≤ _ := by simpa only [one_pow, one_mul] using mul_le_mul_of_nonneg_right hp hv
  · have hlarge := large_shear_real_volume_ge q r hr θ (le_of_not_ge hθ)
    have hb' : b ≤ |θ| ^ (q * (q + r)) * (volume (shearCubeOverlap q r θ 0 0)).toReal := by
      apply (div_le_iff₀ hc).mpr
      simpa only [mul_assoc, mul_comm, mul_left_comm] using hlarge
    have hp : |θ| ^ (q * (q + r)) ≤ (1 + |θ|) ^ (q * (q + r)) := by gcongr; linarith
    exact (min_le_right a b).trans (hb'.trans (mul_le_mul_of_nonneg_right hp hv))

#print axioms small_cube_subset_shearOverlap
#print axioms large_cube_subset_selected_overlap
#print axioms small_shear_real_volume_ge
#print axioms large_shear_real_volume_ge
#print axioms exists_regularized_shear_volume_lower

end
end GaloisForLFunctions.BiarithmeticGeometry.ParsellVinogradov
