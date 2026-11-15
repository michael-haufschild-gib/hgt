import GaloisForLFunctions.BiarithmeticGeometry.Affine.MixedCoordinateVolume
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# Cubic overlap decay for quadratic Parsell–Vinogradov frames

The centered quadratic moment map uses coordinates `(z,z²,x,x²,xz)`.
Selecting the original coordinates `z,z²` and the transformed coordinates
`z,xz,z²` produces a determinant `θ³`, independent of translation. This
controls the overlap of two radius-one cubes uniformly in both real parameters.
At zero translation, an explicit inverse of the selected coordinates places a
fixed small cube inside the overlap and gives a matching cubic lower bound.
-/

open MeasureTheory Matrix
open scoped ENNReal
open GaloisForLFunctions.BiarithmeticGeometry.MixedCoordinateVolume

namespace GaloisForLFunctions.BiarithmeticGeometry.ParsellVinogradov.Quadratic
noncomputable section

/-- Coordinates are ordered as `(z,z²,x,x²,xz)` to isolate a cubic minor. -/
abbrev Index := Fin 2 ⊕ Fin 3
abbrev Space := Index → ℝ

/-- The degree-two moment surface in the adapted coordinate order. -/
def moment (x z : ℝ) : Space := Sum.elim ![z, z ^ 2] ![x, x ^ 2, x * z]

/-- Matrix of the centered shear and vertical translation on quadratic moments. -/
def frameMatrix (θ t : ℝ) : Matrix Index Index ℝ :=
  Matrix.fromBlocks !![1, 0; 2 * t, 1]
    !![θ, 0, 0; 2 * t * θ, θ ^ 2, 2 * θ] 0
    !![1, 0, 0; 0, 1, 0; t, θ, 1]

/-- Coordinate polynomial of the centered quadratic frame. -/
def frameValues (θ t : ℝ) (v : Space) : Space :=
  Sum.elim
    ![v (.inl 0) + θ * v (.inr 0),
      v (.inl 1) + 2 * t * v (.inl 0) + 2 * t * θ * v (.inr 0) +
        θ ^ 2 * v (.inr 1) + 2 * θ * v (.inr 2)]
    ![v (.inr 0), v (.inr 1), t * v (.inr 0) + θ * v (.inr 1) + v (.inr 2)]

/-- The actual linear frame acting on moment coordinates. -/
def frame (θ t : ℝ) : Space →ₗ[ℝ] Space where
  toFun := frameValues θ t
  map_add' v w := by
    funext i
    rcases i with i | i <;> fin_cases i <;> simp [frameValues] <;> ring
  map_smul' a v := by
    funext i
    rcases i with i | i <;> fin_cases i <;> simp [frameValues, smul_eq_mul] <;> ring

/-- Coordinate formula for the centered quadratic frame. -/
theorem frame_apply (θ t : ℝ) (v : Space) :
    frame θ t v = Sum.elim
      ![v (.inl 0) + θ * v (.inr 0),
        v (.inl 1) + 2 * t * v (.inl 0) + 2 * t * θ * v (.inr 0) +
          θ ^ 2 * v (.inr 1) + 2 * θ * v (.inr 2)]
      ![v (.inr 0), v (.inr 1), t * v (.inr 0) + θ * v (.inr 1) + v (.inr 2)] := rfl

private theorem frame_eq_toLin (θ t : ℝ) : frame θ t = Matrix.toLin' (frameMatrix θ t) := by
  apply LinearMap.ext
  intro v
  rw [frame_apply, Matrix.toLin'_apply]
  funext i
  rcases i with i | i <;> fin_cases i <;>
    simp [frameMatrix, Matrix.mulVec, dotProduct,
      Fintype.sum_sum_type, Fin.sum_univ_two, Fin.sum_univ_three]
  all_goals ring

/-- The frame is exactly the centered action of `(x,z) ↦ (x,z+θx+t)` on moments. -/
theorem frame_moment (θ t x z : ℝ) :
    frame θ t (moment x z) = moment x (z + θ * x + t) - moment 0 t := by
  rw [frame_apply]
  funext i
  rcases i with i | i <;> fin_cases i <;> simp [moment] <;> ring

/-- Both shear and translation parameters add under composition. -/
theorem frame_comp_apply (θ φ t s : ℝ) (v : Space) :
    frame θ t (frame φ s v) = frame (θ + φ) (t + s) v := by
  simp only [frame_apply]
  funext i
  rcases i with i | i <;> fin_cases i <;> simp <;> ring

@[simp] theorem frame_zero_apply (v : Space) : frame 0 0 v = v := by
  rw [frame_apply]
  funext i
  rcases i with i | i <;> fin_cases i <;> simp

/-- Each quadratic frame has determinant one. -/
theorem det_frame (θ t : ℝ) : (frame θ t).det = 1 := by
  rw [frame_eq_toLin, LinearMap.det_toLin']
  simp [frameMatrix, Matrix.det_fromBlocks_zero₂₁,
    Matrix.det_fin_two, Matrix.det_fin_three]

/-- Negating both parameters gives the inverse, on arbitrary sets. -/
theorem frame_image_eq_preimage_neg (θ t : ℝ) (S : Set Space) :
    frame θ t '' S = frame (-θ) (-t) ⁻¹' S := by
  ext v
  constructor
  · rintro ⟨u, hu, rfl⟩
    change frame (-θ) (-t) (frame θ t u) ∈ S
    simpa only [frame_comp_apply, neg_add_cancel, frame_zero_apply] using hu
  · intro hv
    refine ⟨frame (-θ) (-t) v, hv, ?_⟩
    simp only [frame_comp_apply, add_neg_cancel, frame_zero_apply]

/-- Original `z,z²`, followed by transformed `z,xz,z²`. -/
def overlapSelector : Index → Index ⊕ Index :=
  Sum.elim ![.inl (.inl 0), .inl (.inl 1)]
    ![.inr (.inl 0), .inr (.inr 2), .inr (.inl 1)]

/-- The mixed-coordinate matrix has a lower triangular block decomposition. -/
def overlapMatrix (θ t : ℝ) : Matrix Index Index ℝ :=
  Matrix.fromBlocks !![1, 0; 0, 1] 0 !![1, 0; 0, 0; 2 * t, 1]
    !![θ, 0, 0; t, θ, 1; 2 * t * θ, θ ^ 2, 2 * θ]

private theorem mixed_eq_toLin (θ t : ℝ) :
    mixed (frame θ t) overlapSelector = Matrix.toLin' (overlapMatrix θ t) := by
  apply LinearMap.ext
  intro v
  funext i
  rcases i with i | i <;> fin_cases i <;>
    simp [mixed_apply, overlapSelector, frame_apply, overlapMatrix, Matrix.toLin'_apply,
      Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two, Fin.sum_univ_three]
  all_goals ring

/-- Translation cancels from the decisive minor, whose determinant is exactly `θ³`. -/
theorem det_mixed (θ t : ℝ) : (mixed (frame θ t) overlapSelector).det = θ ^ 3 := by
  rw [mixed_eq_toLin, LinearMap.det_toLin']
  rw [overlapMatrix, Matrix.det_fromBlocks_zero₁₂, Matrix.det_fin_two, Matrix.det_fin_three]
  change ((1 : ℝ) * 1 - 0 * 0) *
    (θ * θ * (2 * θ) - θ * 1 * θ ^ 2 - 0 * t * (2 * θ) +
      0 * 1 * (2 * t * θ) + 0 * t * θ ^ 2 - 0 * θ * (2 * t * θ)) = θ ^ 3
  ring

/-- The closed radius-one cube in the five moment coordinates. -/
def Q : Set Space := cube Index 1

/-- Intersection measured in the original frame and the transformed frame. -/
def overlap (θ t : ℝ) : Set Space := Q ∩ frame θ t ⁻¹' Q

theorem volume_Q : volume Q = 32 := by
  rw [Q, volume_cube]
  norm_num [Fintype.card_sum, Fintype.card_fin]

/-- Every overlap is contained in the radius-one cube. -/
theorem volume_overlap_le (θ t : ℝ) : volume (overlap θ t) ≤ 32 := by
  rw [← volume_Q]
  exact measure_mono Set.inter_subset_left

/-- The cubic minor controls overlap volume even at zero shear. -/
theorem cubic_mul_volume_overlap_le (θ t : ℝ) :
    ENNReal.ofReal (|θ| ^ 3) * volume (overlap θ t) ≤ 32 := by
  have h := determinant_mul_volume_overlap_le (frame θ t) overlapSelector 1
  rw [det_mixed, abs_pow] at h
  norm_num [Fintype.card_sum, Fintype.card_fin] at h
  simpa only [overlap, Q, ENNReal.ofReal_pow (abs_nonneg θ)] using h

private theorem volume_overlap_ne_top (θ t : ℝ) : volume (overlap θ t) ≠ ∞ :=
  ne_of_lt ((volume_overlap_le θ t).trans_lt (by norm_num))

private theorem cubic_mul_real_volume_le (θ t : ℝ) :
    |θ| ^ 3 * (volume (overlap θ t)).toReal ≤ 32 := by
  have h := ENNReal.toReal_mono (by norm_num : (32 : ℝ≥0∞) ≠ ∞)
    (cubic_mul_volume_overlap_le θ t)
  simpa only [ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (pow_nonneg (abs_nonneg θ) 3), ENNReal.toReal_ofNat] using h

/-- The small-shear and large-shear estimates combine with one explicit constant. -/
theorem regularized_cubic_mul_real_volume_le (θ t : ℝ) :
    (1 + |θ|) ^ 3 * (volume (overlap θ t)).toReal ≤ 256 := by
  have hv : 0 ≤ (volume (overlap θ t)).toReal := ENNReal.toReal_nonneg
  by_cases hθ : |θ| ≤ 1
  · have hpow : (1 + |θ|) ^ 3 ≤ (2 : ℝ) ^ 3 :=
      pow_le_pow_left₀ (by positivity) (by linarith only [hθ]) 3
    have hvol : (volume (overlap θ t)).toReal ≤ 32 := by
      have h := ENNReal.toReal_mono (by norm_num : (32 : ℝ≥0∞) ≠ ∞) (volume_overlap_le θ t)
      simpa only [ENNReal.toReal_ofNat] using h
    have h := mul_le_mul hpow hvol hv (by norm_num : (0 : ℝ) ≤ 2 ^ 3)
    norm_num at h
    exact h
  · have ha : 1 ≤ |θ| := (lt_of_not_ge hθ).le
    calc
      _ ≤ (2 * |θ|) ^ 3 * (volume (overlap θ t)).toReal :=
        mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (by positivity) (by linarith only [ha]) 3) hv
      _ = 8 * (|θ| ^ 3 * (volume (overlap θ t)).toReal) := by ring
      _ ≤ 8 * 32 := mul_le_mul_of_nonneg_left (cubic_mul_real_volume_le θ t) (by norm_num)
      _ = 256 := by norm_num

/-- Cubic overlap decay holds for every real shear, uniformly in vertical translation. -/
theorem volume_overlap_le_decay (θ t : ℝ) :
    volume (overlap θ t) ≤ ENNReal.ofReal (256 / (1 + |θ|) ^ 3) := by
  calc
    _ = ENNReal.ofReal (volume (overlap θ t)).toReal :=
      (ENNReal.ofReal_toReal (volume_overlap_ne_top θ t)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by
      apply (le_div_iff₀ (by positivity : (0 : ℝ) < (1 + |θ|) ^ 3)).mpr
      simpa only [mul_comm] using regularized_cubic_mul_real_volume_le θ t)

/-- The image-overlap form of cubic decay, for all real frame parameters. -/
theorem volume_cube_inter_frame_le (θ t : ℝ) :
    volume (Q ∩ frame θ t '' Q) ≤ ENNReal.ofReal (256 / (1 + |θ|) ^ 3) := by
  rw [frame_image_eq_preimage_neg]
  simpa only [overlap, abs_neg] using volume_overlap_le_decay (-θ) (-t)

/-- The concrete quadratic frames preserve outer volume on every set. -/
theorem volume_frame_image (θ t : ℝ) (S : Set Space) :
    volume (frame θ t '' S) = volume S := by
  simpa only [det_frame, abs_one, ENNReal.ofReal_one, one_mul] using
    Measure.addHaar_image_linearMap volume (frame θ t) S

/-- Relative overlap depends only on parameter differences. -/
theorem volume_two_frames (θ φ t s : ℝ) :
    volume (frame θ t '' Q ∩ frame φ s '' Q) =
      volume (Q ∩ frame (φ - θ) (s - t) '' Q) := by
  have hi : Function.Injective (frame θ t) := by
    apply Function.LeftInverse.injective (g := frame (-θ) (-t))
    intro v
    simp only [frame_comp_apply, neg_add_cancel, frame_zero_apply]
  have hc : (fun v => frame θ t (frame (φ - θ) (s - t) v)) = frame φ s := by
    funext v
    rw [frame_comp_apply, show θ + (φ - θ) = φ by ring, show t + (s - t) = s by ring]
  have hset : frame θ t '' (Q ∩ frame (φ - θ) (s - t) '' Q) =
      frame θ t '' Q ∩ frame φ s '' Q := by
    rw [Set.image_inter hi, Set.image_image, hc]
  rw [← hset, volume_frame_image]

/-- Two arbitrary quadratic frames have cubic decay in their relative shear. -/
theorem volume_two_frames_le (θ φ t s : ℝ) :
    volume (frame θ t '' Q ∩ frame φ s '' Q) ≤
      ENNReal.ofReal (256 / (1 + |φ - θ|) ^ 3) := by
  rw [volume_two_frames]
  exact volume_cube_inter_frame_le (φ - θ) (s - t)

/-- Inverse of the selected coordinates for a nonzero shear at zero translation. -/
def unmix (θ : ℝ) (y : Space) : Space :=
  Sum.elim ![y (.inl 0), y (.inl 1)]
    ![(y (.inr 0) - y (.inl 0)) / θ,
      (2 * θ * y (.inr 1) - y (.inr 2) + y (.inl 1)) / θ ^ 2,
      (y (.inr 2) - y (.inl 1) - θ * y (.inr 1)) / θ]

private theorem mixed_frame_unmix {θ : ℝ} (hθ : θ ≠ 0) (y : Space) :
    mixed (frame θ 0) overlapSelector (unmix θ y) = y := by
  funext i
  rcases i with i | i <;> fin_cases i <;>
    simp [mixed_apply, overlapSelector, frame_apply, unmix] <;> field_simp [hθ] <;> ring

private theorem frame_unmix {θ : ℝ} (hθ : θ ≠ 0) (y : Space) :
    frame θ 0 (unmix θ y) = Sum.elim ![y (.inr 0), y (.inr 2)]
      ![(unmix θ y) (.inr 0), (unmix θ y) (.inr 1), y (.inr 1)] := by
  rw [frame_apply]
  funext i
  rcases i with i | i <;> fin_cases i <;>
    simp [unmix] <;> field_simp [hθ] <;> ring

/-- A fixed small cube in the selected coordinates fits inside every large-shear overlap. -/
private theorem unmix_mem_overlap {θ : ℝ} (ha : 1 ≤ |θ|) {y : Space}
    (hy : y ∈ cube Index (1 / 4)) : unmix θ y ∈ overlap θ 0 := by
  have hb := (mem_cube_iff y (1 / 4)).mp hy
  have ha0 : 0 < |θ| := zero_lt_one.trans_le ha
  have hθ : θ ≠ 0 := by
    intro h
    rw [h, abs_zero] at ha
    norm_num at ha
  have hx : |(y (.inr 0) - y (.inl 0)) / θ| ≤ 1 := by
    rw [abs_div]
    apply (div_le_iff₀ ha0).mpr
    calc
      _ ≤ |y (.inr 0)| + |y (.inl 0)| := abs_sub _ _
      _ ≤ 1 / 4 + 1 / 4 := add_le_add (hb _) (hb _)
      _ ≤ 1 * |θ| := by linarith only [ha]
  have hu : |(2 * θ * y (.inr 1) - y (.inr 2) + y (.inl 1)) / θ ^ 2| ≤ 1 := by
    rw [abs_div, abs_pow]
    apply (div_le_iff₀ (sq_pos_of_pos ha0)).mpr
    calc
      _ ≤ |2 * θ * y (.inr 1) - y (.inr 2)| + |y (.inl 1)| := abs_add_le _ _
      _ ≤ (|2 * θ * y (.inr 1)| + |y (.inr 2)|) + |y (.inl 1)| :=
        add_le_add (abs_sub _ _) le_rfl
      _ = 2 * |θ| * |y (.inr 1)| + |y (.inr 2)| + |y (.inl 1)| := by
        rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      _ ≤ 2 * |θ| * (1 / 4) + 1 / 4 + 1 / 4 :=
        add_le_add (add_le_add
          (mul_le_mul_of_nonneg_left (hb _) (by positivity)) (hb _)) (hb _)
      _ ≤ 1 * |θ| ^ 2 := by
        have h := mul_nonneg (abs_nonneg θ) (sub_nonneg.mpr ha)
        nlinarith only [ha, h]
  have hw : |(y (.inr 2) - y (.inl 1) - θ * y (.inr 1)) / θ| ≤ 1 := by
    rw [abs_div]
    apply (div_le_iff₀ ha0).mpr
    calc
      _ ≤ |y (.inr 2) - y (.inl 1)| + |θ * y (.inr 1)| := abs_sub _ _
      _ ≤ (|y (.inr 2)| + |y (.inl 1)|) + |θ * y (.inr 1)| :=
        add_le_add (abs_sub _ _) le_rfl
      _ = |y (.inr 2)| + |y (.inl 1)| + |θ| * |y (.inr 1)| := by rw [abs_mul]
      _ ≤ 1 / 4 + 1 / 4 + |θ| * (1 / 4) :=
        add_le_add (add_le_add (hb _) (hb _))
          (mul_le_mul_of_nonneg_left (hb _) (abs_nonneg θ))
      _ ≤ 1 * |θ| := by linarith only [ha]
  have hquarter : (1 / 4 : ℝ) ≤ 1 := by norm_num
  change unmix θ y ∈ cube Index 1 ∧ frame θ 0 (unmix θ y) ∈ cube Index 1
  constructor
  · apply (mem_cube_iff _ _).mpr
    intro i
    rcases i with i | i
    · fin_cases i
      · exact (hb (.inl 0)).trans hquarter
      · exact (hb (.inl 1)).trans hquarter
    · fin_cases i
      · exact hx
      · exact hu
      · exact hw
  · rw [frame_unmix hθ]
    apply (mem_cube_iff _ _).mpr
    intro i
    rcases i with i | i
    · fin_cases i
      · exact (hb (.inr 0)).trans hquarter
      · exact (hb (.inr 2)).trans hquarter
    · fin_cases i
      · exact hx
      · exact hu
      · exact (hb (.inr 1)).trans hquarter

private theorem small_cube_subset_overlap {θ : ℝ} (ha : |θ| ≤ 1) :
    cube Index (1 / 4) ⊆ overlap θ 0 := by
  intro v hv
  have hb := (mem_cube_iff v (1 / 4)).mp hv
  have hquarter : (1 / 4 : ℝ) ≤ 1 := by norm_num
  have hm (j : Index) : |θ * v j| ≤ 1 / 4 := by
    rw [abs_mul]
    simpa only [one_mul] using mul_le_mul ha (hb j) (abs_nonneg (v j)) zero_le_one
  have hs : |θ ^ 2| ≤ 1 := by
    rw [abs_pow]
    simpa only [one_pow] using pow_le_pow_left₀ (abs_nonneg θ) ha 2
  have hm2 (j : Index) : |θ ^ 2 * v j| ≤ 1 / 4 := by
    rw [abs_mul]
    simpa only [one_mul] using mul_le_mul hs (hb j) (abs_nonneg (v j)) zero_le_one
  have htwice (j : Index) : |2 * θ * v j| ≤ 1 / 2 := by
    rw [mul_assoc, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have h := mul_le_mul_of_nonneg_left (hm j) (by norm_num : (0 : ℝ) ≤ 2)
    norm_num at h
    simpa only [abs_mul] using h
  have hz : |v (.inl 0) + θ * v (.inr 0)| ≤ 1 := by
    calc
      _ ≤ |v (.inl 0)| + |θ * v (.inr 0)| := abs_add_le _ _
      _ ≤ 1 / 4 + 1 / 4 := add_le_add (hb _) (hm _)
      _ ≤ 1 := by norm_num
  have hzz : |v (.inl 1) + θ ^ 2 * v (.inr 1) + 2 * θ * v (.inr 2)| ≤ 1 := by
    calc
      _ ≤ |v (.inl 1) + θ ^ 2 * v (.inr 1)| + |2 * θ * v (.inr 2)| := abs_add_le _ _
      _ ≤ (|v (.inl 1)| + |θ ^ 2 * v (.inr 1)|) + |2 * θ * v (.inr 2)| :=
        add_le_add (abs_add_le _ _) le_rfl
      _ ≤ (1 / 4 + 1 / 4) + 1 / 2 := add_le_add (add_le_add (hb _) (hm2 _)) (htwice _)
      _ = 1 := by norm_num
  have hxz : |θ * v (.inr 1) + v (.inr 2)| ≤ 1 := by
    calc
      _ ≤ |θ * v (.inr 1)| + |v (.inr 2)| := abs_add_le _ _
      _ ≤ 1 / 4 + 1 / 4 := add_le_add (hm _) (hb _)
      _ ≤ 1 := by norm_num
  change v ∈ cube Index 1 ∧ frame θ 0 v ∈ cube Index 1
  constructor
  · exact (mem_cube_iff _ _).mpr (fun i => (hb i).trans hquarter)
  · rw [frame_apply]
    simp only [zero_mul, mul_zero, zero_add, add_zero]
    apply (mem_cube_iff _ _).mpr
    intro i
    rcases i with i | i
    · fin_cases i
      · exact hz
      · exact hzz
    · fin_cases i
      · exact (hb (.inr 0)).trans hquarter
      · exact (hb (.inr 1)).trans hquarter
      · exact hxz

private theorem volume_small_cube : volume (cube Index (1 / 4)) = ENNReal.ofReal (1 / 32) := by
  rw [volume_cube, ← ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2 * (1 / 4))]
  congr 1
  norm_num [Fintype.card_sum, Fintype.card_fin]

private theorem cubic_mul_real_volume_ge {θ : ℝ} (ha : 1 ≤ |θ|) :
    (1 / 32 : ℝ) ≤ |θ| ^ 3 * (volume (overlap θ 0)).toReal := by
  have hθ : θ ≠ 0 := abs_pos.mp (zero_lt_one.trans_le ha)
  have hsubset : cube Index (1 / 4) ⊆ mixed (frame θ 0) overlapSelector '' overlap θ 0 := by
    intro y hy
    exact ⟨unmix θ y, unmix_mem_overlap ha hy, mixed_frame_unmix hθ y⟩
  have h := measure_mono hsubset (μ := volume)
  rw [volume_small_cube, Measure.addHaar_image_linearMap, det_mixed, abs_pow] at h
  have hfinite : ENNReal.ofReal (|θ| ^ 3) * volume (overlap θ 0) ≠ ∞ :=
    ne_of_lt ((cubic_mul_volume_overlap_le θ 0).trans_lt (by norm_num))
  have hr := ENNReal.toReal_mono hfinite h
  simpa only [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 32),
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg (abs_nonneg θ) 3)] using hr

/-- At zero translation the cubic rate is also a lower bound, for every real shear. -/
theorem regularized_cubic_mul_real_volume_ge (θ : ℝ) :
    (1 / 32 : ℝ) ≤ (1 + |θ|) ^ 3 * (volume (overlap θ 0)).toReal := by
  have hv : 0 ≤ (volume (overlap θ 0)).toReal := ENNReal.toReal_nonneg
  by_cases ha : |θ| ≤ 1
  · have h := measure_mono (small_cube_subset_overlap ha) (μ := volume)
    rw [volume_small_cube] at h
    have hr := ENNReal.toReal_mono (volume_overlap_ne_top θ 0) h
    have hlo : (1 / 32 : ℝ) ≤ (volume (overlap θ 0)).toReal := by
      simpa only [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 32)] using hr
    have hpow : (1 : ℝ) ≤ (1 + |θ|) ^ 3 := by
      have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1)
        (show (1 : ℝ) ≤ 1 + |θ| by linarith only [abs_nonneg θ]) 3
      simpa only [one_pow] using h
    calc
      _ ≤ (volume (overlap θ 0)).toReal := hlo
      _ = 1 * (volume (overlap θ 0)).toReal := (one_mul _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right hpow hv
  · calc
      _ ≤ |θ| ^ 3 * (volume (overlap θ 0)).toReal :=
        cubic_mul_real_volume_ge (lt_of_not_ge ha).le
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (abs_nonneg θ) (by linarith only [abs_nonneg θ]) 3) hv

/-- A global lower bound proves that cubic shear decay cannot be improved. -/
theorem volume_overlap_ge_decay (θ : ℝ) :
    ENNReal.ofReal (1 / (32 * (1 + |θ|) ^ 3)) ≤ volume (overlap θ 0) := by
  rw [← ENNReal.ofReal_toReal (volume_overlap_ne_top θ 0)]
  apply ENNReal.ofReal_le_ofReal
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 32 * (1 + |θ|) ^ 3)).mpr
  have h := regularized_cubic_mul_real_volume_ge θ
  nlinarith only [h]

/-- Two-sided cubic decay for the unshifted quadratic frame. -/
theorem volume_overlap_two_sided (θ : ℝ) :
    ENNReal.ofReal (1 / (32 * (1 + |θ|) ^ 3)) ≤ volume (overlap θ 0) ∧
      volume (overlap θ 0) ≤ ENNReal.ofReal (256 / (1 + |θ|) ^ 3) :=
  ⟨volume_overlap_ge_decay θ, volume_overlap_le_decay θ 0⟩

#print axioms frame_moment
#print axioms frame_comp_apply
#print axioms det_frame
#print axioms frame_image_eq_preimage_neg
#print axioms det_mixed
#print axioms cubic_mul_volume_overlap_le
#print axioms volume_overlap_le_decay
#print axioms volume_cube_inter_frame_le
#print axioms volume_two_frames_le
#print axioms volume_overlap_ge_decay
#print axioms volume_overlap_two_sided

end
end GaloisForLFunctions.BiarithmeticGeometry.ParsellVinogradov.Quadratic
