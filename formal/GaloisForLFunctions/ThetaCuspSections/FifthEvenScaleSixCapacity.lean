import GaloisForLFunctions.ThetaCuspSections.FifthEvenScaleSixSourceBounds
import GaloisForLFunctions.ThetaCuspSections.CrossLoadCapacity

/-!
# Exact scaling capacity of the fixed theta cross-load

At scale six the negative compensation turns the positive cross-load into
an ordered affine pencil. Its positive interval ends at a singular
semidefinite matrix, strictly between zero and the full load.
-/

noncomputable section
open Matrix RHTower
namespace GaloisForLFunctions.ThetaCuspSections.SixCrossCapacity
open SixSourceBounds EightCrossData FifthNativeRay FifthRemainder

private def positiveLoad : Matrix (Fin 5) (Fin 5) ℝ :=
  (-(FifthPolynomialCross.compensation center/sourceUnit center)) • loadGram 6

private theorem positiveLoad_posSemidef : positiveLoad.PosSemidef := by
  have hK := sourceUnit_pos (x := center) (by rw [center_scale]; norm_num)
  exact (loadGram_posSemidef 6).smul
    (neg_nonneg.mpr (div_neg_of_neg_of_pos compensation_negative hK).le)

private theorem source_posDef : (sourceGram center).PosDef :=
  sourceGram_posDef (by rw [center_scale]; norm_num)

private theorem pencil_eq (t : ℝ) :
    CrossLoadCapacity.pencil (sourceGram center) positiveLoad t=scaledGram t := by
  rw [scaledGram_eq]
  ext i j
  simp only [CrossLoadCapacity.pencil,positiveLoad,Matrix.sub_apply,Matrix.add_apply,
    Matrix.smul_apply,smul_eq_mul]
  ring

private theorem unit_not_posSemidef :
    ¬ (CrossLoadCapacity.pencil (sourceGram center) positiveLoad 1).PosSemidef := by
  rw [pencil_eq]
  exact full_load_not_posSemidef

/-- Supremal scalar multiple preserving strict positivity at scale six. -/
def capacity : ℝ := CrossLoadCapacity.capacity (sourceGram center) positiveLoad

/-- Strict positivity holds precisely below the scaling capacity. -/
theorem posDef_iff {t : ℝ} : (scaledGram t).PosDef ↔ t < capacity := by
  rw [← pencil_eq]
  exact CrossLoadCapacity.posDef_iff source_posDef positiveLoad_posSemidef unit_not_posSemidef

/-- Native positivity and full-load failure leave a nonempty bounded admissible interval. -/
theorem capacity_bounds : 0 < capacity ∧ capacity < 1 :=
  CrossLoadCapacity.capacity_bounds source_posDef positiveLoad_posSemidef unit_not_posSemidef

/-- Nonnegativity includes the capacity endpoint and no larger load. -/
theorem posSemidef_iff {t : ℝ} : (scaledGram t).PosSemidef ↔ t ≤ capacity := by
  rw [← pencil_eq]
  exact CrossLoadCapacity.posSemidef_iff source_posDef positiveLoad_posSemidef unit_not_posSemidef

/-- The complete scalar loss places the endpoint strictly below a rational fraction of the full load. -/
theorem capacity_strict_upper : capacity < (1000/1251 : ℝ) := by
  have hp := mul_le_mul_of_nonneg_left normalized_compensation_bounds.2
    (by norm_num : (0 : ℝ) ≤ 1000/1251)
  have hc : ((1000/1251)*FifthPolynomialCross.compensation center)/sourceUnit center ≤ -100 := by
    rw [mul_div_assoc]
    nlinarith only [hp]
  have hn : ¬ (scaledSource (1000/1251)).PosSemidef := loaded_not_posSemidef hc
  by_contra h
  have hg := posSemidef_iff.mpr (not_lt.mp h)
  exact hn ((scaledGram_posSemidef_iff _).mp hg)

/-- At capacity the complete matrix is positive semidefinite and singular. -/
theorem boundary : (scaledGram capacity).PosSemidef ∧ (scaledGram capacity).det=0 := by
  have h := CrossLoadCapacity.boundary source_posDef positiveLoad_posSemidef unit_not_posSemidef
  simpa only [pencil_eq,capacity] using h

/-- Exact capacity law in the original moment coordinates. -/
theorem source_posDef_iff {t : ℝ} : (scaledSource t).PosDef ↔ t < capacity := by
  rw [← scaledGram_posDef_iff]
  exact posDef_iff

/-- Semidefiniteness holds on the closed capacity half-line. -/
theorem source_posSemidef_iff {t : ℝ} : (scaledSource t).PosSemidef ↔ t ≤ capacity := by
  rw [← scaledGram_posSemidef_iff]
  exact posSemidef_iff

/-- The capacity endpoint is a singular positive semidefinite complete source. -/
theorem source_boundary : (scaledSource capacity).PosSemidef ∧ (scaledSource capacity).det=0 := by
  have hp := (scaledGram_posSemidef_iff _).mp boundary.1
  refine ⟨hp,?_⟩
  by_contra hn
  have hd := hp.posDef_iff_det_ne_zero.mpr hn
  exact (not_lt_of_ge le_rfl) (posDef_iff.mp ((scaledGram_posDef_iff _).mpr hd))

/-- A strict rational bracket determines the sharp admissibility boundary. -/
theorem exact_scaling_capacity : ∃ τ : ℝ, 0 < τ ∧ τ < 1000/1251 ∧
    (∀ t : ℝ, (scaledSource t).PosDef ↔ t < τ) ∧
    (∀ t : ℝ, (scaledSource t).PosSemidef ↔ t ≤ τ) ∧
    (scaledSource τ).det=0 :=
  ⟨capacity,capacity_bounds.1,capacity_strict_upper,
    fun _ => source_posDef_iff,fun _ => source_posSemidef_iff,source_boundary.2⟩

end GaloisForLFunctions.ThetaCuspSections.SixCrossCapacity

