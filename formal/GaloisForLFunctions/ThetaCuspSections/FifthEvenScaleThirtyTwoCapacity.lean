import GaloisForLFunctions.ThetaCuspSections.FifthEvenPolynomialCrossObstruction
import GaloisForLFunctions.ThetaCuspSections.CrossLoadCapacity

/-!
# The admissible quartic load at theta scale thirty-two

The unit quartic repair fails, but its admissible scalar loads have an exact
positive threshold. Strict positivity holds below it, semidefiniteness through
it, and the boundary source is singular.
-/

noncomputable section
open Matrix RHTower RHTower.ThetaCuspGaussianLimit
namespace GaloisForLFunctions.ThetaCuspSections.ThirtyTwoCrossCapacity
open ThirtyTwoCrossSource ThirtyTwoCrossObstruction FifthNativeRay EvenFiveEndpoint

/-- Complete source with a scalar multiple of the quartic correction. -/
def scaledSource (t : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  loadedSource (t*FifthPolynomialCross.compensation center)

private def positiveLoad : Matrix (Fin 5) (Fin 5) ℝ :=
  (-FifthPolynomialCross.compensation center) • crossLoad paidSevenSchur

private theorem positiveLoad_posSemidef : positiveLoad.PosSemidef := by
  have h : FifthPolynomialCross.compensation center ≤ 0 :=
    profile_compensation_upper.trans (mul_nonpos_of_nonpos_of_nonneg
      (by norm_num) (sq_nonneg _))
  exact (crossCoefficient_posDef.posSemidef.conjTranspose_mul_mul_same loadMap).smul
    (neg_nonneg.mpr h)

private theorem source_posDef : (nativeShiftedMatrix 5 0 center).PosDef :=
  native_even_five_posDef (by rw [center_scale]; norm_num)

private theorem pencil_eq (t : ℝ) :
    CrossLoadCapacity.pencil (nativeShiftedMatrix 5 0 center) positiveLoad t=scaledSource t := by
  ext i j
  simp only [CrossLoadCapacity.pencil,positiveLoad,scaledSource,loadedSource,
    Matrix.sub_apply,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul]
  ring

private theorem unit_not_posSemidef :
    ¬ (CrossLoadCapacity.pencil (nativeShiftedMatrix 5 0 center) positiveLoad 1).PosSemidef := by
  rw [pencil_eq]
  simpa only [scaledSource,loadedSource,one_mul,FifthPolynomialCross.repair]
    using repair_not_posSemidef

/-- Supremal admissible scalar multiple of the quartic compensation. -/
def capacity : ℝ := CrossLoadCapacity.capacity (nativeShiftedMatrix 5 0 center) positiveLoad

/-- The complete source admits a nonempty interval of positive loads, but not the unit load. -/
theorem capacity_bounds : 0 < capacity ∧ capacity < 1 :=
  CrossLoadCapacity.capacity_bounds source_posDef positiveLoad_posSemidef unit_not_posSemidef

/-- Strict positivity is exactly the open capacity half-line. -/
theorem posDef_iff {t : ℝ} : (scaledSource t).PosDef ↔ t < capacity := by
  rw [← pencil_eq]
  exact CrossLoadCapacity.posDef_iff source_posDef positiveLoad_posSemidef unit_not_posSemidef

/-- Semidefiniteness includes the capacity endpoint and no larger load. -/
theorem posSemidef_iff {t : ℝ} : (scaledSource t).PosSemidef ↔ t ≤ capacity := by
  rw [← pencil_eq]
  exact CrossLoadCapacity.posSemidef_iff source_posDef positiveLoad_posSemidef unit_not_posSemidef

/-- The endpoint is positive semidefinite and singular. -/
theorem boundary : (scaledSource capacity).PosSemidef ∧ (scaledSource capacity).det=0 := by
  have h := CrossLoadCapacity.boundary source_posDef positiveLoad_posSemidef unit_not_posSemidef
  simpa only [pencil_eq,capacity] using h

/-- Exact admissibility classification for the complete quartic source at scale thirty-two. -/
theorem exact_scaling_capacity : ∃ τ : ℝ, 0 < τ ∧ τ < 1 ∧
    (∀ t : ℝ, (scaledSource t).PosDef ↔ t < τ) ∧
    (∀ t : ℝ, (scaledSource t).PosSemidef ↔ t ≤ τ) ∧
    (scaledSource τ).det=0 :=
  ⟨capacity,capacity_bounds.1,capacity_bounds.2,
    fun _ => posDef_iff,fun _ => posSemidef_iff,boundary.2⟩

/-- The explicit negative comparison excludes the load twenty-seven thirty-fifths. -/
theorem capacity_upper : capacity < 27/35 := by
  have hn : ¬ (scaledSource (27/35)).PosSemidef := by
    apply loaded_not_posSemidef
    have h := mul_le_mul_of_nonneg_left normalized_compensation_upper
      (by norm_num : (0 : ℝ) ≤ 27/35)
    change ((27/35)*FifthPolynomialCross.compensation center)/FifthRemainder.sourceUnit center ≤ _
    calc
      _ = (27/35)*(FifthPolynomialCross.compensation center/FifthRemainder.sourceUnit center) := by ring
      _ ≤ -216*61^2 := by nlinarith only [h]
  by_contra h
  exact hn (posSemidef_iff.mpr (le_of_not_gt h))

end GaloisForLFunctions.ThetaCuspSections.ThirtyTwoCrossCapacity
