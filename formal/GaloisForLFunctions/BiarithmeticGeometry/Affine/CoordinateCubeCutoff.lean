import GaloisForLFunctions.BiarithmeticGeometry.Affine.CoordinateCubeTranslations
import GaloisForLFunctions.HTGeometry.SmoothPlateau
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

/-!
# A smooth compact cutoff for coordinate cubes

The product of scalar plateaus equals one on the radius-three-halves cube
and vanishes whenever a coordinate has absolute value at least two. Its
open plateau contains the closed unit cube. The same explicit function,
viewed as complex-valued, is a Schwartz function.
-/

open scoped BigOperators
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.BiarithmeticGeometry.MixedCoordinateVolume

namespace GaloisForLFunctions.BiarithmeticGeometry.CoordinateCubeCutoff
noncomputable section

variable {ι : Type*} [Fintype ι]

/-- A product plateau with an open neighborhood of the unit cube on which it equals one. -/
def cubeCutoff (x : ι → ℝ) : ℝ := ∏ i, smoothPlateau (-2) 2 (1 / 2) (x i)

/-- Every value of the cutoff belongs to the unit interval. -/
theorem cubeCutoff_mem_Icc (x : ι → ℝ) : cubeCutoff x ∈ Set.Icc (0 : ℝ) 1 := by
  exact ⟨Finset.prod_nonneg (fun i _ => smoothPlateau_nonneg (x i)),
    Finset.prod_le_one (fun i _ => smoothPlateau_nonneg (x i))
      (fun i _ => smoothPlateau_le_one (x i))⟩

/-- The cutoff is one on a closed cube strictly larger than the unit cube. -/
theorem cubeCutoff_eq_one (x : ι → ℝ) (hx : x ∈ centeredCube 0 (3 / 2)) :
    cubeCutoff x = 1 := by
  rw [mem_centeredCube_iff] at hx
  simp only [Pi.zero_apply, sub_zero] at hx
  apply Finset.prod_eq_one
  intro i _
  apply smoothPlateau_eq_one (by norm_num)
  · linarith only [(abs_le.mp (hx i)).1]
  · linarith only [(abs_le.mp (hx i)).2]

/-- A coordinate on or beyond the radius-two boundary forces the cutoff to vanish. -/
theorem cubeCutoff_eq_zero_of_coordinate (x : ι → ℝ) (i : ι) (hi : 2 ≤ |x i|) :
    cubeCutoff x = 0 := by
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  rcases le_total 0 (x i) with h | h
  · rw [abs_of_nonneg h] at hi
    exact smoothPlateau_eq_zero_of_ge (by norm_num) hi
  · rw [abs_of_nonpos h] at hi
    exact smoothPlateau_eq_zero_of_le (by norm_num) (by linarith only [hi])

private theorem support_cubeCutoff_subset :
    Function.support (cubeCutoff : (ι → ℝ) → ℝ) ⊆ centeredCube 0 2 := by
  intro x hx
  change cubeCutoff x ≠ 0 at hx
  rw [mem_centeredCube_iff]
  intro i
  simp only [Pi.zero_apply, sub_zero]
  by_contra h
  exact hx (cubeCutoff_eq_zero_of_coordinate x i (not_le.mp h).le)

/-- The topological support lies in the closed radius-two cube. -/
theorem tsupport_cubeCutoff_subset :
    tsupport (cubeCutoff : (ι → ℝ) → ℝ) ⊆ centeredCube 0 2 :=
  closure_minimal support_cubeCutoff_subset isClosed_Icc

/-- The explicit product cutoff has compact support in every finite coordinate space. -/
theorem hasCompactSupport_cubeCutoff : HasCompactSupport (cubeCutoff : (ι → ℝ) → ℝ) := by
  exact (isCompact_Icc : IsCompact (centeredCube (0 : ι → ℝ) 2)).of_isClosed_subset
    (isClosed_tsupport _) tsupport_cubeCutoff_subset

/-- All derivatives of the product cutoff exist and are continuous. -/
theorem contDiff_cubeCutoff : ContDiff ℝ (↑(⊤ : ℕ∞)) (cubeCutoff : (ι → ℝ) → ℝ) := by
  unfold cubeCutoff
  apply contDiff_prod
  intro i _
  unfold smoothPlateau
  exact (Real.smoothTransition.contDiff.comp (by fun_prop)).mul
    (Real.smoothTransition.contDiff.comp (by fun_prop))

/-- The open coordinate cube on which the cutoff is identically one. -/
def cubeCore (ι : Type*) : Set (ι → ℝ) :=
  Set.univ.pi (fun _ => Set.Ioo (-(3 / 2 : ℝ)) (3 / 2))

theorem isOpen_cubeCore : IsOpen (cubeCore ι) :=
  isOpen_set_pi Set.finite_univ (fun _ _ => isOpen_Ioo)

omit [Fintype ι] in
/-- The closed unit cube lies strictly inside the open plateau. -/
theorem unitCube_subset_cubeCore : centeredCube (0 : ι → ℝ) 1 ⊆ cubeCore ι := by
  intro x hx
  rw [mem_centeredCube_iff] at hx
  simp only [Pi.zero_apply, sub_zero] at hx
  intro i _
  exact ⟨by linarith only [(abs_le.mp (hx i)).1],
    by linarith only [(abs_le.mp (hx i)).2]⟩

/-- The entire open core is a plateau of value one. -/
theorem cubeCutoff_eqOn_core : Set.EqOn (cubeCutoff : (ι → ℝ) → ℝ) 1 (cubeCore ι) := by
  intro x hx
  apply cubeCutoff_eq_one
  rw [mem_centeredCube_iff]
  intro i
  simp only [Pi.zero_apply, sub_zero]
  exact abs_le.mpr ⟨(hx i (Set.mem_univ i)).1.le, (hx i (Set.mem_univ i)).2.le⟩

/-- The actual complex-valued cutoff, bundled as a Schwartz function. -/
def cubeCutoffSchwartz (ι : Type*) [Fintype ι] : SchwartzMap (ι → ℝ) ℂ :=
  ((hasCompactSupport_cubeCutoff (ι := ι)).comp_left
    (show Complex.ofRealCLM 0 = 0 from rfl)).toSchwartzMap
      (Complex.ofRealCLM.contDiff.comp contDiff_cubeCutoff)

theorem cubeCutoffSchwartz_apply (x : ι → ℝ) :
    cubeCutoffSchwartz ι x = (cubeCutoff x : ℂ) := rfl

#print axioms cubeCutoff_mem_Icc
#print axioms cubeCutoff_eq_one
#print axioms cubeCutoff_eq_zero_of_coordinate
#print axioms tsupport_cubeCutoff_subset
#print axioms hasCompactSupport_cubeCutoff
#print axioms contDiff_cubeCutoff
#print axioms isOpen_cubeCore
#print axioms unitCube_subset_cubeCore
#print axioms cubeCutoff_eqOn_core
#print axioms cubeCutoffSchwartz

end
end GaloisForLFunctions.BiarithmeticGeometry.CoordinateCubeCutoff
