import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainMeanLineBounds
import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainMeanHorizontal
import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainMeanResidue
import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainTargetAverage
import Mathlib.Analysis.MellinInversion

/-!
# The boundary contour of the averaged Narain source

Absolute Mellin inversion and vanishing horizontal edges shift the actual mean from
the Euler line to the square-root boundary, retaining its exact double-pole residue.
-/

open Complex RHTower Set Filter Topology MeasureTheory
open GaloisForLFunctions.BlackHoleRingdown
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap

/-- The actual scalar mean in the physical Mellin variable. -/
def narainMeanMellin (Y Z : Height) (s : ℂ) : ℂ := narainMellinMean Y Z (s - 1 / 2)

private theorem boundary_line (Y Z : Height) (t : ℝ) :
    narainMeanMellin Y Z ((1 / 2 : ℝ) + (t : ℂ) * I) =
      narainMellinMean Y Z ((t : ℂ) * I) := by
  unfold narainMeanMellin
  congr 1
  push_cast
  ring

private theorem right_line (Y Z : Height) (t : ℝ) :
    narainMeanMellin Y Z ((2 : ℝ) + (t : ℂ) * I) =
      narainMellinMean Y Z ((3 / 2 : ℝ) + (t : ℂ) * I) := by
  unfold narainMeanMellin
  congr 1
  push_cast
  ring

/-- Both vertical lines of the boundary contour are absolutely integrable. -/
theorem verticalIntegrable_narainMeanMellin (Y Z : Height) :
    VerticalIntegrable (narainMeanMellin Y Z) (1 / 2) ∧
      VerticalIntegrable (narainMeanMellin Y Z) 2 := by
  constructor
  · simpa only [VerticalIntegrable, boundary_line] using integrable_narainMellinMean_boundary Y Z
  · simpa only [VerticalIntegrable, right_line] using
      integrable_narainMellinMean_positive_line Y Z (a := 3 / 2) (by norm_num) (by norm_num)

/-- Mellin inversion reconstructs the actual target-averaged heat source on the Euler line. -/
theorem mellinInv_narainMeanMellin (Y Z : Height) {y : ℝ} (hy : 0 < y) :
    mellinInv 2 (narainMeanMellin Y Z) y = narainScalarHeatAverage Y Z y := by
  have heq (t : ℝ) : mellin (narainScalarHeatAverage Y Z) ((2 : ℝ) + (t : ℂ) * I) =
      narainMeanMellin Y Z ((2 : ℝ) + (t : ℂ) * I) :=
    mellin_narainScalarHeatAverage Y Z (by simp)
  have hv : VerticalIntegrable (mellin (narainScalarHeatAverage Y Z)) 2 := by
    simpa only [VerticalIntegrable, heq] using (verticalIntegrable_narainMeanMellin Y Z).2
  have hm := mellinInv_mellin_eq 2 (narainScalarHeatAverage Y Z) hy
    (mellinConvergent_narainScalarHeatAverage Y Z (s := 2) (by norm_num)) hv
    ((continuousOn_narainScalarHeatAverage Y Z).continuousAt (isOpen_Ioi.mem_nhds hy))
  rw [← hm, mellinInv, mellinInv]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with t
  rw [heq]

private theorem differentiable_mellin_weight {y : ℝ} (hy : 0 < y) :
    Differentiable ℂ (fun s : ℂ => (y : ℂ) ^ (-s)) :=
  (by fun_prop : Differentiable ℂ (fun s : ℂ => -s)).const_cpow
    (Or.inl (Complex.ofReal_ne_zero.mpr hy.ne'))

private theorem integrable_weighted_vertical {F : ℂ → ℂ} {a y : ℝ}
    (hy : 0 < y) (hF : VerticalIntegrable F a) :
    Integrable (fun t : ℝ => (y : ℂ) ^ (-((a : ℂ) + t * I)) * F ((a : ℂ) + t * I)) := by
  have hw : Continuous (fun t : ℝ => (y : ℂ) ^ (-((a : ℂ) + t * I))) :=
    (differentiable_mellin_weight hy).continuous.comp (by fun_prop)
  apply (hF.norm.const_mul (y ^ (-a))).mono' (hw.aestronglyMeasurable.mul hF.aestronglyMeasurable)
  filter_upwards [] with t
  dsimp only [Pi.mul_apply]
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy]
  simp

/-- The physical mean is analytic throughout the boundary strip except at its main pole. -/
theorem analyticAt_narainMeanMellin (Y Z : Height) {s : ℂ}
    (hs : 1 / 2 ≤ s.re) (hs₁ : s ≠ 1) : AnalyticAt ℂ (narainMeanMellin Y Z) s := by
  have hu : 0 ≤ (s - 1 / 2).re := by simp; linarith only [hs]
  have hn : s - 1 / 2 ≠ 1 / 2 := by
    intro h
    apply hs₁
    linear_combination h
  exact AnalyticAt.comp (g := narainMellinMean Y Z)
    (f := fun z : ℂ => z - 1 / 2) (x := s)
    (analyticAt_narainMellinMean_of_nonneg_re Y Z hu hn) (by fun_prop)

/-- The boundary contour shift, with the exact double-pole residue. -/
theorem narainMeanMellin_contour_shift (Y Z : Height) {y : ℝ} (hy : 0 < y) :
    mellinInv 2 (narainMeanMellin Y Z) y - mellinInv (1 / 2) (narainMeanMellin Y Z) y =
      (y : ℂ) ^ (-1 : ℂ) *
        (narainAverageConstant Y Z - (3 / (Real.pi : ℂ)) * (Real.log y : ℂ)) := by
  have hw := differentiable_mellin_weight hy
  have hmero : MeromorphicAt (fun s : ℂ => (y : ℂ) ^ (-s) * narainMeanMellin Y Z s) 1 :=
    (hw.analyticAt 1).meromorphicAt.mul (meromorphicAt_narainMellinMean_shift_one Y Z)
  have hoff (s : ℂ) (hs : 1 / 2 ≤ s.re) (_ : s.re ≤ 2) (hne : s ∉ ({1} : Finset ℂ)) :
      AnalyticAt ℂ (fun z : ℂ => (y : ℂ) ^ (-z) * narainMeanMellin Y Z z) s :=
    (hw.analyticAt s).mul (analyticAt_narainMeanMellin Y Z hs (by simpa using hne))
  have hT : Tendsto (fun k => goodHeight k / 2) atTop atTop :=
    tendsto_goodHeight.atTop_div_const (by norm_num)
  have hres := verticalIntegral_sub_eq_sum_laurentCoeff_of_horizontal_tendsto_seq
    (f := fun s : ℂ => (y : ℂ) ^ (-s) * narainMeanMellin Y Z s)
    (a := 1 / 2) (c := 2) (by norm_num) (P := {1})
    (by intro p hp; simp only [Finset.mem_singleton] at hp; subst p; norm_num)
    (by intro p hp; simp only [Finset.mem_singleton] at hp; subst p; exact hmero) hoff
    (integrable_weighted_vertical hy (verticalIntegrable_narainMeanMellin Y Z).1)
    (integrable_weighted_vertical hy (verticalIntegrable_narainMeanMellin Y Z).2) hT
    (narainMellinMean_horizontal_tendsto_zero Y Z hy).1
    (narainMellinMean_horizontal_tendsto_zero Y Z hy).2
  simp only [Finset.sum_singleton, narainMeanMellin, narainMellinMean_weighted_residue Y Z hy] at hres
  simp only [mellinInv, Complex.real_smul, smul_eq_mul, ← mul_sub]
  change ((1 / (2 * Real.pi) : ℝ) : ℂ) * _ = _
  dsimp only [narainMeanMellin]
  rw [hres]
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]

#print axioms mellinInv_narainMeanMellin
#print axioms narainMeanMellin_contour_shift
end GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
