import GaloisForLFunctions.HTGeometry.PaperDirichletPrimitive
import Mathlib.Algebra.Field.Periodic

/-! # A globally bounded periodic primitive of the mean-zero Fourier kernel

The literal Dirichlet kernel has mean one. Subtracting the linear part of its
primitive produces a periodic primitive with a uniform bound on the whole line.
-/

noncomputable section

open MeasureTheory Set Filter Topology

namespace GaloisForLFunctions.HTGeometry.FourierLLogL.Period

private theorem phase_unit_integral (n : ℤ) :
    (∫ y in (0 : ℝ)..1, phase n y) = if n = 0 then 1 else 0 := by
  rw [← seg_eq_interval (phase n) zero_le_one]
  change (∫ y, phase n y ∂μ₁) = _
  have hc : (∫ y, phase n y ∂μ₁) =
      fourierCoeff (fun _ : Torus => (1 : ℂ)) (-n) := by
    rw [fourierCoeff_eq_integral, ← map_circle_volume]
    rw [integral_map (f := fun x : Torus => (1 : ℂ) * fourier (- -n) x)
      measurable_circle.aemeasurable (by fun_prop)]
    simp only [one_mul, neg_neg, fourier_circle]
  rw [hc]
  have he : (fun _ : Torus => (1 : ℂ)) = fourier (0 : ℤ) := by
    funext x
    exact fourier_zero.symm
  rw [he, fourierCoeff_fourier]
  by_cases hn : n = 0 <;> simp [hn]

theorem dirichletPrimitive_one (N : ℕ) : dirichletPrimitive N 1 = 1 := by
  unfold dirichletPrimitive dirichlet
  rw [intervalIntegral.integral_finsetSum (fun (n : ℤ) _ => (phase_cont n).intervalIntegrable _ _)]
  simp_rw [phase_unit_integral]
  simp

theorem hasDerivAt_dirichletPrimitive (N : ℕ) (t : ℝ) :
    HasDerivAt (dirichletPrimitive N) (dirichlet N t) t := by
  exact intervalIntegral.integral_hasDerivAt_right
    ((dirichlet_cont N).intervalIntegrable _ _)
    (dirichlet_cont N).aestronglyMeasurable.stronglyMeasurableAtFilter
    (dirichlet_cont N).continuousAt

theorem dirichletPrimitive_add_one (N : ℕ) (t : ℝ) :
    dirichletPrimitive N (t + 1) = dirichletPrimitive N t + 1 := by
  have h := (dirichlet_periodic N).intervalIntegral_add_eq_add 0 t
    (fun a b => (dirichlet_cont N).intervalIntegrable a b)
  simp only [zero_add] at h
  change dirichletPrimitive N (t + 1) = dirichletPrimitive N t + dirichletPrimitive N 1 at h
  simpa only [dirichletPrimitive_one] using h

/-- The mean-zero kernel primitive has matching endpoint values in every period. -/
def meanZeroDirichletPrimitive (N : ℕ) (t : ℝ) : ℂ := dirichletPrimitive N t - t

theorem meanZeroDirichletPrimitive_periodic (N : ℕ) :
    Function.Periodic (meanZeroDirichletPrimitive N) 1 := by
  intro t
  simp only [meanZeroDirichletPrimitive, dirichletPrimitive_add_one, Complex.ofReal_add,
    Complex.ofReal_one]
  ring

theorem meanZeroDirichletPrimitive_zero (N : ℕ) : meanZeroDirichletPrimitive N 0 = 0 := by
  simp [meanZeroDirichletPrimitive, dirichletPrimitive_zero]

theorem meanZeroDirichletPrimitive_one (N : ℕ) : meanZeroDirichletPrimitive N 1 = 0 := by
  simp [meanZeroDirichletPrimitive, dirichletPrimitive_one]

theorem hasDerivAt_meanZeroDirichletPrimitive (N : ℕ) (t : ℝ) :
    HasDerivAt (meanZeroDirichletPrimitive N) (dirichlet N t - 1) t := by
  exact (hasDerivAt_dirichletPrimitive N t).sub (hasDerivAt_id t).ofReal_comp

theorem continuous_meanZeroDirichletPrimitive (N : ℕ) :
    Continuous (meanZeroDirichletPrimitive N) := by
  exact continuous_iff_continuousAt.mpr
    (fun t => (hasDerivAt_meanZeroDirichletPrimitive N t).continuousAt)

/-- Both the frequency and the real coordinate are unrestricted in this bound. -/
theorem norm_meanZeroDirichletPrimitive_le (N : ℕ) (t : ℝ) :
    ‖meanZeroDirichletPrimitive N t‖ ≤ 5 / 2 := by
  obtain ⟨y, hy, hty⟩ := (meanZeroDirichletPrimitive_periodic N).exists_mem_Ico
    (by norm_num : (0 : ℝ) < 1) t (-1 / 2)
  have hyc : y ∈ Icc (-1 / 2 : ℝ) (1 / 2) := ⟨hy.1, by linarith [hy.2]⟩
  have habs : |y| ≤ 1 / 2 := abs_le.mpr ⟨by linarith [hyc.1], hyc.2⟩
  rw [hty, meanZeroDirichletPrimitive]
  calc
    ‖dirichletPrimitive N y - (y : ℂ)‖ ≤ ‖dirichletPrimitive N y‖ + ‖(y : ℂ)‖ := norm_sub_le _ _
    _ ≤ 2 + 1 / 2 := add_le_add (norm_dirichletPrimitive_center_le N ⟨y, hyc⟩)
      (by simpa only [Complex.norm_real, Real.norm_eq_abs] using habs)
    _ = 5 / 2 := by ring

end GaloisForLFunctions.HTGeometry.FourierLLogL.Period
