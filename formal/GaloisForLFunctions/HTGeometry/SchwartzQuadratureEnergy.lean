import GaloisForLFunctions.HTGeometry.SchwartzOscillatorAlgebra
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Energy quadrature with arbitrary sample positions

On each interval the error between the energy integral and its sampled value
is controlled by interval length times the local derivative cross integral.
The sample may lie anywhere in the interval. Smoothness and integrability
follow from the Schwartz structure; no analytic premise is required.
-/

open scoped SchwartzMap RealInnerProductSpace NNReal
open MeasureTheory intervalIntegral
noncomputable section

namespace GaloisForLFunctions

/-- Squared norm oscillation is bounded by the local derivative cross integral. -/
theorem schwartzEnergy_interval_oscillation (f : SchwartzMap ℝ ℂ) (a : ℝ) (h : ℝ≥0)
    (x y : Set.Icc a (a + (h : ℝ))) :
    |‖f x‖ ^ 2 - ‖f y‖ ^ 2| ≤
      ∫ u in a..a + (h : ℝ), 2 * (‖f u‖ * ‖derivSCLM f u‖) := by
  let g' : ℝ → ℝ := fun u => 2 * inner ℝ (f u) (derivSCLM f u)
  have hg' : Continuous g' := by dsimp [g']; fun_prop
  have hcross : Continuous (fun u : ℝ => 2 * (‖f u‖ * ‖derivSCLM f u‖)) := by fun_prop
  have hderiv (u : ℝ) : HasDerivAt (fun v : ℝ => ‖f v‖ ^ 2) (g' u) u := by
    simpa only [g', derivSCLM_apply] using (f.hasDerivAt u).norm_sq
  have habs (u : ℝ) : |g' u| ≤ 2 * (‖f u‖ * ‖derivSCLM f u‖) := by
    dsimp [g']
    rw [abs_mul, abs_two]
    exact mul_le_mul_of_nonneg_left (abs_real_inner_le_norm (f u) (derivSCLM f u))
      (by positivity)
  have hftc : (∫ u in (y : ℝ)..(x : ℝ), g' u) = ‖f x‖ ^ 2 - ‖f y‖ ^ 2 :=
    integral_eq_sub_of_hasDerivAt (fun u _ => hderiv u) (hg'.intervalIntegrable _ _)
  rw [← hftc]
  have hsub : |∫ u in (y : ℝ)..(x : ℝ), g' u| ≤
      ∫ u in a..a + (h : ℝ), |g' u| := by
    rcases le_total (y : ℝ) (x : ℝ) with hyx | hxy
    · exact (abs_integral_le_integral_abs hyx).trans
        (integral_mono_interval y.property.1 hyx x.property.2
          (Filter.Eventually.of_forall fun _ => abs_nonneg _)
          (hg'.abs.intervalIntegrable _ _))
    · rw [integral_symm, abs_neg]
      exact (abs_integral_le_integral_abs hxy).trans
        (integral_mono_interval x.property.1 hxy y.property.2
          (Filter.Eventually.of_forall fun _ => abs_nonneg _)
          (hg'.abs.intervalIntegrable _ _))
  exact hsub.trans (integral_mono_on (le_add_of_nonneg_right h.coe_nonneg)
    (hg'.abs.intervalIntegrable _ _) (hcross.intervalIntegrable _ _)
    (fun u _ => habs u))

/-- An arbitrary sample in a cell approximates its full energy with a local cross-term bound. -/
theorem schwartzEnergy_interval_quadrature_error (f : SchwartzMap ℝ ℂ) (a : ℝ) (h : ℝ≥0)
    (x : Set.Icc a (a + (h : ℝ))) :
    |(∫ u in a..a + (h : ℝ), ‖f u‖ ^ 2) - (h : ℝ) * ‖f x‖ ^ 2| ≤
      (h : ℝ) * (∫ u in a..a + (h : ℝ), 2 * (‖f u‖ * ‖derivSCLM f u‖)) := by
  let J := ∫ u in a..a + (h : ℝ), 2 * (‖f u‖ * ‖derivSCLM f u‖)
  have hc : Continuous (fun u : ℝ => ‖f u‖ ^ (2 : ℕ)) := by fun_prop
  have hp (u : ℝ) (hu : u ∈ Set.Icc a (a + (h : ℝ))) :
      |‖f u‖ ^ 2 - ‖f x‖ ^ 2| ≤ J :=
    schwartzEnergy_interval_oscillation f a h ⟨u, hu⟩ x
  have hlow := integral_mono_on (μ := (volume : Measure ℝ))
    (le_add_of_nonneg_right h.coe_nonneg : a ≤ a + (h : ℝ))
    (f := fun _ : ℝ => ‖f x‖ ^ 2 - J) (g := fun u : ℝ => ‖f u‖ ^ 2)
    intervalIntegrable_const (hc.intervalIntegrable _ _)
    (fun u hu => by have ht := (abs_le.mp (hp u hu)).1; linarith only [ht])
  have hupp := integral_mono_on (μ := (volume : Measure ℝ))
    (le_add_of_nonneg_right h.coe_nonneg : a ≤ a + (h : ℝ))
    (f := fun u : ℝ => ‖f u‖ ^ 2) (g := fun _ : ℝ => ‖f x‖ ^ 2 + J)
    (hc.intervalIntegrable _ _) intervalIntegrable_const
    (fun u hu => by have ht := (abs_le.mp (hp u hu)).2; linarith only [ht])
  rw [intervalIntegral.integral_const] at hlow hupp
  simp only [add_sub_cancel_left, smul_eq_mul] at hlow hupp
  apply abs_le.mpr
  constructor <;> nlinarith only [hlow, hupp]

/-- Summing adjacent cells preserves the local cross integral without a cell-count loss. -/
theorem schwartzEnergy_grid_quadrature_error (f : SchwartzMap ℝ ℂ) (a : ℝ) (h : ℝ≥0)
    (s : ℕ → Set.Icc (0 : ℝ) 1) (N : ℕ) :
    |(∫ u in a..a + (N : ℝ) * h, ‖f u‖ ^ 2) -
        (h : ℝ) * ∑ j ∈ Finset.range N, ‖f (a + ((j : ℝ) + (s j : ℝ)) * h)‖ ^ 2| ≤
      (h : ℝ) * (∫ u in a..a + (N : ℝ) * h, 2 * (‖f u‖ * ‖derivSCLM f u‖)) := by
  let A : ℕ → ℝ := fun j => a + (j : ℝ) * h
  have hstep (j : ℕ) : A j + h = A (j + 1) := by dsimp [A]; push_cast; ring
  have hzero : A 0 = a := by simp [A]
  have htel (F : ℝ → ℝ) (hF : Continuous F) :
      (∑ j ∈ Finset.range N, ∫ u in A j..A j + (h : ℝ), F u) =
        ∫ u in a..a + (N : ℝ) * h, F u := by
    simp_rw [hstep]
    rw [sum_integral_adjacent_intervals (fun j _ => hF.intervalIntegrable (A j) (A (j + 1)))]
    rw [hzero]
  have hcell (j : ℕ) :
      |(∫ u in A j..A j + (h : ℝ), ‖f u‖ ^ 2) -
          (h : ℝ) * ‖f (a + ((j : ℝ) + (s j : ℝ)) * h)‖ ^ 2| ≤
        (h : ℝ) * (∫ u in A j..A j + (h : ℝ), 2 * (‖f u‖ * ‖derivSCLM f u‖)) := by
    have hx : a + ((j : ℝ) + (s j : ℝ)) * h ∈ Set.Icc (A j) (A j + (h : ℝ)) := by
      dsimp [A]
      rw [show a + ((j : ℝ) + (s j : ℝ)) * h =
        (a + (j : ℝ) * h) + (s j : ℝ) * h by ring]
      constructor
      · exact le_add_of_nonneg_right (mul_nonneg (s j).property.1 h.coe_nonneg)
      · apply add_le_add le_rfl
        simpa only [one_mul] using mul_le_mul_of_nonneg_right (s j).property.2 h.coe_nonneg
    exact schwartzEnergy_interval_quadrature_error f (A j) h ⟨_, hx⟩
  rw [← htel (fun u => ‖f u‖ ^ (2 : ℕ)) (by fun_prop), Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ j ∈ Finset.range N,
        |(∫ u in A j..A j + (h : ℝ), ‖f u‖ ^ 2) -
          (h : ℝ) * ‖f (a + ((j : ℝ) + (s j : ℝ)) * h)‖ ^ 2| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range N,
        (h : ℝ) * (∫ u in A j..A j + (h : ℝ), 2 * (‖f u‖ * ‖derivSCLM f u‖)) :=
      Finset.sum_le_sum fun j _ => hcell j
    _ = _ := by rw [← Finset.mul_sum, htel _ (by fun_prop)]

end GaloisForLFunctions
