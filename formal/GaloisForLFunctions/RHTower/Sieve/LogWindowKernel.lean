import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The exact kernel of a logarithmic short-interval sum

Write `S(u) = ∑_{u < log n ≤ u + δ} a_n`.  As a function of `u` each term is the indicator of the
window `[log n - δ, log n)`, so the mean square of `S` over the whole line is an exact quadratic form
in the coefficients:

    ∫_ℝ |S(u)|² du = ∑_{n,m} Re(a_n conj(a_m)) · (δ - |log n - log m|)₊ ,

the kernel being the overlap of two windows of common length `δ` — the triangular kernel in the
logarithmic variable.

The identity is elementary and exact: only the measure of the intersection of two half-open intervals
of equal length enters.  It is the first step of Gallagher's reduction of a short-interval mean
square to a Dirichlet polynomial, the second being the Fourier transform of that triangular kernel.
-/

namespace RHTower.Sieve

open MeasureTheory Finset

/-- The set of positions `u` for which `log n` lies in the window `(u, u + δ]`. -/
noncomputable def logWindow (δ : ℝ) (n : ℕ) : Set ℝ :=
  Set.Ico (Real.log n - δ) (Real.log n)

theorem measurableSet_logWindow (δ : ℝ) (n : ℕ) : MeasurableSet (logWindow δ n) :=
  measurableSet_Ico

theorem volume_logWindow_ne_top (δ : ℝ) (n : ℕ) : volume (logWindow δ n) ≠ ⊤ := by
  rw [logWindow, Real.volume_Ico]
  exact ENNReal.ofReal_ne_top

/-- The short-interval sum in the logarithmic variable. -/
noncomputable def logWindowSum (a : ℕ → ℂ) (s : Finset ℕ) (δ u : ℝ) : ℂ :=
  ∑ n ∈ s, (Set.indicator (logWindow δ n) (fun _ => (1 : ℝ)) u) • a n

/-- **The overlap of two windows of common length `δ`.**  Two half-open intervals of length `δ` meet
in a set of measure `(δ - |gap|)₊`. -/
theorem volume_real_logWindow_inter (δ : ℝ) (n m : ℕ) :
    volume.real (logWindow δ n ∩ logWindow δ m)
      = max (δ - |Real.log n - Real.log m|) 0 := by
  have hgap : min (Real.log n) (Real.log m) - (max (Real.log n) (Real.log m) - δ)
      = δ - |Real.log n - Real.log m| := by
    rcases le_total (Real.log n) (Real.log m) with h | h
    · rw [min_eq_left h, max_eq_right h, abs_of_nonpos (by linarith)]; ring
    · rw [min_eq_right h, max_eq_left h, abs_of_nonneg (by linarith)]; ring
  have hinter : logWindow δ n ∩ logWindow δ m
      = Set.Ico (max (Real.log n) (Real.log m) - δ) (min (Real.log n) (Real.log m)) := by
    rw [logWindow, logWindow, Set.Ico_inter_Ico]
    congr 1
    rcases le_total (Real.log n) (Real.log m) with h | h
    · rw [max_eq_right h, max_eq_right (by linarith : Real.log n - δ ≤ Real.log m - δ)]
    · rw [max_eq_left h, max_eq_left (by linarith : Real.log m - δ ≤ Real.log n - δ)]
  rw [hinter, measureReal_def, Real.volume_Ico, hgap]
  rcases le_total 0 (δ - |Real.log n - Real.log m|) with h | h
  · rw [ENNReal.toReal_ofReal h, max_eq_left h]
  · rw [ENNReal.ofReal_eq_zero.2 h, ENNReal.toReal_zero, max_eq_right h]

/-- The product of two window indicators is the indicator of the overlap. -/
theorem indicator_logWindow_mul (δ : ℝ) (n m : ℕ) (u : ℝ) :
    (Set.indicator (logWindow δ n) (fun _ => (1 : ℝ)) u)
        * (Set.indicator (logWindow δ m) (fun _ => (1 : ℝ)) u)
      = Set.indicator (logWindow δ n ∩ logWindow δ m) (fun _ => (1 : ℝ)) u := by
  by_cases hn : u ∈ logWindow δ n <;> by_cases hm : u ∈ logWindow δ m <;>
    simp [Set.indicator_of_mem, Set.indicator_of_notMem, hn, hm]

/-- The pointwise expansion of the mean square into the overlap kernel. -/
theorem normSq_logWindowSum (a : ℕ → ℂ) (s : Finset ℕ) (δ u : ℝ) :
    ‖logWindowSum a s δ u‖ ^ 2
      = ∑ n ∈ s, ∑ m ∈ s,
          (a n * (starRingEnd ℂ) (a m)).re
            * Set.indicator (logWindow δ n ∩ logWindow δ m) (fun _ => (1 : ℝ)) u := by
  have hz : ‖logWindowSum a s δ u‖ ^ 2
      = (logWindowSum a s δ u * (starRingEnd ℂ) (logWindowSum a s δ u)).re := by
    rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  rw [hz, logWindowSum, map_sum, Finset.sum_mul_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  have hconj : (starRingEnd ℂ)
      ((Set.indicator (logWindow δ m) (fun _ => (1 : ℝ)) u) • a m)
      = (Set.indicator (logWindow δ m) (fun _ => (1 : ℝ)) u) • (starRingEnd ℂ) (a m) := by
    rw [Complex.real_smul, Complex.real_smul, map_mul, Complex.conj_ofReal]
  rw [hconj, Complex.real_smul, Complex.real_smul,
    show ((Set.indicator (logWindow δ n) (fun _ => (1 : ℝ)) u : ℝ) : ℂ) * a n
        * (((Set.indicator (logWindow δ m) (fun _ => (1 : ℝ)) u : ℝ) : ℂ)
            * (starRingEnd ℂ) (a m))
      = (((Set.indicator (logWindow δ n) (fun _ => (1 : ℝ)) u
            * Set.indicator (logWindow δ m) (fun _ => (1 : ℝ)) u : ℝ)) : ℂ)
          * (a n * (starRingEnd ℂ) (a m)) by push_cast; ring,
    Complex.re_ofReal_mul, indicator_logWindow_mul]
  ring

/-- Each term of the expansion is integrable. -/
theorem integrable_indicator_logWindow_inter (δ : ℝ) (n m : ℕ) (c : ℝ) :
    Integrable (fun u : ℝ =>
      c * Set.indicator (logWindow δ n ∩ logWindow δ m) (fun _ => (1 : ℝ)) u) := by
  have hfin : volume (logWindow δ n ∩ logWindow δ m) ≠ ⊤ :=
    ne_top_of_le_ne_top (volume_logWindow_ne_top δ n) (measure_mono Set.inter_subset_left)
  have hmeas : MeasurableSet (logWindow δ n ∩ logWindow δ m) :=
    (measurableSet_logWindow δ n).inter (measurableSet_logWindow δ m)
  have hone : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (logWindow δ n ∩ logWindow δ m) :=
    integrableOn_const hfin (by simp)
  exact (hone.integrable_indicator hmeas).const_mul c

/-- **The mean square of a logarithmic short-interval sum is the triangular quadratic form.** -/
theorem integral_normSq_logWindowSum (a : ℕ → ℂ) (s : Finset ℕ) (δ : ℝ) :
    (∫ u : ℝ, ‖logWindowSum a s δ u‖ ^ 2)
      = ∑ n ∈ s, ∑ m ∈ s,
          (a n * (starRingEnd ℂ) (a m)).re * max (δ - |Real.log n - Real.log m|) 0 := by
  have hmeas : ∀ n m : ℕ, MeasurableSet (logWindow δ n ∩ logWindow δ m) := fun n m =>
    (measurableSet_logWindow δ n).inter (measurableSet_logWindow δ m)
  calc (∫ u : ℝ, ‖logWindowSum a s δ u‖ ^ 2)
      = ∫ u : ℝ, ∑ n ∈ s, ∑ m ∈ s,
          (a n * (starRingEnd ℂ) (a m)).re
            * Set.indicator (logWindow δ n ∩ logWindow δ m) (fun _ => (1 : ℝ)) u := by
        exact integral_congr_ae (Filter.Eventually.of_forall fun u => normSq_logWindowSum a s δ u)
    _ = ∑ n ∈ s, ∫ u : ℝ, ∑ m ∈ s,
          (a n * (starRingEnd ℂ) (a m)).re
            * Set.indicator (logWindow δ n ∩ logWindow δ m) (fun _ => (1 : ℝ)) u :=
        integral_finsetSum _ fun n _ =>
          integrable_finsetSum _ fun m _ => integrable_indicator_logWindow_inter δ n m _
    _ = ∑ n ∈ s, ∑ m ∈ s, ∫ u : ℝ,
          (a n * (starRingEnd ℂ) (a m)).re
            * Set.indicator (logWindow δ n ∩ logWindow δ m) (fun _ => (1 : ℝ)) u :=
        Finset.sum_congr rfl fun n _ =>
          integral_finsetSum _ fun m _ => integrable_indicator_logWindow_inter δ n m _
    _ = ∑ n ∈ s, ∑ m ∈ s,
          (a n * (starRingEnd ℂ) (a m)).re * max (δ - |Real.log n - Real.log m|) 0 := by
        refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => ?_
        rw [integral_const_mul, show (fun u : ℝ =>
            Set.indicator (logWindow δ n ∩ logWindow δ m) (fun _ => (1 : ℝ)) u)
            = Set.indicator (logWindow δ n ∩ logWindow δ m) 1 from rfl,
          integral_indicator_one (hmeas n m), volume_real_logWindow_inter]

end RHTower.Sieve
