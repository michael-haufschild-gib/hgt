import GaloisForLFunctions.RHTower.Sieve.ProfileStepIntegralComparison

/-!
# The explicit prime-profile bound against `∫₀¹ g(t) dt/t`

Every ingredient of the prime-profile transfer is now available: the exact partition at the
exponents `j/m`, the step approximation of a Lipschitz profile, the small-prime head bound, and the
step-versus-integral comparison.  This file assembles them into one explicit finite inequality,

`|primeProfileSum g N − ∫₀¹ g(t) dt/t| ≤ (L/m)·Σ_j W_j + (C/m + C·c₁/log N)`
`  + Σ_j |g(j/m)|·|W_j − (log (j+1) − log j)| + (L/m)·log m + C/m`,

valid for every `m ≥ 1` and every `N ≥ 2` past the cutoff.  No limit is taken: each summand is a
finite quantity, and the third one is the only one that depends on `N` in an essential way — it is
exactly the deviation of the prime-window masses from their logarithmic limits.

A profile vanishing linearly at the origin (`|g t| ≤ C t`) makes `t ↦ g t / t` bounded, so the
integral through the origin exists and its head is `O(1/m)`.
-/

namespace RHTower.Sieve

open Finset intervalIntegral MeasureTheory
open scoped Topology

noncomputable section

/-! ## The profile quotient is integrable through the origin -/

theorem norm_profile_div_le {g : ℝ → ℝ} {C : ℝ}
    (hbd : ∀ t : ℝ, 0 ≤ t → |g t| ≤ C * t) {t : ℝ} (ht : 0 < t) :
    ‖g t / t‖ ≤ C := by
  have habs := hbd t ht.le
  rw [Real.norm_eq_abs, abs_div, abs_of_pos ht, div_le_iff₀ ht]
  exact habs

theorem integrableOn_profile_div {g : ℝ → ℝ} {C : ℝ} (hg : Continuous g)
    (hbd : ∀ t : ℝ, 0 ≤ t → |g t| ≤ C * t) (r : ℝ) :
    IntegrableOn (fun t => g t / t) (Set.Ioc 0 r) volume := by
  refine MeasureTheory.Measure.integrableOn_of_bounded
    (measure_Ioc_lt_top).ne ((hg.measurable.div measurable_id).aestronglyMeasurable)
    (M := C) ?_
  refine (ae_restrict_iff' measurableSet_Ioc).2 ?_
  filter_upwards [] with t ht
  exact norm_profile_div_le hbd ht.1

theorem intervalIntegrable_profile_div {g : ℝ → ℝ} {C : ℝ} (hg : Continuous g)
    (hbd : ∀ t : ℝ, 0 ≤ t → |g t| ≤ C * t) {r : ℝ} (hr : 0 ≤ r) :
    IntervalIntegrable (fun t => g t / t) volume 0 r := by
  rw [intervalIntegrable_iff, Set.uIoc_of_le hr]
  exact integrableOn_profile_div hg hbd r

/-- **The integral head is linear in the cutoff.** -/
theorem abs_integral_profile_head_le {g : ℝ → ℝ} {C : ℝ}
    (hbd : ∀ t : ℝ, 0 ≤ t → |g t| ≤ C * t) {r : ℝ} (hr : 0 ≤ r) :
    |∫ t in (0 : ℝ)..r, g t / t| ≤ C * r := by
  have hbound : ∀ x ∈ Set.uIoc (0 : ℝ) r, ‖g x / x‖ ≤ C := by
    intro x hx
    rw [Set.uIoc_of_le hr] at hx
    exact norm_profile_div_le hbd hx.1
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  rwa [Real.norm_eq_abs, sub_zero, abs_of_nonneg hr] at h

theorem integral_profile_split {g : ℝ → ℝ} {C : ℝ} (hg : Continuous g)
    (hbd : ∀ t : ℝ, 0 ≤ t → |g t| ≤ C * t) {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) :
    (∫ t in (0 : ℝ)..1, g t / t)
      = (∫ t in (0 : ℝ)..r, g t / t) + ∫ t in r..1, g t / t := by
  have h1 : IntervalIntegrable (fun t => g t / t) volume 0 r :=
    intervalIntegrable_profile_div hg hbd hr0.le
  have h2 : IntervalIntegrable (fun t => g t / t) volume r 1 :=
    intervalIntegrable_div_id hg hr0 hr1
  exact (intervalIntegral.integral_add_adjacent_intervals h1 h2).symm

/-! ## The explicit master bound -/

/-- **The explicit prime-profile bound.**  All five error sources are displayed: the step
approximation, the small-prime head, the window-mass deviations, the step-versus-integral
comparison, and the integral head. -/
theorem abs_primeProfileSum_sub_integral_le
    {g : ℝ → ℝ} {L C : ℝ} (hL : 0 ≤ L) (hC : 0 ≤ C)
    (hg : Continuous g) (hlip : ∀ s t : ℝ, |g s - g t| ≤ L * |s - t|)
    (hbd : ∀ t : ℝ, 0 ≤ t → |g t| ≤ C * t)
    {m N : ℕ} (hm : 1 ≤ m) (hN : 2 ≤ N)
    (hcut : (2 : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / (m : ℝ))) :
    |primeProfileSum g N - ∫ t in (0 : ℝ)..1, g t / t|
      ≤ L / m * (∑ j ∈ Finset.Ico 1 m, exponentWindowMass m N j)
        + (C * ((1 : ℝ) / m) + C * mertensFirstConst / Real.log N)
        + (∑ j ∈ Finset.Ico 1 m,
            |g ((j : ℝ) / m)| *
              |exponentWindowMass m N j - (Real.log ((j : ℝ) + 1) - Real.log j)|)
        + L / m * Real.log m
        + C * ((1 : ℝ) / m) := by
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hrpos : (0 : ℝ) < (1 : ℝ) / (m : ℝ) := by positivity
  have hr1 : (1 : ℝ) / (m : ℝ) ≤ 1 := by
    rw [div_le_one hmpos]
    exact_mod_cast hm
  set H : ℝ := ∑ p ∈ Nat.primesLE (exponentCutoff ((1 : ℝ) / m) N),
    g (Real.log p / Real.log N) / (p : ℝ) with hH
  set S : ℝ := ∑ j ∈ Finset.Ico 1 m, g ((j : ℝ) / m) * exponentWindowMass m N j with hS
  set T : ℝ := ∑ j ∈ Finset.Ico 1 m,
    g ((j : ℝ) / m) * (Real.log ((j : ℝ) + 1) - Real.log j) with hT
  -- the five estimates
  have e1 : |primeProfileSum g N - (H + S)|
      ≤ L / m * ∑ j ∈ Finset.Ico 1 m, exponentWindowMass m N j :=
    abs_primeProfileSum_sub_stepSum_le hL hlip hm hN
  have e2 : |H| ≤ C * ((1 : ℝ) / m) + C * mertensFirstConst / Real.log N :=
    abs_primeProfileSum_head_le' hC hrpos hbd hN hcut
  have e3 : |S - T| ≤ ∑ j ∈ Finset.Ico 1 m,
      |g ((j : ℝ) / m)| *
        |exponentWindowMass m N j - (Real.log ((j : ℝ) + 1) - Real.log j)| := by
    rw [hS, hT, ← Finset.sum_sub_distrib]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum ?_)
    intro j _
    rw [← mul_sub, abs_mul]
  have e4 : |T - ∫ t in ((1 : ℝ) / m)..1, g t / t| ≤ L / m * Real.log m :=
    abs_stepSum_sub_integral_le hL hg hlip hm
  have e5 : |∫ t in (0 : ℝ)..((1 : ℝ) / m), g t / t| ≤ C * ((1 : ℝ) / m) :=
    abs_integral_profile_head_le hbd hrpos.le
  have hsplit := integral_profile_split hg hbd hrpos hr1
  have hdecomp : primeProfileSum g N - ∫ t in (0 : ℝ)..1, g t / t
      = (primeProfileSum g N - (H + S)) + H + (S - T)
        + (T - ∫ t in ((1 : ℝ) / m)..1, g t / t)
        - (∫ t in (0 : ℝ)..((1 : ℝ) / m), g t / t) := by
    rw [hsplit]
    ring
  rw [hdecomp]
  calc |(primeProfileSum g N - (H + S)) + H + (S - T)
          + (T - ∫ t in ((1 : ℝ) / m)..1, g t / t)
          - (∫ t in (0 : ℝ)..((1 : ℝ) / m), g t / t)|
      ≤ |(primeProfileSum g N - (H + S)) + H + (S - T)
          + (T - ∫ t in ((1 : ℝ) / m)..1, g t / t)|
        + |∫ t in (0 : ℝ)..((1 : ℝ) / m), g t / t| := abs_sub _ _
    _ ≤ (|(primeProfileSum g N - (H + S)) + H + (S - T)|
          + |T - ∫ t in ((1 : ℝ) / m)..1, g t / t|)
        + |∫ t in (0 : ℝ)..((1 : ℝ) / m), g t / t| := by
        gcongr
        exact abs_add_le _ _
    _ ≤ ((|(primeProfileSum g N - (H + S)) + H| + |S - T|)
          + |T - ∫ t in ((1 : ℝ) / m)..1, g t / t|)
        + |∫ t in (0 : ℝ)..((1 : ℝ) / m), g t / t| := by
        gcongr
        exact abs_add_le _ _
    _ ≤ (((|primeProfileSum g N - (H + S)| + |H|) + |S - T|)
          + |T - ∫ t in ((1 : ℝ) / m)..1, g t / t|)
        + |∫ t in (0 : ℝ)..((1 : ℝ) / m), g t / t| := by
        gcongr
        exact abs_add_le _ _
    _ ≤ _ := by
        gcongr

end

end RHTower.Sieve
