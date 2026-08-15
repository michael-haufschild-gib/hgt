import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# The canonical smooth transition has bounded derivative

`Real.smoothTransition` is smooth, vanishes on `(-∞,0]` and is one on `[1,∞)`, so its derivative is
continuous and vanishes off the unit interval.  Compactness of `[0,1]` therefore bounds it globally.

This is the uniform constant that every cutoff built from a fixed transition inherits: a cutoff of
the form `ϑ(A(L))` has `|d/dL ϑ(A(L))| ≤ Λ·sup|A'|`, with `Λ` independent of the coordinate.
-/

open Set

noncomputable section

namespace GaloisForLFunctions.HTGeometry

theorem continuous_deriv_smoothTransition : Continuous (deriv Real.smoothTransition) :=
  ContDiff.continuous_deriv (Real.smoothTransition.contDiff (n := 2)) (by norm_num)

/-- The transition is locally constant off the unit interval, so its derivative vanishes there. -/
theorem deriv_smoothTransition_eq_zero_of_notMem {x : ℝ} (hx : x ∉ Icc (0 : ℝ) 1) :
    deriv Real.smoothTransition x = 0 := by
  simp only [mem_Icc, not_and_or, not_le] at hx
  rcases hx with hx | hx
  · have hnhds : Real.smoothTransition =ᶠ[nhds x] fun _ => (0 : ℝ) := by
      filter_upwards [Iio_mem_nhds hx] with y hy
      exact Real.smoothTransition.zero_of_nonpos (le_of_lt hy)
    rw [Filter.EventuallyEq.deriv_eq hnhds, deriv_const]
  · have hnhds : Real.smoothTransition =ᶠ[nhds x] fun _ => (1 : ℝ) := by
      filter_upwards [Ioi_mem_nhds hx] with y hy
      exact Real.smoothTransition.one_of_one_le (le_of_lt hy)
    rw [Filter.EventuallyEq.deriv_eq hnhds, deriv_const]

/-- **The canonical transition has a uniform derivative bound.** -/
theorem exists_bound_deriv_smoothTransition :
    ∃ Λ : ℝ, 0 ≤ Λ ∧ ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ Λ := by
  have hcont : ContinuousOn (fun x => |deriv Real.smoothTransition x|) (Icc (0 : ℝ) 1) :=
    (continuous_abs.comp continuous_deriv_smoothTransition).continuousOn
  obtain ⟨x₀, hx₀, hmax⟩ :=
    (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_isMaxOn ⟨0, by norm_num⟩ hcont
  refine ⟨|deriv Real.smoothTransition x₀|, abs_nonneg _, fun x => ?_⟩
  by_cases hx : x ∈ Icc (0 : ℝ) 1
  · exact hmax hx
  · rw [deriv_smoothTransition_eq_zero_of_notMem hx, abs_zero]
    exact abs_nonneg _

/-- **The chain rule bound for a transition cutoff.**  A cutoff obtained by composing the canonical
transition with a coordinate of bounded derivative has uniformly bounded derivative. -/
theorem abs_deriv_smoothTransition_comp_le {A : ℝ → ℝ} {A' M Λ : ℝ} {L : ℝ}
    (hΛ : ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ Λ)
    (hA : HasDerivAt A A' L) (hM : |A'| ≤ M) :
    |deriv (fun t => Real.smoothTransition (A t)) L| ≤ Λ * M := by
  have hdiff : HasDerivAt Real.smoothTransition (deriv Real.smoothTransition (A L)) (A L) :=
    (Real.smoothTransition.contDiff (n := 1)).differentiable (by norm_num) |>.differentiableAt
      |>.hasDerivAt
  have hcomp : HasDerivAt (fun t => Real.smoothTransition (A t))
      (deriv Real.smoothTransition (A L) * A') L := hdiff.comp L hA
  rw [hcomp.deriv, abs_mul]
  exact mul_le_mul (hΛ (A L)) hM (abs_nonneg _)
    (le_trans (abs_nonneg _) (hΛ (A L)))

end GaloisForLFunctions.HTGeometry
