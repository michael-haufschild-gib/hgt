import GaloisForLFunctions.RHTower.Sieve.SupportMeanSquare

/-!
# An affine mean-square majorant from a bound at one height

Gallagher's dyadic split consumes an affine majorant `∫_{|w| ≤ T}|A|² ≤ αT + β` valid for every
`T` above the cut.  A cancellation estimate, by contrast, is only available up to some height `T₀`,
because the analytic input degrades as the height grows.  The two are reconciled by the mean value
theorem: above `T₀` the trivial bound is already affine with the right slope, and below `T₀` the
integral is monotone in the height, so a single bound at `T₀` suffices.
-/

namespace RHTower.Sieve

open MeasureTheory

noncomputable section

/-- The mean square over a symmetric window is monotone in the window. -/
theorem integral_normSq_logPoly_mono (a : ℕ → ℂ) (s : Finset ℕ) {T T₀ : ℝ} (hTT : T ≤ T₀) :
    (∫ w in Set.Icc (-T) T, ‖logPoly a s w‖ ^ (2 : ℕ))
      ≤ ∫ w in Set.Icc (-T₀) T₀, ‖logPoly a s w‖ ^ (2 : ℕ) := by
  have hcont : Continuous fun w : ℝ => ‖logPoly a s w‖ ^ (2 : ℕ) :=
    ((continuous_logPoly a s).norm).pow 2
  have hsub : Set.Icc (-T) T ⊆ Set.Icc (-T₀) T₀ := by
    intro w hw
    rw [Set.mem_Icc] at hw ⊢
    constructor
    · linarith [hw.1]
    · linarith [hw.2]
  refine MeasureTheory.setIntegral_mono_set hcont.integrableOn_Icc ?_
    (Filter.Eventually.of_forall hsub)
  exact Filter.Eventually.of_forall fun w => by positivity

/-- **An affine majorant from a bound at one height.**  Below the height the integral is monotone;
above it the mean value theorem is already affine with slope the coefficient energy. -/
theorem affineMajorant_of_bound_at {a : ℕ → ℂ} {s : Finset ℕ} (hs0 : (0 : ℕ) ∉ s) {M : ℕ}
    (hsM : ∀ n ∈ s, n ≤ M) {W T₀ β₀ : ℝ} (hW : 1 ≤ W)
    (hbound : (∫ w in Set.Icc (-T₀) T₀, ‖logPoly a s w‖ ^ (2 : ℕ)) ≤ β₀) :
    ∀ T : ℝ, W ≤ T →
      (∫ w in Set.Icc (-T) T, ‖logPoly a s w‖ ^ (2 : ℕ))
        ≤ (5 * Real.pi / 2 * ∑ n ∈ s, ‖a n‖ ^ (2 : ℕ)) * T
          + (β₀ + 5 * Real.exp 1 / 2 * (M : ℝ) * ∑ n ∈ s, ‖a n‖ ^ (2 : ℕ)) := by
  intro T hT
  have hT1 : (1 : ℝ) ≤ T := le_trans hW hT
  have hT0 : (0 : ℝ) ≤ T := by linarith
  have hE0 : (0 : ℝ) ≤ ∑ n ∈ s, ‖a n‖ ^ (2 : ℕ) :=
    Finset.sum_nonneg fun n _ => by positivity
  have hM0 : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
  have hslope : (0 : ℝ) ≤ (5 * Real.pi / 2 * ∑ n ∈ s, ‖a n‖ ^ (2 : ℕ)) * T := by
    have : (0 : ℝ) ≤ 5 * Real.pi / 2 * ∑ n ∈ s, ‖a n‖ ^ (2 : ℕ) :=
      mul_nonneg (by positivity) hE0
    exact mul_nonneg this hT0
  have htail : (0 : ℝ) ≤ 5 * Real.exp 1 / 2 * (M : ℝ) * ∑ n ∈ s, ‖a n‖ ^ (2 : ℕ) := by
    have : (0 : ℝ) ≤ 5 * Real.exp 1 / 2 * (M : ℝ) := mul_nonneg (by positivity) hM0
    exact mul_nonneg this hE0
  rcases le_total T T₀ with hle | hge
  · have hmono := integral_normSq_logPoly_mono a s hle
    linarith [hmono, hbound, hslope]
  · have hmvt := integral_Icc_normSq_logPoly_le_energy a hs0 hsM hT1
    have hval : (5 * Real.pi / 2 * T + 5 * Real.exp 1 / 2 * (M : ℝ)) * ∑ n ∈ s, ‖a n‖ ^ (2 : ℕ)
        = (5 * Real.pi / 2 * ∑ n ∈ s, ‖a n‖ ^ (2 : ℕ)) * T
          + 5 * Real.exp 1 / 2 * (M : ℝ) * ∑ n ∈ s, ‖a n‖ ^ (2 : ℕ) := by ring
    rw [hval] at hmvt
    have hβ0 : (0 : ℝ) ≤ β₀ := by
      refine le_trans ?_ hbound
      refine MeasureTheory.setIntegral_nonneg measurableSet_Icc fun w _ => ?_
      positivity
    linarith [hmvt, hβ0]

end

end RHTower.Sieve
