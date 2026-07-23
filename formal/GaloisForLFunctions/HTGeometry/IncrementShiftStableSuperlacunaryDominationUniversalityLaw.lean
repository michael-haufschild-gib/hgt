import GaloisForLFunctions.HTGeometry.ShiftStableSuperlacunaryDominationUniversalityLaw
import GaloisForLFunctions.HTGeometry.SuperexponentialGrowth

/-!
# Increment-shift-stable superlacunary domination universality

A positive divergent-ratio magnitude has a successive-increment sequence with the same
divergent-ratio property.  The increment sequence itself tends to infinity.  Consequently every
fixed nonnegative safety margin may be removed from every successive gap without losing positivity,
ratio divergence, or exponential domination of any fixed polynomial scale.
-/

open Filter

namespace GaloisForLFunctions

/-- Successive gaps of an eventually positive divergent-ratio sequence tend to infinity. -/
theorem increments_tendsto_atTop_of_ratio_tendsto_atTop {b : ℕ → ℝ}
    (hpos : ∀ᶠ n in atTop, 0 < b n)
    (hratio : Tendsto (fun n => b (n + 1) / b n) atTop atTop) :
    Tendsto (fun n => b (n + 1) - b n) atTop atTop := by
  obtain ⟨hgapPos, hgapRatio⟩ := increments_ratio_tendsto_atTop hpos hratio
  have hquot :=
    tendsto_div_natCast_atTop_of_ratio_tendsto_atTop hgapPos hgapRatio
  refine tendsto_atTop_mono' atTop ?_ hquot
  filter_upwards [hgapPos, eventually_ge_atTop 1] with n hdn hn
  have hnReal : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnPos : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le zero_lt_one hnReal
  rw [div_le_iff₀ hnPos]
  nlinarith

/-- **Increment-shift-stable superlacunary domination universality law.**  Every fixed nonnegative
margin removed from the successive gaps preserves eventual positivity and divergent gap ratio, and
the exponential of the residual gap eventually dominates every fixed positive polynomial scale. -/
theorem incrementShiftStableSuperlacunaryDominationUniversality {b : ℕ → ℝ}
    (hpos : ∀ᶠ n in atTop, 0 < b n)
    (hratio : Tendsto (fun n => b (n + 1) / b n) atTop atTop)
    {c : ℝ} (hc : 0 ≤ c) :
    (∀ᶠ n in atTop, 0 < (b (n + 1) - b n) - c) ∧
      Tendsto
        (fun n =>
          ((b (n + 2) - b (n + 1)) - c) /
            ((b (n + 1) - b n) - c))
        atTop atTop ∧
      ∀ (A : ℝ), 0 < A → ∀ (C E R : ℕ), 0 < C →
        ∃ M₀ : ℕ, ∀ m ≥ M₀,
          A * ((C : ℝ) * ((m : ℝ) + 1)) ^ E <
            Real.exp (((b (m + 1) - b m) - c) / ((R : ℝ) + 1)) := by
  have hgap := increments_ratio_tendsto_atTop hpos hratio
  have hgapTop :=
    increments_tendsto_atTop_of_ratio_tendsto_atTop hpos hratio
  simpa only [Nat.add_assoc, Nat.reduceAdd] using
    (shiftStableSuperlacunaryDominationUniversality
      (b := fun n => b (n + 1) - b n) hgapTop hgap.2 hc)

end GaloisForLFunctions
