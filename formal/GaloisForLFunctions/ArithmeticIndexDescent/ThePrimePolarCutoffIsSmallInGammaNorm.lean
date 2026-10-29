import GaloisForLFunctions.ArithmeticCompensationTheory.ThePrimePolarCutoffHasUniformFrequencyBounds
import GaloisForLFunctions.ArithmeticIndexDescent.TheSquarePrimeBoundaryIsLowerOrder

/-!
# Prime–polar cancellation in the Gamma multiplier norm

The normalized literal cutoff multiplier tends to zero on every bounded
frequency interval and stays uniformly bounded on the full line. The Gamma
increment tends to infinity, so these estimates give a uniform bound relative
to one plus the original Gamma symbol.
-/

noncomputable section
open Filter Topology

namespace GaloisForLFunctions.ArithmeticIndexDescent
open ArithmeticCompensationTheory

/-- Both polar densities and all prime powers cancel uniformly relative to Gamma plus mass. -/
theorem eventually_primePolarCutoffSymbol_gamma_small {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ S : ℝ in atTop, 0 < S ∧ ∀ t : ℝ,
      |primePolarCutoffSymbol S t| ≤
        ε * Real.exp (S / 2) * (1 + gammaIncrementSymbol t) := by
  obtain ⟨T₀, hT₀, hgamma⟩ := exists_half_log_le_gammaIncrement
  let T := max T₀ (Real.exp (34 / ε))
  have hlarge (t : ℝ) (ht : T ≤ |t|) : 17 ≤ ε * gammaIncrementSymbol t := by
    have ht₀ : T₀ ≤ |t| := (le_max_left _ _).trans ht
    have hexp : Real.exp (34 / ε) ≤ |t| := (le_max_right _ _).trans ht
    have hlog := Real.log_le_log (Real.exp_pos (34 / ε)) hexp
    rw [Real.log_exp] at hlog
    have hg := hgamma t ht₀
    have hdiv : 17 / ε ≤ gammaIncrementSymbol t := by
      calc 17 / ε = (34 / ε) / 2 := by ring
        _ ≤ Real.log |t| / 2 := div_le_div_of_nonneg_right hlog (by norm_num)
        _ ≤ gammaIncrementSymbol t := hg
    simpa only [mul_comm] using (div_le_iff₀ hε).mp hdiv
  filter_upwards [eventually_primePolarCutoffSymbol_bounded_all_frequencies,
    eventually_primePolarCutoffSymbol_small_on_frequency_interval T hε] with S hbound hsmall
  refine ⟨hbound.1, fun t => ?_⟩
  rcases le_or_gt T |t| with ht | ht
  · calc _ ≤ 17 * Real.exp (S / 2) := hbound.2 t
      _ ≤ (ε * gammaIncrementSymbol t) * Real.exp (S / 2) :=
        mul_le_mul_of_nonneg_right (hlarge t ht) (Real.exp_pos _).le
      _ ≤ ε * Real.exp (S / 2) * (1 + gammaIncrementSymbol t) := by
        have hp : 0 ≤ ε * Real.exp (S / 2) := by positivity
        nlinarith only [hp]
  · calc _ ≤ ε * Real.exp (S / 2) := hsmall.2 t ht.le
      _ ≤ ε * Real.exp (S / 2) * (1 + gammaIncrementSymbol t) := by
        have hp := mul_nonneg (show 0 ≤ ε * Real.exp (S / 2) by positivity)
          (gammaIncrementSymbol_nonneg t)
        nlinarith only [hp]

end GaloisForLFunctions.ArithmeticIndexDescent
