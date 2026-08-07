import GaloisForLFunctions.RHTower.Sieve.HalaszLargeValueWindow
import GaloisForLFunctions.RHTower.Sieve.HalaszIntegralBound
import GaloisForLFunctions.RHTower.Sieve.EulerBoundLSeries
/-!
# The large-value window as a measurable set

The Halász dichotomy's exceptional set is `{t | (damped bound) < ‖L(f,σ+it)‖}`: a strict inequality between a
constant and a continuous function of the frequency, hence an open set.  Intersected with a bounded height range
it is measurable and of finite measure, and on its complement the damped bound holds *by definition* — the
far-frequency lemma is what makes the set small (inside `volume_halaszLargeValues_le`), not what bounds the series
off it.

These are the side conditions that the split of the three-factor inequality needs: a measurable set, finite
measure, and a bound on the third factor on each piece.
-/


noncomputable section
namespace RHTower.Sieve
open Complex MeasureTheory Set

/-- **The large-value set is open, hence measurable.**  Its defining inequality is a strict inequality between a
constant and a continuous function of the frequency. -/
theorem isOpen_halaszLargeValues {f : ℕ → ℂ} (hbdd : ∀ n, ‖f n‖ ≤ 1) {σ : ℝ} (hσ : 1 < σ) (c : ℝ) :
    IsOpen {t : ℝ | c < ‖∑' n : ℕ, twistedSummand f (((σ : ℝ) : ℂ) + ((t : ℝ) : ℂ) * I) n‖} := by
  have hcont : Continuous fun t : ℝ =>
      ‖∑' n : ℕ, twistedSummand f (((σ : ℝ) : ℂ) + ((t : ℝ) : ℂ) * I) n‖ :=
    (continuous_tsum_twistedSummand hbdd hσ).norm
  exact isOpen_lt continuous_const hcont

theorem measurableSet_halaszLargeValues {f : ℕ → ℂ} (hbdd : ∀ n, ‖f n‖ ≤ 1) {σ : ℝ} (hσ : 1 < σ)
    (c : ℝ) :
    MeasurableSet {t : ℝ | c < ‖∑' n : ℕ, twistedSummand f (((σ : ℝ) : ℂ) + ((t : ℝ) : ℂ) * I) n‖} :=
  (isOpen_halaszLargeValues hbdd hσ c).measurableSet

/-- A subset of a bounded interval has finite measure. -/
theorem volume_inter_Icc_ne_top (A : Set ℝ) (T : ℝ) : volume (A ∩ Set.Icc (-T) T) ≠ ⊤ := by
  refine ne_top_of_le_ne_top ?_ (measure_mono (Set.inter_subset_right))
  rw [Real.volume_Icc]
  exact ENNReal.ofReal_ne_top

/-- **The large-value window of the Halász dichotomy, as a measurable set of finite measure.**  Together with
`volume_halaszLargeValues_le` — which bounds its measure — and the definition of the set — which gives the damped
bound on its complement — this is what the split of the three-factor inequality consumes. -/
theorem measurableSet_and_finite_halaszWindow {f : ℕ → ℂ} (hbdd : ∀ n, ‖f n‖ ≤ 1) {σ : ℝ}
    (hσ : 1 < σ) (c T : ℝ) :
    MeasurableSet ({t : ℝ | c < ‖∑' n : ℕ, twistedSummand f (((σ : ℝ) : ℂ) + ((t : ℝ) : ℂ) * I) n‖}
        ∩ Set.Icc (-T) T)
      ∧ volume ({t : ℝ | c < ‖∑' n : ℕ,
            twistedSummand f (((σ : ℝ) : ℂ) + ((t : ℝ) : ℂ) * I) n‖} ∩ Set.Icc (-T) T) ≠ ⊤ :=
  ⟨(measurableSet_halaszLargeValues hbdd hσ c).inter measurableSet_Icc,
    volume_inter_Icc_ne_top _ T⟩

/-- **Off the large-value set the damped bound holds.**  By the definition of the set — no analytic input at the
point of use; the far-frequency lemma is what makes the set small, not what bounds the series off it. -/
theorem norm_tsum_twistedSummand_le_of_not_mem {f : ℕ → ℂ} {σ c : ℝ} {t : ℝ}
    (ht : t ∉ {t : ℝ | c < ‖∑' n : ℕ, twistedSummand f (((σ : ℝ) : ℂ) + ((t : ℝ) : ℂ) * I) n‖}) :
    ‖∑' n : ℕ, twistedSummand f (((σ : ℝ) : ℂ) + ((t : ℝ) : ℂ) * I) n‖ ≤ c := by
  rw [Set.mem_setOf_eq, not_lt] at ht
  exact ht

end RHTower.Sieve
end
