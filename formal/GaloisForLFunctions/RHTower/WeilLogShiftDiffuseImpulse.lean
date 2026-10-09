import GaloisForLFunctions.RHTower.WeilLogShiftImpulseLineObstruction
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass

/-!
# Diffuse noise at one late observation

The native exceptional-amplitude set is subsingleton. Consequently every
measure vanishing on points assigns it measure zero. Almost every amplitude
has unbounded moment tails and signed nonsummability jointly at all real
shifts. This uses the exact impulse-fibre law, independently of category
arguments, and needs neither normalization nor sigma-finiteness.
-/

open Filter MeasureTheory Topology Real
open scoped BoundedContinuousFunction

namespace RHTower

open WeilExcess

/-- One threshold works for every bounded center and every diffuse amplitude
measure: the amplitudes failing global tail unboundedness have measure zero. -/
theorem exists_weilLogShiftRecoveryImpulse_exception_measure_zero :
    ∃ K : ℕ, ∀ (center : ℕ →ᵇ ℝ) (k : ℕ), K ≤ k →
      ∀ (μ : Measure ℝ) [NullSingletonClass μ],
        μ {t : ℝ | ¬ WeilLogShiftUniformNowhereBounded
          (weilLogShiftRecoveryImpulseHistory center k t)} = 0 := by
  obtain ⟨K, hK⟩ := exists_weilLogShiftRecoveryImpulse_exceptional_subsingleton
  refine ⟨K, ?_⟩
  intro center k hk μ hμ
  exact (hK center k hk).measure_zero μ

/-- Almost every diffuse impulse amplitude gives global tail unboundedness
and failure of signed summability at every real shift. -/
theorem exists_weilLogShiftRecoveryImpulse_ae_divergence :
    ∃ K : ℕ, ∀ (center : ℕ →ᵇ ℝ) (k : ℕ), K ≤ k →
      ∀ (μ : Measure ℝ) [NullSingletonClass μ], ∀ᵐ t ∂μ,
        WeilLogShiftUniformNowhereBounded (weilLogShiftRecoveryImpulseHistory center k t) ∧
        ∀ y : ℝ, ¬ Summable
          (weilLogShiftRecoveryMoment y (weilLogShiftRecoveryImpulseHistory center k t)) := by
  obtain ⟨K, hK⟩ := exists_weilLogShiftRecoveryImpulse_exception_measure_zero
  refine ⟨K, ?_⟩
  intro center k hk μ hμ
  have hgood : ∀ᵐ t ∂μ, WeilLogShiftUniformNowhereBounded
      (weilLogShiftRecoveryImpulseHistory center k t) := ae_iff.mpr (hK center k hk μ)
  filter_upwards [hgood] with t ht
  exact ⟨ht, weilLogShiftUniform_nowhere_summable_of_nowhere_bounded ht⟩

/-- Eventual boundedness or signed summability at even one real shift has
zero measure under every diffuse amplitude law on a native late impulse line. -/
theorem exists_weilLogShiftRecoveryImpulse_regular_exceptions_measure_zero :
    ∃ K : ℕ, ∀ (center : ℕ →ᵇ ℝ) (k : ℕ), K ≤ k →
      ∀ (μ : Measure ℝ) [NullSingletonClass μ],
        μ {t : ℝ | ∃ (y B : ℝ) (N : ℕ), ∀ n : ℕ, N ≤ n →
          ‖weilLogShiftRecoveryMoment y (weilLogShiftRecoveryImpulseHistory center k t) n‖ ≤ B} = 0 ∧
        μ {t : ℝ | ∃ y : ℝ, Summable
          (weilLogShiftRecoveryMoment y (weilLogShiftRecoveryImpulseHistory center k t))} = 0 := by
  obtain ⟨K, hK⟩ := exists_weilLogShiftRecoveryImpulse_exception_measure_zero
  refine ⟨K, ?_⟩
  intro center k hk μ hμ
  constructor
  · apply measure_mono_null ?_ (hK center k hk μ)
    rintro t ⟨y, B, N, hbound⟩ hgood
    obtain ⟨n, hn, hlarge⟩ := hgood y B N
    exact (not_lt_of_ge (hbound n hn)) hlarge
  · apply measure_mono_null ?_ (hK center k hk μ)
    rintro t ⟨y, hs⟩ hgood
    exact weilLogShiftUniform_nowhere_summable_of_nowhere_bounded hgood y hs

end RHTower
