import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.FixedOverlapPositivityIsSelectiveAgainstTheLiouvilleTwin
import GaloisForLFunctions.TransMetzlerWeilPositivity.EveryPoleFreeSignTwinBreaksAboveTheRobinEulerRatio

/-!
# Fixed-overlap positivity is selective against every cofinite flip

For the Liouville selector `φ*` and every fixed overlap `c` above its Robin–Euler threshold
(`< 1`), eventually in `N` the complete Weil matrix of `ζ` is positive definite, while every
pole-free sign gauge `ε` — completely multiplicative, `±1`, with bounded harmonic sums — has a
strictly negative complete form on an atomic family of the same width
(`liouvilleSelector_selective_of_signGauge`). Every cofinite flip (all primes outside a finite set
flipped; the Liouville twin is the empty set) is such a gauge
(`liouvilleSelector_selective_of_cofiniteFlip`): one profile at one bounded overlap separates `ζ`
from infinitely many twins, none of them a finite flip.
-/

noncomputable section

open MeasureTheory Filter Topology Finset

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory

open SpacingScaleHarmonicAnalysis TransMetzlerWeilPositivity RenormalizedArithmeticPotentialTheory
  ArithmeticElectrostatics ArithmeticCountingPositivity SelectiveMultiscaleArithmeticPositivity

/-- **Selectivity against every pole-free sign gauge** at every overlap above the Robin–Euler
threshold of the Liouville selector. -/
theorem liouvilleSelector_selective_of_signGauge {ε : ℕ → ℝ} (hε : IsSignGauge ε) {B : ℝ}
    (hB : ∀ M : ℕ, |gaugeHarmonicSum ε M| ≤ B) {c : ℝ}
    (hc : robinEulerThreshold liouvilleSelector < c) :
    ∀ᶠ N : ℕ in atTop,
      (∀ x : EuclideanSpace ℝ (PrimeHorizonIndex N), x ≠ 0 →
        0 < weilQuad (atomicTest N (primeHorizonExtension x) (atomDilate liouvilleSelector (c / N)))) ∧
      ∃ x : EuclideanSpace ℝ (PrimeHorizonIndex N),
        weilQuadTw (fun n => ε n * ArithmeticFunction.vonMangoldt n)
          (atomicTest N (primeHorizonExtension x) (atomDilate liouvilleSelector (c / N))) < 0 := by
  have hc0 : 0 < c := (robinEulerThreshold_pos _).trans hc
  have hM : 0 < ∫ u, liouvilleSelector u ^ 2 := by
    linarith [integral_liouvilleSelector_sq_ge]
  have hlim : Tendsto (fun N : ℕ => c / N * (N : ℝ)) atTop (𝓝 c) :=
    tendsto_const_nhds.congr' (by
      filter_upwards [eventually_ge_atTop 1] with N hN
      have : (N : ℝ) ≠ 0 := by positivity
      field_simp)
  have hneg := eventually_signGauge_weilQuadTw_neg_of_gt_robinEuler hε hB
    contDiff_liouvilleSelector (fun _ hu => liouvilleSelector_eq_zero hu) hM
    robinEulerThreshold_liouvilleSelector_lt_one hc (w := fun N : ℕ => c / N)
    (by filter_upwards [eventually_ge_atTop 1] with N hN; positivity) hlim
  filter_upwards [liouvilleSelector_selective hc, hneg] with N hN hL
  obtain ⟨y, hy⟩ := hL
  exact ⟨hN.1, WithLp.toLp 2 (fun n : PrimeHorizonIndex N => y n),
    by rwa [atomicTest_restrict] at hy⟩

/-- **Selectivity against every cofinite flip** at every overlap `c ≥ 1`. -/
theorem liouvilleSelector_selective_of_cofiniteFlip {F : Finset ℕ} (hF : ∀ p ∈ F, p.Prime)
    {c : ℝ} (hc : 1 ≤ c) :
    ∀ᶠ N : ℕ in atTop,
      (∀ x : EuclideanSpace ℝ (PrimeHorizonIndex N), x ≠ 0 →
        0 < weilQuad (atomicTest N (primeHorizonExtension x) (atomDilate liouvilleSelector (c / N)))) ∧
      ∃ x : EuclideanSpace ℝ (PrimeHorizonIndex N),
        weilQuadTw (fun n => cofiniteFlip F n * ArithmeticFunction.vonMangoldt n)
          (atomicTest N (primeHorizonExtension x) (atomDilate liouvilleSelector (c / N))) < 0 :=
  liouvilleSelector_selective_of_signGauge (cofiniteFlip_isSignGauge F)
    (cofiniteFlip_harmonicSum_abs_le hF)
    (robinEulerThreshold_liouvilleSelector_lt_one.trans_le hc)

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory
