import GaloisForLFunctions.HTGeometry.LeafUniqueness
import GaloisForLFunctions.HTGeometry.LeafTightness

/-!
# What survives a weak limit

Two transfers, both already used in the construction with the *level* as the moving index, restated
with an arbitrary sequence of probability measures so that they can be run with the *parameter* as
the moving index:

* a weak limit of measures all representing the same sequence represents it;
* a weak limit of measures that eventually miss every compact subset of an open set misses that open
  set.
-/

open scoped BigOperators
open MeasureTheory Filter

namespace HTGeometry

variable {s : ℕ → ℝ}

/-- **Representing the sequence survives a weak limit.** -/
theorem hasHamburgerMoments_of_tendsto (h : PositiveMomentForm s) (h0 : s 0 = 1)
    {μs : ℕ → ProbabilityMeasure ℝ} {ν : ProbabilityMeasure ℝ}
    (hmom : ∀ n, GaloisForLFunctions.HTGeometry.HasHamburgerMoments s (μs n : Measure ℝ))
    (hlim : Tendsto μs atTop (nhds ν)) :
    GaloisForLFunctions.HTGeometry.HasHamburgerMoments s (ν : Measure ℝ) := by
  intro k
  have hopen : ∀ G, IsOpen G →
      (ν : Measure ℝ) G ≤ atTop.liminf fun i => (μs i : Measure ℝ) G :=
    fun G hG => ProbabilityMeasure.le_liminf_measure_open_of_tendsto hlim hG
  have hs2k : 0 < s (2 * k) := moment_even_pos h k
  have hlint : ∫⁻ x, ENNReal.ofReal (x ^ (2 * k)) ∂(ν : Measure ℝ)
      ≤ ENNReal.ofReal (s (2 * k)) := by
    refine lintegral_even_pow_le_of_forall_isOpen_le_liminf k hopen ?_
    refine Filter.Eventually.of_forall fun i => le_of_eq ?_
    have hnn : 0 ≤ᵐ[(μs i : Measure ℝ)] fun x : ℝ => x ^ (2 * k) :=
      Filter.Eventually.of_forall fun x => pow_two_mul_nonneg k x
    rw [← ofReal_integral_eq_lintegral_ofReal (hmom i (2 * k)).1 hnn, (hmom i (2 * k)).2]
  have hmeas : Measurable fun x : ℝ => x ^ (2 * k) := measurable_id.pow_const _
  have hnn : ∀ x : ℝ, 0 ≤ x ^ (2 * k) := pow_two_mul_nonneg k
  have hint2 : Integrable (fun x : ℝ => x ^ (2 * k)) (ν : Measure ℝ) :=
    integrable_of_lintegral_ofReal_lt_top hmeas hnn
      (lt_of_le_of_lt hlint (lt_top_iff_ne_top.mpr ENNReal.ofReal_ne_top))
  have hMmu : ∫ x, x ^ (2 * k) ∂(ν : Measure ℝ) ≤ s (2 * k) := by
    have := integral_le_toReal_of_lintegral_le hmeas hnn ENNReal.ofReal_ne_top hlint
    rwa [ENNReal.toReal_ofReal hs2k.le] at this
  have hintk : Integrable (fun x : ℝ => x ^ k) (ν : Measure ℝ) :=
    integrable_pow_of_integrable_even k hint2
  refine ⟨hintk, ?_⟩
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have hν : ∫ x : ℝ, x ^ 0 ∂(ν : Measure ℝ) = 1 := by simp
    rw [hν, h0]
  have hMnu : ∀ᶠ i in atTop, ∫ x, x ^ (2 * k) ∂(μs i : Measure ℝ) ≤ s (2 * k) :=
    Filter.Eventually.of_forall fun i => le_of_eq (hmom i (2 * k)).2
  have hmain := tendsto_integral_pow_of_uniform_even_moment
    (μ := (ν : Measure ℝ)) (νs := fun i => (μs i : Measure ℝ)) hk
    (fun f => ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hlim f)
    hMnu hMmu
    (fun i => (hmom i k).1)
    (fun i => (hmom i (2 * k)).1)
    (fun R hR i => integrable_truncPow hR k)
    hintk hint2
    (fun R hR => integrable_truncPow hR k)
  have hconst : (fun _ : ℕ => s k) =ᶠ[atTop] fun i => ∫ x, x ^ k ∂(μs i : Measure ℝ) :=
    Filter.Eventually.of_forall fun i => (hmom i k).2.symm
  exact tendsto_nhds_unique hmain (Tendsto.congr' hconst tendsto_const_nhds)

/-- **Missing an open set survives a weak limit.** -/
theorem measure_eq_zero_of_tendsto {μs : ℕ → ProbabilityMeasure ℝ} {ν : ProbabilityMeasure ℝ}
    (hlim : Tendsto μs atTop (nhds ν)) {U : Set ℝ} (hU : IsOpen U)
    (hzero : ∀ L : Set ℝ, IsCompact L → L ⊆ U → ∀ᶠ n in atTop, (μs n : Measure ℝ) L = 0) :
    (ν : Measure ℝ) U = 0 := by
  have hopen : ∀ G, IsOpen G →
      (ν : Measure ℝ) G ≤ atTop.liminf fun i => (μs i : Measure ℝ) G :=
    fun G hG => ProbabilityMeasure.le_liminf_measure_open_of_tendsto hlim hG
  refine measure_open_eq_zero_of_compacts _ hU ?_
  intro K hK hKU
  obtain ⟨L, hLc, hKL, hLU⟩ := exists_compact_between hK hU hKU
  have hint0 : ∀ᶠ n in atTop, (μs n : Measure ℝ) (interior L) = 0 := by
    filter_upwards [hzero L hLc hLU] with n hn
    exact le_antisymm (le_trans (measure_mono interior_subset) (le_of_eq hn)) zero_le
  have hlim0 : atTop.liminf (fun n => (μs n : Measure ℝ) (interior L)) = 0 := by
    rw [Filter.liminf_congr hint0, liminf_const]
  have hνint : (ν : Measure ℝ) (interior L) = 0 := by
    refine le_antisymm ?_ zero_le
    rw [← hlim0]
    exact hopen (interior L) isOpen_interior
  exact le_antisymm (le_trans (measure_mono hKL) (le_of_eq hνint)) zero_le

end HTGeometry
