import GaloisForLFunctions.HTGeometry.BirkhoffPointwise
import GaloisForLFunctions.HTGeometry.CountableTestFamily

/-!
# Generic sequences of a stationary ergodic process

A shift-ergodic probability law on sequences has a deterministic realization along which every
finite-block empirical average converges to the corresponding marginal expectation.  Birkhoff's
theorem gives a conull set of realizations for each observable; the countable test family reduces
the uncountable family of bounded continuous block observables to countably many conditions.
-/

open MeasureTheory Filter
open scoped Topology

namespace GaloisForLFunctions.HTGeometry

/-- The shift on real sequences. -/
def shiftSeq : (ℕ → ℝ) → (ℕ → ℝ) := fun ω n => ω (n + 1)

theorem measurable_shiftSeq : Measurable shiftSeq := by
  unfold shiftSeq
  fun_prop

theorem shiftSeq_iterate (j : ℕ) (ω : ℕ → ℝ) : shiftSeq^[j] ω = fun n => ω (j + n) := by
  induction j generalizing ω with
  | zero => simp
  | succ j ih =>
    funext n
    rw [Function.iterate_succ_apply, ih]
    simp only [shiftSeq]
    congr 1
    omega

/-- The first `k` coordinates of a sequence. -/
def blockMap (k : ℕ) : (ℕ → ℝ) → (Fin k → ℝ) := fun ω i => ω i

theorem measurable_blockMap (k : ℕ) : Measurable (blockMap k) := by
  unfold blockMap
  fun_prop

theorem blockMap_shiftSeq_iterate (k j : ℕ) (ω : ℕ → ℝ) :
    blockMap k (shiftSeq^[j] ω) = fun i : Fin k => ω (j + i) := by
  rw [shiftSeq_iterate]
  rfl

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Filter
open scoped Topology

variable {P : Measure (ℕ → ℝ)} [IsProbabilityMeasure P]

/-- Birkhoff's theorem for a bounded continuous block observable. -/
theorem ae_tendsto_block_average (hErg : Ergodic shiftSeq P) (k : ℕ) {ψ : (Fin k → ℝ) → ℝ}
    (hψc : Continuous ψ) {M : ℝ} (hψb : ∀ x, |ψ x| ≤ M) :
    ∀ᵐ ω ∂P, Tendsto
      (fun N : ℕ => (N : ℝ)⁻¹ * ∑ j ∈ Finset.range N, ψ (fun i : Fin k => ω (j + i)))
      atTop (𝓝 (∫ ω, ψ (blockMap k ω) ∂P)) := by
  have hfm : Measurable (fun ω => ψ (blockMap k ω)) :=
    hψc.measurable.comp (measurable_blockMap k)
  have hf : Integrable (fun ω => ψ (blockMap k ω)) P :=
    Integrable.mono' (integrable_const M) hfm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by simpa [Real.norm_eq_abs] using hψb (blockMap k ω))
  have hbirk := ae_tendsto_birkhoffAverage hErg measurable_shiftSeq hf hfm
  filter_upwards [hbirk] with ω hω
  refine hω.congr fun N => ?_
  simp only [birkhoffAverage, birkhoffSum, smul_eq_mul]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [blockMap_shiftSeq_iterate]

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Filter
open scoped Topology

variable {P : Measure (ℕ → ℝ)} [IsProbabilityMeasure P]

/-- Birkhoff's theorem for the first coordinate. -/
theorem ae_tendsto_coordinate_average (hErg : Ergodic shiftSeq P)
    (hint : Integrable (fun ω => ω 0) P) :
    ∀ᵐ ω ∂P, Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ j ∈ Finset.range N, ω j) atTop
      (𝓝 (∫ ω, ω 0 ∂P)) := by
  have hfm : Measurable (fun ω : ℕ → ℝ => ω 0) := measurable_pi_apply 0
  have hbirk := ae_tendsto_birkhoffAverage hErg measurable_shiftSeq hint hfm
  filter_upwards [hbirk] with ω hω
  refine hω.congr fun N => ?_
  simp only [birkhoffAverage, birkhoffSum, smul_eq_mul]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [shiftSeq_iterate]
  simp

/-- **A stationary ergodic law of mean one has a positive deterministic realization carrying every
finite-block empirical law.** -/
theorem exists_generic_sequence (hErg : Ergodic shiftSeq P)
    (hint : Integrable (fun ω => ω 0) P) (hmean : ∫ ω, ω 0 ∂P = 1)
    (hpos : ∀ᵐ ω ∂P, ∀ n, 0 < ω n) :
    ∃ g : ℕ → ℝ, (∀ j, 0 < g j) ∧
      Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ j ∈ Finset.range N, g j) atTop (𝓝 1) ∧
      ∀ (k : ℕ) (Φ : (Fin k → ℝ) → ℝ), Continuous Φ → (∃ M : ℝ, ∀ x, |Φ x| ≤ M) →
        Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ j ∈ Finset.range N, Φ (fun i : Fin k => g (j + i)))
          atTop (𝓝 (∫ ω, Φ (blockMap k ω) ∂P)) := by
  classical
  have hmeanae : ∀ᵐ ω ∂P,
      Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ j ∈ Finset.range N, ω j) atTop (𝓝 1) := by
    have h := ae_tendsto_coordinate_average hErg hint
    rwa [hmean] at h
  have htest : ∀ᵐ ω ∂P, ∀ k : ℕ, ∀ ψ ∈ testFamily (Fin k → ℝ),
      Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ j ∈ Finset.range N, ψ (fun i : Fin k => ω (j + i)))
        atTop (𝓝 (∫ ω, ψ (blockMap k ω) ∂P)) := by
    rw [ae_all_iff]
    intro k
    rw [ae_ball_iff countable_testFamily]
    intro ψ hψ
    obtain ⟨M, hM⟩ := exists_bound_of_mem_testFamily hψ
    exact ae_tendsto_block_average hErg k (continuous_of_mem_testFamily hψ) hM
  obtain ⟨g, hgpos, hgmean, hgtest⟩ := (hpos.and (hmeanae.and htest)).exists
  refine ⟨g, hgpos, hgmean, ?_⟩
  intro k Φ hΦc hΦb
  obtain ⟨M, hM⟩ := hΦb
  haveI : IsProbabilityMeasure (Measure.map (blockMap k) P) :=
    Measure.isProbabilityMeasure_map (measurable_blockMap k).aemeasurable
  have hmapint : ∀ ψ : (Fin k → ℝ) → ℝ, Continuous ψ →
      ∫ x, ψ x ∂(Measure.map (blockMap k) P) = ∫ ω, ψ (blockMap k ω) ∂P := by
    intro ψ hψ
    exact integral_map (measurable_blockMap k).aemeasurable hψ.aestronglyMeasurable
  have hfam : ∀ ψ ∈ testFamily (Fin k → ℝ),
      Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ j ∈ Finset.range N, ψ (fun i : Fin k => g (j + i)))
        atTop (𝓝 (∫ x, ψ x ∂(Measure.map (blockMap k) P))) := by
    intro ψ hψ
    rw [hmapint ψ (continuous_of_mem_testFamily hψ)]
    exact hgtest k ψ hψ
  have h := tendsto_average_of_testFamily (μ := Measure.map (blockMap k) P)
    (y := fun j : ℕ => fun i : Fin k => g (j + i)) hfam hΦc hM
  rwa [hmapint Φ hΦc] at h

end GaloisForLFunctions.HTGeometry
