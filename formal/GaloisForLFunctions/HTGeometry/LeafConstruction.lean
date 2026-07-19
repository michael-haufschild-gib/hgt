import GaloisForLFunctions.HTGeometry.QuasiLevelFamily
import GaloisForLFunctions.HTGeometry.DenominatorAvoidance

/-!
# The N-extremal leaf of a parameter

Running the quasi-orthogonal construction along the levels where the denominator has full degree
produces a probability measure with the right moments, and the avoidance estimate confines it to the
zero set of the limiting denominator.

Carriedness is obtained on compact sets and then spread by inner regularity: a compact subset of the
complement sits inside the interior of a larger compact subset, the approximating measures give that
larger set no mass eventually, and the portmanteau inequality for open sets transfers this to the
limit.
-/

open scoped BigOperators
open MeasureTheory Filter

namespace HTGeometry

variable {s : ℕ → ℝ}

/-- The complement of the limiting denominator's zero set is open. -/
theorem isOpen_denominator_ne_zero (h : PositiveMomentForm s) (h0b : BoundedKernel s 0)
    (tau : ℝ) : IsOpen {x : ℝ | nevBrealInf s x * tau - nevDrealInf s x ≠ 0} := by
  have hcont : Continuous fun x : ℝ => nevBrealInf s x * tau - nevDrealInf s x :=
    ((continuous_nevBrealInf h h0b).mul continuous_const).sub (continuous_nevDrealInf h h0b)
  exact isOpen_ne_fun hcont continuous_const

/-- **The leaf of a parameter.**  A probability measure representing the normalised moment sequence
and carried by the zero set of `B·τ − D`. -/
theorem exists_leaf (h : PositiveMomentForm s) (h0b : BoundedKernel s 0) (tau : ℝ) :
    ∃ μ : ProbabilityMeasure ℝ,
      (∀ k : ℕ, Integrable (fun x : ℝ => x ^ k) (μ : Measure ℝ) ∧
        ∫ x, x ^ k ∂(μ : Measure ℝ) = (s 0)⁻¹ * s k) ∧
      (μ : Measure ℝ) {x : ℝ | nevBrealInf s x * tau - nevDrealInf s x ≠ 0} = 0 := by
  classical
  set ν : ℕ → ℕ := goodLevel h tau with hνdef
  have hν : ∀ n, n + 1 ≤ ν n := goodLevel_ge h tau
  set τ' : ℕ → ℝ := leafParam h tau with hτdef
  obtain ⟨μ, φ, hφ, hlim⟩ := exists_subseq_tendsto_quasiProbMeasure_of_level h ν hν τ'
  have hopen : ∀ G, IsOpen G →
      (μ : Measure ℝ) G ≤ atTop.liminf fun i => quasiProb s (ν (φ i)) (τ' (φ i)) G :=
    fun G hG => ProbabilityMeasure.le_liminf_measure_open_of_tendsto hlim hG
  refine ⟨μ, fun k => hasMoments_of_tendsto_quasi_of_level h ν hν τ' hφ hopen hlim k, ?_⟩
  -- carriedness
  refine measure_open_eq_zero_of_compacts _ (isOpen_denominator_ne_zero h h0b tau) ?_
  intro K hK hKU
  obtain ⟨L, hLc, hKL, hLU⟩ :=
    exists_compact_between hK (isOpen_denominator_ne_zero h h0b tau) hKU
  have hLF : ∀ x ∈ L, nevBrealInf s x * tau - nevDrealInf s x ≠ 0 := fun x hx => hLU hx
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp
    (eventually_quasiMeasure_compact_eq_zero h h0b tau hLc hLF)
  have hzero : ∀ᶠ i in atTop, quasiProb s (ν (φ i)) (τ' (φ i)) (interior L) = 0 := by
    refine Filter.eventually_atTop.mpr ⟨N₀, fun i hi => ?_⟩
    have hgrow : N₀ ≤ ν (φ i) := by
      have h1 : i ≤ φ i := hφ.le_apply
      have h2 : φ i + 1 ≤ ν (φ i) := hν (φ i)
      omega
    have hmzero : quasiMeasure s (ν (φ i)) (τ' (φ i)) L = 0 :=
      hN₀ (ν (φ i)) hgrow (goodLevel_nevAlpha_ne_zero h tau (φ i))
    have hle : quasiProb s (ν (φ i)) (τ' (φ i)) (interior L) = 0 := by
      rw [quasiProb, Measure.smul_apply, smul_eq_mul]
      have hsub : quasiMeasure s (ν (φ i)) (τ' (φ i)) (interior L) = 0 :=
        le_antisymm (le_trans (measure_mono interior_subset) (le_of_eq hmzero)) zero_le
      rw [hsub, mul_zero]
    exact hle
  have hlim0 : atTop.liminf (fun i => quasiProb s (ν (φ i)) (τ' (φ i)) (interior L)) = 0 := by
    rw [Filter.liminf_congr hzero, liminf_const]
  have hint : (μ : Measure ℝ) (interior L) = 0 := by
    refine le_antisymm ?_ zero_le
    rw [← hlim0]
    exact hopen (interior L) isOpen_interior
  exact le_antisymm (le_trans (measure_mono hKL) (le_of_eq hint)) zero_le

end HTGeometry
