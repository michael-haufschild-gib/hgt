import GaloisForLFunctions.HTGeometry.InfinityDenominator
import GaloisForLFunctions.HTGeometry.QuasiLevelFamily
import GaloisForLFunctions.HTGeometry.DenominatorAvoidance

/-!
# The leaf at infinity

The parameter at infinity has denominator `B`, and `InfinityDenominator` puts it in the same
quasi-orthogonal form as the finite parameters, with the same Wronskian non-degeneracy and the same
cofinality of good levels.  So the construction of `LeafConstruction` runs unchanged.
-/

open scoped BigOperators
open MeasureTheory Filter

namespace HTGeometry

variable {s : ℕ → ℝ}

/-- **`Bₙ` eventually has no zero on a compact set where `B` has none.** -/
theorem eventually_no_nevBreal_zero_on_compact (h : PositiveMomentForm s)
    (h0b : BoundedKernel s 0) {K : Set ℝ} (hK : IsCompact K)
    (hKF : ∀ x ∈ K, nevBrealInf s x ≠ 0) :
    ∀ᶠ n in atTop, ∀ x ∈ K, nevBreal s n x ≠ 0 := by
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · exact Filter.Eventually.of_forall fun n x hx => absurd hx (Set.notMem_empty x)
  have hcont : Continuous fun x : ℝ => |nevBrealInf s x| := (continuous_nevBrealInf h h0b).abs
  obtain ⟨x₀, hx₀K, hmin⟩ := hK.exists_isMinOn hKne hcont.continuousOn
  set δ : ℝ := |nevBrealInf s x₀| with hδdef
  have hδ : 0 < δ := abs_pos.mpr (hKF x₀ hx₀K)
  obtain ⟨r, hr, hKr⟩ := exists_radius_of_isCompact hK hKne
  obtain ⟨S, P, hSpos, hPpos, hS, hP⟩ := h0b
  filter_upwards [eventually_nevBreal_close h hS hP hr (half_pos hδ)] with n hn x hx
  intro hzero
  have h1 := hn x (hKr x hx)
  rw [hzero, zero_sub, abs_neg] at h1
  have h2 : δ ≤ |nevBrealInf s x| := hmin hx
  linarith

/-- **The quasi measure eventually gives such a compact set zero mass.** -/
theorem eventually_quasiMeasure_compact_eq_zero_inf (h : PositiveMomentForm s)
    (h0b : BoundedKernel s 0) {K : Set ℝ} (hK : IsCompact K)
    (hKF : ∀ x ∈ K, nevBrealInf s x ≠ 0) :
    ∀ᶠ n in atTop, nevAlphaInf s n ≠ 0 →
      quasiMeasure s n (nevBetaInf s n / nevAlphaInf s n) K = 0 := by
  classical
  filter_upwards [eventually_no_nevBreal_zero_on_compact h h0b hK hKF] with n hn hα
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  rw [quasiMeasure, finsetWeightedDirac_apply _ _ hKm]
  refine Finset.sum_eq_zero fun ξ hξ => ?_
  have hnot : ξ ∉ K := fun hc => hn ξ hc ((nevBreal_zero_iff h n hα ξ).mpr hξ)
  rw [Set.indicator_of_notMem hnot, mul_zero]

/-! ## Selecting the good levels -/

/-- A level above `n` at which `B` has full degree. -/
noncomputable def goodLevelInf (h : PositiveMomentForm s) (n : ℕ) : ℕ :=
  (exists_ge_nevAlphaInf_ne_zero h (n + 1)).choose

theorem goodLevelInf_ge (h : PositiveMomentForm s) (n : ℕ) : n + 1 ≤ goodLevelInf h n :=
  (exists_ge_nevAlphaInf_ne_zero h (n + 1)).choose_spec.1

theorem goodLevelInf_nevAlphaInf_ne_zero (h : PositiveMomentForm s) (n : ℕ) :
    nevAlphaInf s (goodLevelInf h n) ≠ 0 :=
  (exists_ge_nevAlphaInf_ne_zero h (n + 1)).choose_spec.2

/-- The quasi parameter selecting the level-`goodLevelInf n` denominator. -/
noncomputable def leafParamInf (h : PositiveMomentForm s) (n : ℕ) : ℝ :=
  nevBetaInf s (goodLevelInf h n) / nevAlphaInf s (goodLevelInf h n)

/-- The complement of `B`'s zero set is open. -/
theorem isOpen_nevBrealInf_ne_zero (h : PositiveMomentForm s) (h0b : BoundedKernel s 0) :
    IsOpen {x : ℝ | nevBrealInf s x ≠ 0} :=
  isOpen_ne_fun (continuous_nevBrealInf h h0b) continuous_const

/-- **The leaf at infinity.** -/
theorem exists_leaf_infinity (h : PositiveMomentForm s) (h0b : BoundedKernel s 0) :
    ∃ μ : ProbabilityMeasure ℝ,
      (∀ k : ℕ, Integrable (fun x : ℝ => x ^ k) (μ : Measure ℝ) ∧
        ∫ x, x ^ k ∂(μ : Measure ℝ) = (s 0)⁻¹ * s k) ∧
      (μ : Measure ℝ) {x : ℝ | nevBrealInf s x ≠ 0} = 0 := by
  classical
  set ν : ℕ → ℕ := goodLevelInf h with hνdef
  have hν : ∀ n, n + 1 ≤ ν n := goodLevelInf_ge h
  set τ' : ℕ → ℝ := leafParamInf h with hτdef
  obtain ⟨μ, φ, hφ, hlim⟩ := exists_subseq_tendsto_quasiProbMeasure_of_level h ν hν τ'
  have hopen : ∀ G, IsOpen G →
      (μ : Measure ℝ) G ≤ atTop.liminf fun i => quasiProb s (ν (φ i)) (τ' (φ i)) G :=
    fun G hG => ProbabilityMeasure.le_liminf_measure_open_of_tendsto hlim hG
  refine ⟨μ, fun k => hasMoments_of_tendsto_quasi_of_level h ν hν τ' hφ hopen hlim k, ?_⟩
  refine measure_open_eq_zero_of_compacts _ (isOpen_nevBrealInf_ne_zero h h0b) ?_
  intro K hK hKU
  obtain ⟨L, hLc, hKL, hLU⟩ :=
    exists_compact_between hK (isOpen_nevBrealInf_ne_zero h h0b) hKU
  have hLF : ∀ x ∈ L, nevBrealInf s x ≠ 0 := fun x hx => hLU hx
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp
    (eventually_quasiMeasure_compact_eq_zero_inf h h0b hLc hLF)
  have hzero : ∀ᶠ i in atTop, quasiProb s (ν (φ i)) (τ' (φ i)) (interior L) = 0 := by
    refine Filter.eventually_atTop.mpr ⟨N₀, fun i hi => ?_⟩
    have hgrow : N₀ ≤ ν (φ i) := by
      have h1 : i ≤ φ i := hφ.le_apply
      have h2 : φ i + 1 ≤ ν (φ i) := hν (φ i)
      omega
    have hmzero : quasiMeasure s (ν (φ i)) (τ' (φ i)) L = 0 :=
      hN₀ (ν (φ i)) hgrow (goodLevelInf_nevAlphaInf_ne_zero h (φ i))
    rw [quasiProb, Measure.smul_apply, smul_eq_mul]
    have hsub : quasiMeasure s (ν (φ i)) (τ' (φ i)) (interior L) = 0 :=
      le_antisymm (le_trans (measure_mono interior_subset) (le_of_eq hmzero)) zero_le
    rw [hsub, mul_zero]
  have hlim0 : atTop.liminf (fun i => quasiProb s (ν (φ i)) (τ' (φ i)) (interior L)) = 0 := by
    rw [Filter.liminf_congr hzero, liminf_const]
  have hint : (μ : Measure ℝ) (interior L) = 0 := by
    refine le_antisymm ?_ zero_le
    rw [← hlim0]
    exact hopen (interior L) isOpen_interior
  exact le_antisymm (le_trans (measure_mono hKL) (le_of_eq hint)) zero_le

/-- **The leaf at infinity, in fiber form.** -/
theorem exists_leaf_infinityDenominatorFiber (h : PositiveMomentForm s)
    (h0b : BoundedKernel s 0) :
    ∃ μ : ProbabilityMeasure ℝ,
      GaloisForLFunctions.HTGeometry.HasHamburgerMoments (fun k => (s 0)⁻¹ * s k)
          (μ : Measure ℝ) ∧
        (μ : Measure ℝ) (nevMatrixDataInf h h0b).infinityDenominatorFiberᶜ = 0 := by
  obtain ⟨μ, hmom, hcar⟩ := exists_leaf_infinity h h0b
  refine ⟨μ, fun k => hmom k, ?_⟩
  have hset : (nevMatrixDataInf h h0b).infinityDenominatorFiberᶜ
      = {x : ℝ | nevBrealInf s x ≠ 0} := by
    ext x
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq,
      GaloisForLFunctions.HTGeometry.ClassicalNevanlinnaMatrixData.infinityDenominatorFiber,
      nevMatrixDataInf]
  rw [hset]
  exact hcar

end HTGeometry
