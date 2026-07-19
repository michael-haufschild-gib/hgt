import GaloisForLFunctions.HTGeometry.InfinitySignChange
import GaloisForLFunctions.HTGeometry.InfinityLeaf
import GaloisForLFunctions.HTGeometry.LeafAtoms

/-!
# The atoms of the leaf at infinity

The same assembly as for a finite parameter, with `B` in place of `B·τ − D`.
-/

open scoped BigOperators
open MeasureTheory Filter Set

namespace HTGeometry

variable {s : ℕ → ℝ}

/-- **The leaf at infinity together with its approximating sequence.** -/
theorem exists_leaf_infinity_approx (h : PositiveMomentForm s) (h0b : BoundedKernel s 0) :
    ∃ (μ : ProbabilityMeasure ℝ) (φ : ℕ → ℕ), StrictMono φ ∧
      Tendsto (fun i => quasiProbMeasure h (goodLevelInf h (φ i)) (leafParamInf h (φ i)))
        atTop (nhds μ) ∧
      (∀ k : ℕ, Integrable (fun x : ℝ => x ^ k) (μ : Measure ℝ) ∧
        ∫ x, x ^ k ∂(μ : Measure ℝ) = (s 0)⁻¹ * s k) ∧
      (μ : Measure ℝ) {x : ℝ | nevBrealInf s x ≠ 0} = 0 := by
  classical
  have hν : ∀ n, n + 1 ≤ goodLevelInf h n := goodLevelInf_ge h
  obtain ⟨μ, φ, hφ, hlim⟩ :=
    exists_subseq_tendsto_quasiProbMeasure_of_level h (goodLevelInf h) hν (leafParamInf h)
  have hopen : ∀ G, IsOpen G →
      (μ : Measure ℝ) G ≤ atTop.liminf fun i =>
        quasiProb s (goodLevelInf h (φ i)) (leafParamInf h (φ i)) G :=
    fun G hG => ProbabilityMeasure.le_liminf_measure_open_of_tendsto hlim hG
  refine ⟨μ, φ, hφ, hlim,
    fun k => hasMoments_of_tendsto_quasi_of_level h (goodLevelInf h) hν (leafParamInf h)
      hφ hopen hlim k, ?_⟩
  refine measure_open_eq_zero_of_compacts _ (isOpen_nevBrealInf_ne_zero h h0b) ?_
  intro K hK hKU
  obtain ⟨L, hLc, hKL, hLU⟩ :=
    exists_compact_between hK (isOpen_nevBrealInf_ne_zero h h0b) hKU
  have hLF : ∀ x ∈ L, nevBrealInf s x ≠ 0 := fun x hx => hLU hx
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp
    (eventually_quasiMeasure_compact_eq_zero_inf h h0b hLc hLF)
  have hzero : ∀ᶠ i in atTop,
      quasiProb s (goodLevelInf h (φ i)) (leafParamInf h (φ i)) (interior L) = 0 := by
    refine Filter.eventually_atTop.mpr ⟨N₀, fun i hi => ?_⟩
    have hgrow : N₀ ≤ goodLevelInf h (φ i) := by
      have h1 : i ≤ φ i := hφ.le_apply
      have h2 : φ i + 1 ≤ goodLevelInf h (φ i) := hν (φ i)
      omega
    have hmzero : quasiMeasure s (goodLevelInf h (φ i)) (leafParamInf h (φ i)) L = 0 :=
      hN₀ (goodLevelInf h (φ i)) hgrow (goodLevelInf_nevAlphaInf_ne_zero h (φ i))
    rw [quasiProb, Measure.smul_apply, smul_eq_mul]
    have hsub : quasiMeasure s (goodLevelInf h (φ i)) (leafParamInf h (φ i)) (interior L) = 0 :=
      le_antisymm (le_trans (measure_mono interior_subset) (le_of_eq hmzero)) zero_le
    rw [hsub, mul_zero]
  have hlim0 : atTop.liminf (fun i =>
      quasiProb s (goodLevelInf h (φ i)) (leafParamInf h (φ i)) (interior L)) = 0 := by
    rw [Filter.liminf_congr hzero, liminf_const]
  have hint : (μ : Measure ℝ) (interior L) = 0 := by
    refine le_antisymm ?_ zero_le
    rw [← hlim0]
    exact hopen (interior L) isOpen_interior
  exact le_antisymm (le_trans (measure_mono hKL) (le_of_eq hint)) zero_le

/-- **The atom at a zero of `B` is at least the Christoffel limit.** -/
theorem ofReal_christoffelLimit_le_leaf_infinity_singleton (h : PositiveMomentForm s)
    (h0b : BoundedKernel s 0) (h0 : s 0 = 1) {μ : ProbabilityMeasure ℝ} {φ : ℕ → ℕ}
    (hφ : StrictMono φ)
    (hlim : Tendsto (fun i => quasiProbMeasure h (goodLevelInf h (φ i)) (leafParamInf h (φ i)))
      atTop (nhds μ))
    {ξ : ℝ} (hξ : nevBrealInf s ξ = 0) :
    ENNReal.ofReal (christoffelLimit s ξ) ≤ (μ : Measure ℝ) {ξ} := by
  obtain ⟨η₁, hη₁, hnode⟩ := eventually_exists_quasiNode_near_inf h h0b hξ
  have hle : ∀ ε : ℝ, 0 < ε → christoffelLimit s ξ - ε ≤ ((μ : Measure ℝ) {ξ}).toReal := by
    intro ε hε
    have hcont := (continuous_christoffelLimit h h0b).continuousAt (x := ξ)
    have hev : ∀ᶠ x in nhds ξ, christoffelLimit s ξ - ε < christoffelLimit s x :=
      hcont.eventually_const_lt (by linarith)
    rw [Metric.eventually_nhds_iff] at hev
    obtain ⟨η₂, hη₂, hall₂⟩ := hev
    set η : ℝ := min η₁ η₂ with hηdef
    have hη : 0 < η := lt_min hη₁ hη₂
    have hIcc : ∀ δ : ℝ, 0 < δ → δ < η →
        ENNReal.ofReal (christoffelLimit s ξ - ε) ≤ (μ : Measure ℝ) (Icc (ξ - δ) (ξ + δ)) := by
      intro δ hδ hδη
      have hδ1 : δ < η₁ := lt_of_lt_of_le hδη (min_le_left _ _)
      have hδ2 : δ < η₂ := lt_of_lt_of_le hδη (min_le_right _ _)
      obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hnode δ hδ hδ1)
      have hbelow : ∀ᶠ i in atTop, ENNReal.ofReal (christoffelLimit s ξ - ε)
          ≤ quasiProb s (goodLevelInf h (φ i)) (leafParamInf h (φ i)) (Icc (ξ - δ) (ξ + δ)) := by
        refine Filter.eventually_atTop.mpr ⟨N, fun i hi => ?_⟩
        have hgrow : N ≤ goodLevelInf h (φ i) := by
          have h1 : i ≤ φ i := hφ.le_apply
          have h2 : φ i + 1 ≤ goodLevelInf h (φ i) := goodLevelInf_ge h (φ i)
          omega
        obtain ⟨x, hxmem, hxδ⟩ :=
          hN (goodLevelInf h (φ i)) hgrow (goodLevelInf_nevAlphaInf_ne_zero h (φ i))
        have hxA : x ∈ Icc (ξ - δ) (ξ + δ) := by
          rw [mem_Icc]
          rw [abs_le] at hxδ
          exact ⟨by linarith [hxδ.1], by linarith [hxδ.2]⟩
        have hlamx : christoffelLimit s ξ - ε < christoffelLimit s x := by
          have hdist : dist x ξ < η₂ := by
            rw [Real.dist_eq]
            exact lt_of_le_of_lt hxδ hδ2
          exact hall₂ hdist
        refine le_trans (ENNReal.ofReal_le_ofReal hlamx.le) ?_
        exact quasiProb_ge_ofReal_christoffelLimit h h0 _ _ measurableSet_Icc hxmem hxA
      have hport := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hlim
        (F := Icc (ξ - δ) (ξ + δ)) isClosed_Icc
      refine le_trans ?_ hport
      exact le_limsup_of_frequently_le hbelow.frequently
    have hsing := le_measure_singleton_of_forall_Icc (μ : Measure ℝ) ξ hη hIcc
    have htop : (μ : Measure ℝ) {ξ} ≠ ⊤ := measure_ne_top _ _
    have h2 : ENNReal.ofReal (christoffelLimit s ξ - ε)
        ≤ ENNReal.ofReal (((μ : Measure ℝ) {ξ}).toReal) := by
      rwa [ENNReal.ofReal_toReal htop]
    exact (ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg).mp h2
  have hfinal : christoffelLimit s ξ ≤ ((μ : Measure ℝ) {ξ}).toReal := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    linarith [hle ε hε]
  calc ENNReal.ofReal (christoffelLimit s ξ)
      ≤ ENNReal.ofReal (((μ : Measure ℝ) {ξ}).toReal) := ENNReal.ofReal_le_ofReal hfinal
    _ = (μ : Measure ℝ) {ξ} := ENNReal.ofReal_toReal (measure_ne_top _ _)

/-- **The leaf at infinity, with its weights identified.** -/
theorem exists_leaf_infinity_atoms (h : PositiveMomentForm s) (h0b : BoundedKernel s 0)
    (h0 : s 0 = 1) :
    ∃ μ : ProbabilityMeasure ℝ,
      GaloisForLFunctions.HTGeometry.HasHamburgerMoments s (μ : Measure ℝ) ∧
        (μ : Measure ℝ) (nevMatrixDataInf h h0b).infinityDenominatorFiberᶜ = 0 ∧
        ∀ ξ ∈ (nevMatrixDataInf h h0b).infinityDenominatorFiber,
          (μ : Measure ℝ) {ξ} = ENNReal.ofReal (christoffelLimit s ξ) := by
  obtain ⟨μ, φ, hφ, hlim, hmom, hcar⟩ := exists_leaf_infinity_approx h h0b
  have hmom' : GaloisForLFunctions.HTGeometry.HasHamburgerMoments s (μ : Measure ℝ) := by
    intro k
    refine ⟨(hmom k).1, ?_⟩
    simpa [h0] using (hmom k).2
  have hset : (nevMatrixDataInf h h0b).infinityDenominatorFiberᶜ
      = {x : ℝ | nevBrealInf s x ≠ 0} := by
    ext x
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq,
      GaloisForLFunctions.HTGeometry.ClassicalNevanlinnaMatrixData.infinityDenominatorFiber,
      nevMatrixDataInf]
  refine ⟨μ, hmom', by rw [hset]; exact hcar, fun ξ hξmem => ?_⟩
  have hξ : nevBrealInf s ξ = 0 := hξmem
  refine le_antisymm ?_ ?_
  · exact measure_singleton_le_ofReal_christoffelLimit h hmom' ξ
  · exact ofReal_christoffelLimit_le_leaf_infinity_singleton h h0b h0 hφ hlim hξ

end HTGeometry
