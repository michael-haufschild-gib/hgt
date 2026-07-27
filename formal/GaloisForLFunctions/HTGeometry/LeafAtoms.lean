import GaloisForLFunctions.HTGeometry.LeafConstruction
import GaloisForLFunctions.HTGeometry.FiberWeightSum
import GaloisForLFunctions.HTGeometry.NodeConvergence
import GaloisForLFunctions.HTGeometry.QuasiMeasureLowerBound
import GaloisForLFunctions.HTGeometry.KernelContinuity

/-!
# The atoms of the leaf are the Christoffel limits

The approximating measures carry a node near every fiber point, hence mass at least `λ` there; the
portmanteau inequality for closed sets carries that to the limit, and shrinking the interval gives the
atom.  With the general bound in the other direction this identifies every atom of the leaf.
-/

open scoped BigOperators
open MeasureTheory Filter Set

namespace HTGeometry

variable {s : ℕ → ℝ}

/-- **The leaf together with its approximating sequence.** -/
theorem exists_leaf_approx (h : PositiveMomentForm s) (h0b : BoundedKernel s 0) (tau : ℝ) :
    ∃ (μ : ProbabilityMeasure ℝ) (φ : ℕ → ℕ), StrictMono φ ∧
      Tendsto (fun i => quasiProbMeasure h (goodLevel h tau (φ i)) (leafParam h tau (φ i)))
        atTop (nhds μ) ∧
      (∀ k : ℕ, Integrable (fun x : ℝ => x ^ k) (μ : Measure ℝ) ∧
        ∫ x, x ^ k ∂(μ : Measure ℝ) = (s 0)⁻¹ * s k) ∧
      (μ : Measure ℝ) {x : ℝ | nevBrealInf s x * tau - nevDrealInf s x ≠ 0} = 0 := by
  classical
  have hν : ∀ n, n + 1 ≤ goodLevel h tau n := goodLevel_ge h tau
  obtain ⟨μ, φ, hφ, hlim⟩ :=
    exists_subseq_tendsto_quasiProbMeasure_of_level h (goodLevel h tau) hν (leafParam h tau)
  have hopen : ∀ G, IsOpen G →
      (μ : Measure ℝ) G ≤ atTop.liminf fun i =>
        quasiProb s (goodLevel h tau (φ i)) (leafParam h tau (φ i)) G :=
    fun G hG => ProbabilityMeasure.le_liminf_measure_open_of_tendsto hlim hG
  refine ⟨μ, φ, hφ, hlim,
    fun k => hasMoments_of_tendsto_quasi_of_level h (goodLevel h tau) hν (leafParam h tau)
      hφ hopen hlim k, ?_⟩
  refine measure_open_eq_zero_of_compacts _ (isOpen_denominator_ne_zero h h0b tau) ?_
  intro K hK hKU
  obtain ⟨L, hLc, hKL, hLU⟩ :=
    exists_compact_between hK (isOpen_denominator_ne_zero h h0b tau) hKU
  have hLF : ∀ x ∈ L, nevBrealInf s x * tau - nevDrealInf s x ≠ 0 := fun x hx => hLU hx
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp
    (eventually_quasiMeasure_compact_eq_zero h h0b tau hLc hLF)
  have hzero : ∀ᶠ i in atTop,
      quasiProb s (goodLevel h tau (φ i)) (leafParam h tau (φ i)) (interior L) = 0 := by
    refine Filter.eventually_atTop.mpr ⟨N₀, fun i hi => ?_⟩
    have hgrow : N₀ ≤ goodLevel h tau (φ i) := by
      have h1 : i ≤ φ i := hφ.le_apply
      have h2 : φ i + 1 ≤ goodLevel h tau (φ i) := hν (φ i)
      omega
    have hmzero : quasiMeasure s (goodLevel h tau (φ i)) (leafParam h tau (φ i)) L = 0 :=
      hN₀ (goodLevel h tau (φ i)) hgrow (goodLevel_nevAlpha_ne_zero h tau (φ i))
    rw [quasiProb, Measure.smul_apply, smul_eq_mul]
    have hsub : quasiMeasure s (goodLevel h tau (φ i)) (leafParam h tau (φ i)) (interior L) = 0 :=
      le_antisymm (le_trans (measure_mono interior_subset) (le_of_eq hmzero)) zero_le
    rw [hsub, mul_zero]
  have hlim0 : atTop.liminf (fun i =>
      quasiProb s (goodLevel h tau (φ i)) (leafParam h tau (φ i)) (interior L)) = 0 := by
    rw [Filter.liminf_congr hzero, liminf_const]
  have hint : (μ : Measure ℝ) (interior L) = 0 := by
    refine le_antisymm ?_ zero_le
    rw [← hlim0]
    exact hopen (interior L) isOpen_interior
  exact le_antisymm (le_trans (measure_mono hKL) (le_of_eq hint)) zero_le

/-- **Atoms of a convergent quasi-level family.**  Let `lvl` be a level map growing past its index
and `par` the associated leaf parameters.  If every sufficiently small neighbourhood of `ξ`
eventually contains a quasi-node of level `lvl i` with parameter `par i`, and the leaf measures
along a strictly monotone subsequence converge to `μ`, then `μ` charges `{ξ}` at least by the
Christoffel limit at `ξ`.  Continuity of the Christoffel limit turns each node into a lower bound on
a shrinking interval, the portmanteau inequality transports that bound to `μ`, and letting the
interval shrink isolates the atom. -/
theorem ofReal_christoffelLimit_le_leaf_singleton_of_eventually_node
    (h : PositiveMomentForm s) (h0b : BoundedKernel s 0) (h0 : s 0 = 1)
    {lvl : ℕ → ℕ} {par : ℕ → ℝ} (hlvl : ∀ n, n + 1 ≤ lvl n)
    {μ : ProbabilityMeasure ℝ} {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (hlim : Tendsto (fun i => quasiProbMeasure h (lvl (φ i)) (par (φ i))) atTop (nhds μ))
    {ξ : ℝ}
    (hnode : ∃ η > 0, ∀ δ : ℝ, 0 < δ → δ < η →
      ∀ᶠ n in atTop, ∀ i : ℕ, n = lvl i →
        ∃ x ∈ quasiNodes s n (par i), |x - ξ| ≤ δ) :
    ENNReal.ofReal (christoffelLimit s ξ) ≤ (μ : Measure ℝ) {ξ} := by

  obtain ⟨η₁, hη₁, hnode⟩ := hnode
  have hle : ∀ ε : ℝ, 0 < ε → christoffelLimit s ξ - ε ≤ ((μ : Measure ℝ) {ξ}).toReal := by
    intro ε hε
    -- continuity of λ gives an interval on which λ stays above λ(ξ) − ε
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
          ≤ quasiProb s (lvl (φ i)) (par (φ i)) (Icc (ξ - δ) (ξ + δ)) := by
        refine Filter.eventually_atTop.mpr ⟨N, fun i hi => ?_⟩
        have hgrow : N ≤ lvl (φ i) := by
          have h1 : i ≤ φ i := hφ.le_apply
          have h2 : φ i + 1 ≤ lvl (φ i) := hlvl (φ i)
          omega
        obtain ⟨x, hxmem, hxδ⟩ :=
          hN (lvl (φ i)) hgrow (φ i) rfl
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

/-- **The atom of the leaf at a fiber point is at least the Christoffel limit.** -/
theorem ofReal_christoffelLimit_le_leaf_singleton (h : PositiveMomentForm s)
    (h0b : BoundedKernel s 0) (h0 : s 0 = 1) {tau : ℝ} {μ : ProbabilityMeasure ℝ} {φ : ℕ → ℕ}
    (hφ : StrictMono φ)
    (hlim : Tendsto (fun i => quasiProbMeasure h (goodLevel h tau (φ i)) (leafParam h tau (φ i)))
      atTop (nhds μ))
    {ξ : ℝ} (hξ : nevBrealInf s ξ * tau - nevDrealInf s ξ = 0) :
    ENNReal.ofReal (christoffelLimit s ξ) ≤ (μ : Measure ℝ) {ξ} := by
  refine ofReal_christoffelLimit_le_leaf_singleton_of_eventually_node h h0b h0
    (lvl := goodLevel h tau) (par := leafParam h tau) (goodLevel_ge h tau) hφ hlim ?_
  obtain ⟨η, hη, hnode⟩ := eventually_exists_quasiNode_near h h0b hξ
  refine ⟨η, hη, fun δ hδ hδη => ?_⟩
  filter_upwards [hnode δ hδ hδη] with n hn i hi
  subst hi
  exact hn (goodLevel_nevAlpha_ne_zero h tau i)

/-- **The N-extremal leaf, with its weights identified.**  For a normalised moment sequence and any
finite parameter there is a probability measure representing the sequence, carried by the denominator
fiber, whose atom at each fiber point is exactly the Christoffel limit there. -/
theorem exists_leaf_atoms (h : PositiveMomentForm s) (h0b : BoundedKernel s 0) (h0 : s 0 = 1)
    (tau : ℝ) :
    ∃ μ : ProbabilityMeasure ℝ,
      GaloisForLFunctions.HTGeometry.HasHamburgerMoments s (μ : Measure ℝ) ∧
        (μ : Measure ℝ) ((nevMatrixDataInf h h0b).finiteDenominatorFiber tau)ᶜ = 0 ∧
        ∀ ξ ∈ (nevMatrixDataInf h h0b).finiteDenominatorFiber tau,
          (μ : Measure ℝ) {ξ} = ENNReal.ofReal (christoffelLimit s ξ) := by
  obtain ⟨μ, φ, hφ, hlim, hmom, hcar⟩ := exists_leaf_approx h h0b tau
  have hmom' : GaloisForLFunctions.HTGeometry.HasHamburgerMoments s (μ : Measure ℝ) := by
    intro k
    refine ⟨(hmom k).1, ?_⟩
    simpa [h0] using (hmom k).2
  have hset : ((nevMatrixDataInf h h0b).finiteDenominatorFiber tau)ᶜ
      = {x : ℝ | nevBrealInf s x * tau - nevDrealInf s x ≠ 0} := by
    ext x
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq,
      GaloisForLFunctions.HTGeometry.ClassicalNevanlinnaMatrixData.finiteDenominatorFiber,
      nevMatrixDataInf]
  refine ⟨μ, hmom', by rw [hset]; exact hcar, fun ξ hξmem => ?_⟩
  have hξ : nevBrealInf s ξ * tau - nevDrealInf s ξ = 0 := hξmem
  refine le_antisymm ?_ ?_
  · exact measure_singleton_le_ofReal_christoffelLimit h hmom' ξ
  · exact ofReal_christoffelLimit_le_leaf_singleton h h0b h0 hφ hlim hξ

end HTGeometry
