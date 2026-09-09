import GaloisForLFunctions.HTGeometry.FokasLenellsRawComplexGraph
import GaloisForLFunctions.RHTower.FokasLenellsCutoffWeakLimits
import GaloisForLFunctions.HTGeometry.L2MultiplierContinuity

/-!
# Exact strong recovery on the maximal raw complex graph domain

Cutoff evolution converges precisely on the actual multiplication graph.
The graph domain is complete and dense, but is all of L² (or closed in L²)
exactly at order zero and real time. Cauchy compression also recovers the
raw graph output on this domain; no converse for compressed recovery is asserted.
-/

open MeasureTheory Complex Filter Topology Set
open scoped ENNReal
namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section

/-- The cutoff projection, with the irrelevant point zero retained. -/
def rawComplexGraphCutoffSymbol (a z : ℝ) : ℂ :=
  (insert 0 (cutoffPhaseSet a)).indicator (fun _ => 1) z

private theorem measurable_graphCutoffSymbol (a : ℝ) :
    Measurable (rawComplexGraphCutoffSymbol a) :=
  measurable_const.indicator ((measurableSet_cutoffPhaseSet a).insert 0)

private theorem graphCutoffSymbol_bound (a z : ℝ) :
    ‖rawComplexGraphCutoffSymbol a z‖ ≤ 1 := by
  by_cases hz : z ∈ insert 0 (cutoffPhaseSet a)
  · simp [rawComplexGraphCutoffSymbol,Set.indicator_of_mem hz]
  · simp [rawComplexGraphCutoffSymbol,Set.indicator_of_notMem hz]

private theorem graphCutoffSymbol_tendsto (z : ℝ) :
    Tendsto (fun a => rawComplexGraphCutoffSymbol a z) atBot (𝓝 1) := by
  apply tendsto_const_nhds.congr'
  by_cases hz : z = 0
  · subst z
    exact Eventually.of_forall (fun a => by simp [rawComplexGraphCutoffSymbol])
  · filter_upwards [eventually_le_atBot (Real.log |z|)] with a ha
    have hm : z ∈ cutoffPhaseSet a := by
      change Real.exp a ≤ |z|
      calc
        _ ≤ Real.exp (Real.log |z|) := Real.exp_le_exp.mpr ha
        _ = _ := Real.exp_log (abs_pos.mpr hz)
    simp [rawComplexGraphCutoffSymbol,Set.indicator_of_mem (mem_insert_of_mem 0 hm)]

/-- Bounded projections recovering every vector in the original Hilbert space. -/
def rawComplexGraphCutoff (a : ℝ) :
    Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  lpBoundedMulCLM (p := 2) (μ := volume) (measurable_graphCutoffSymbol a)
    (by norm_num : (0 : ℝ) ≤ 1) (graphCutoffSymbol_bound a)

private theorem graphCutoff_ae (a : ℝ) (u : Lp ℂ 2 (volume : Measure ℝ)) :
    (rawComplexGraphCutoff a u : ℝ → ℂ) =ᵐ[volume]
      fun z => rawComplexGraphCutoffSymbol a z * u z :=
  lpBoundedMulCLM_coeFn (measurable_graphCutoffSymbol a)
    (by norm_num : (0 : ℝ) ≤ 1) (graphCutoffSymbol_bound a) u

/-- Removing the cutoff strongly recovers every original Hilbert vector. -/
theorem rawComplexGraphCutoff_tendsto (u : Lp ℂ 2 (volume : Measure ℝ)) :
    Tendsto (fun a => rawComplexGraphCutoff a u) atBot (𝓝 u) := by
  have h := tendsto_lpBoundedMulCLM_apply (μ := volume)
    measurable_graphCutoffSymbol (measurable_const : Measurable (fun _ : ℝ => (1 : ℂ)))
    (by norm_num : (0 : ℝ) ≤ 1) graphCutoffSymbol_bound
    (fun _ => by simp) graphCutoffSymbol_tendsto u
  have he : lpBoundedMulCLM (p := 2) (μ := volume)
      (measurable_const : Measurable (fun _ : ℝ => (1 : ℂ)))
      (by norm_num : (0 : ℝ) ≤ 1) (fun _ => by simp) u = u := by
    apply Lp.ext
    filter_upwards [lpBoundedMulCLM_coeFn (p := 2) (μ := volume)
      (measurable_const : Measurable (fun _ : ℝ => (1 : ℂ)))
      (by norm_num : (0 : ℝ) ≤ 1) (fun _ => by simp) u] with z hz
    simpa using hz
  rw [he] at h
  exact h

/-- Exact retained/frozen decomposition of every cutoff complex derivative. -/
theorem cutoffComplexSymbol_graph_decomposition (a : ℝ) (n : ℕ) (τ : ℂ) (z : ℝ) :
    cutoffComplexSymbol a n τ z = (if n = 0 then 1 else 0) +
      rawComplexGraphCutoffSymbol a z * (rawComplexSymbol n τ z - (if n = 0 then 1 else 0)) := by
  rw [cutoffComplexSymbol_eq_raw_or_frozen]
  by_cases hz : z = 0
  · subst z
    have hn : ¬ Real.exp a ≤ |(0 : ℝ)| := by simpa using Real.exp_pos a
    rw [if_neg hn]
    cases n <;> simp [rawComplexGraphCutoffSymbol,rawComplexSymbol]
  · by_cases hm : Real.exp a ≤ |z|
    · rw [if_pos hm]
      have hh : z ∈ insert 0 (cutoffPhaseSet a) := mem_insert_of_mem 0 hm
      simp only [rawComplexGraphCutoffSymbol,Set.indicator_of_mem hh,one_mul]
      ring
    · rw [if_neg hm]
      have hh : z ∉ insert 0 (cutoffPhaseSet a) := by
        rw [mem_insert_iff]
        exact not_or.mpr ⟨hz,hm⟩
      simp [rawComplexGraphCutoffSymbol,Set.indicator_of_notMem hh]

/-- Exact bounded-cutoff representation of the raw graph action. -/
theorem rawComplexGraph_cutoff_decomposition (n : ℕ) (τ : ℂ) (p : rawComplexGraph n τ) (a : ℝ) :
    cutoffComplexOperator a n τ (rawComplexGraphInput n τ p) =
      (if n = 0 then (1 : ℂ) else 0) • rawComplexGraphInput n τ p +
        rawComplexGraphCutoff a (rawComplexGraphOutput n τ p -
          (if n = 0 then (1 : ℂ) else 0) • rawComplexGraphInput n τ p) := by
  let u := rawComplexGraphInput n τ p
  let v := rawComplexGraphOutput n τ p
  let c : ℂ := if n = 0 then 1 else 0
  have hp : (v : ℝ → ℂ) =ᵐ[volume] fun z => rawComplexSymbol n τ z * u z := p.property
  apply Lp.ext
  filter_upwards [cutoffComplexOperator_ae a n τ u,hp,
    graphCutoff_ae a (v - c • u),Lp.coeFn_sub v (c • u),Lp.coeFn_smul c u,
    Lp.coeFn_add (c • u) (rawComplexGraphCutoff a (v - c • u))] with z hm hp hq hs hc ha
  change cutoffComplexOperator a n τ u z = (c • u + rawComplexGraphCutoff a (v - c • u)) z
  rw [hm,ha,Pi.add_apply,hq,hs,Pi.sub_apply,hc,Pi.smul_apply,hp]
  simp only [smul_eq_mul]
  rw [cutoffComplexSymbol_graph_decomposition]
  change (c + rawComplexGraphCutoffSymbol a z * (rawComplexSymbol n τ z - c)) * u z = _
  ring

/-- Every genuine raw graph input is recovered strongly with its actual raw output. -/
theorem rawComplexGraph_cutoff_tendsto (n : ℕ) (τ : ℂ) (p : rawComplexGraph n τ) :
    Tendsto (fun a => cutoffComplexOperator a n τ (rawComplexGraphInput n τ p))
      atBot (𝓝 (rawComplexGraphOutput n τ p)) := by
  have h := (tendsto_const_nhds (x :=
    (if n = 0 then (1 : ℂ) else 0) • rawComplexGraphInput n τ p)).add (rawComplexGraphCutoff_tendsto
    (rawComplexGraphOutput n τ p - (if n = 0 then (1 : ℂ) else 0) • rawComplexGraphInput n τ p))
  have he : (if n = 0 then (1 : ℂ) else 0) • rawComplexGraphInput n τ p +
      (rawComplexGraphOutput n τ p - (if n = 0 then (1 : ℂ) else 0) • rawComplexGraphInput n τ p) =
      rawComplexGraphOutput n τ p := by abel
  rw [he] at h
  simpa only [rawComplexGraph_cutoff_decomposition] using h

private theorem negative_nat_tendsto :
    Tendsto (fun k : ℕ => -(k : ℝ)) atTop atBot :=
  tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop

/-- The actual raw multiplication graph is exactly the maximal strong cutoff recovery graph. -/
theorem rawComplexGraph_mem_iff_cutoff_tendsto (n : ℕ) (τ : ℂ)
    (u v : Lp ℂ 2 (volume : Measure ℝ)) :
    (u,v) ∈ rawComplexGraph n τ ↔
      Tendsto (fun a => cutoffComplexOperator a n τ u) atBot (𝓝 v) := by
  constructor
  · intro hp
    exact rawComplexGraph_cutoff_tendsto n τ ⟨(u,v),hp⟩
  · intro hv
    obtain ⟨ns,hns,hsub⟩ := exists_subseq_ae_tendsto (hv.comp negative_nat_tendsto)
    have hall : ∀ᵐ z ∂volume, ∀ i : ℕ,
        cutoffComplexOperator (-(ns i : ℝ)) n τ u z =
          cutoffComplexSymbol (-(ns i : ℝ)) n τ z * u z :=
      ae_all_iff.mpr (fun i => cutoffComplexOperator_ae (-(ns i : ℝ)) n τ u)
    filter_upwards [hsub,hall] with z hvz haz
    have hraw := ((cutoffComplexSymbol_tendsto_raw n τ z).comp
      (negative_nat_tendsto.comp hns.tendsto_atTop)).mul_const (u z)
    have hout : Tendsto (fun i => cutoffComplexOperator (-(ns i : ℝ)) n τ u z)
        atTop (𝓝 (rawComplexSymbol n τ z * u z)) := by
      exact hraw.congr (fun i => (haz i).symm)
    exact tendsto_nhds_unique hvz hout

/-- Cauchy compression recovers the actual raw output on every genuine graph input. -/
theorem rawComplexGraph_cutoffCauchy_tendsto (n : ℕ) (τ : ℂ) (p : rawComplexGraph n τ) :
    Tendsto (fun a => RHTower.FokasLenells.cutoffComplexCauchyOperator a n τ
      (rawComplexGraphInput n τ p)) atBot
      (𝓝 (RHTower.FokasLenells.negativeCauchy (rawComplexGraphOutput n τ p))) :=
  RHTower.FokasLenells.negativeCauchy.continuous.continuousAt.tendsto.comp
    (rawComplexGraph_cutoff_tendsto n τ p)

/-- The complete raw graph domain fills L² exactly at order zero and real time. -/
theorem rawComplexGraphInput_surjective_iff (n : ℕ) (τ : ℂ) :
    Function.Surjective (rawComplexGraphInput n τ) ↔ n = 0 ∧ τ.im = 0 := by
  constructor
  · intro hs
    apply (RHTower.FokasLenells.cutoffComplexOperator_all_matrixCoefficients_converge_iff n τ).1
    intro u v
    obtain ⟨p,rfl⟩ := hs u
    exact ⟨inner ℂ (rawComplexGraphOutput n τ p) v,
      (rawComplexGraph_cutoff_tendsto n τ p).inner tendsto_const_nhds⟩
  · rintro ⟨rfl,hi⟩ u
    have he : τ = (τ.re : ℂ) := by apply Complex.ext <;> simp [hi]
    have hp : (u,evolution τ.re u) ∈ rawComplexGraph 0 τ := by
      filter_upwards [evolution_ae τ.re u] with z hz
      change (evolution τ.re u) z = rawComplexSymbol 0 τ z * u z
      rw [he,rawComplexSymbol_zero_ofReal,Complex.ofReal_re]
      exact hz
    exact ⟨⟨(u,evolution τ.re u),hp⟩,rfl⟩

/-- In every unbounded case the dense raw domain is proper and nonclosed in the original L² norm. -/
theorem isClosed_range_rawComplexGraphInput_iff (n : ℕ) (τ : ℂ) :
    IsClosed (Set.range (rawComplexGraphInput n τ)) ↔ n = 0 ∧ τ.im = 0 := by
  rw [← rawComplexGraphInput_surjective_iff]
  constructor
  · intro hc u
    have hu := rawComplexGraphInput_denseRange n τ u
    rw [hc.closure_eq] at hu
    exact hu
  · intro hs
    rw [Set.range_eq_univ.mpr hs]
    exact isClosed_univ

end
end GaloisForLFunctions.HTGeometry.FokasLenells
