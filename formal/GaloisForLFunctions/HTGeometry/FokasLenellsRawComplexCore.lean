import GaloisForLFunctions.HTGeometry.FokasLenellsRawComplexRecovery

/-!
# A common entire-vector core for the raw complex hierarchy

Vectors supported away from the inverse-frequency singularity admit actual
entire L² orbits at every derivative order. Their union is dense in L² and
is an operator core for every complete raw graph: the same cutoff recovers
both input and output in the graph norm.
-/

open MeasureTheory Complex Filter Topology Set
open scoped ENNReal
namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section

private theorem coreCutoff_ae (a : ℝ) (u : Lp ℂ 2 (volume : Measure ℝ)) :
    (rawComplexGraphCutoff a u : ℝ → ℂ) =ᵐ[volume]
      fun z => rawComplexGraphCutoffSymbol a z * u z := by
  unfold rawComplexGraphCutoff
  exact lpBoundedMulCLM_coeFn _ _ _ _

private theorem coreSymbol_idempotent (a z : ℝ) :
    rawComplexGraphCutoffSymbol a z * rawComplexGraphCutoffSymbol a z =
      rawComplexGraphCutoffSymbol a z := by
  by_cases hz : z ∈ insert 0 (cutoffPhaseSet a)
  · simp [rawComplexGraphCutoffSymbol,Set.indicator_of_mem hz]
  · simp [rawComplexGraphCutoffSymbol,Set.indicator_of_notMem hz]

private theorem coreSymbol_agreement (a : ℝ) (n : ℕ) (τ : ℂ) (z : ℝ) :
    cutoffComplexSymbol a n τ z * rawComplexGraphCutoffSymbol a z =
      rawComplexSymbol n τ z * rawComplexGraphCutoffSymbol a z := by
  rw [cutoffComplexSymbol_graph_decomposition]
  calc
    _ = (if n = 0 then (1 : ℂ) else 0) * rawComplexGraphCutoffSymbol a z +
        (rawComplexGraphCutoffSymbol a z * rawComplexGraphCutoffSymbol a z) *
          (rawComplexSymbol n τ z - (if n = 0 then 1 else 0)) := by ring
    _ = _ := by rw [coreSymbol_idempotent]; ring

private theorem coreCutoff_absorb {a b : ℝ} (hab : a ≤ b) (u : Lp ℂ 2 (volume : Measure ℝ)) :
    rawComplexGraphCutoff a (rawComplexGraphCutoff b u) = rawComplexGraphCutoff b u := by
  apply Lp.ext
  filter_upwards [coreCutoff_ae a (rawComplexGraphCutoff b u),coreCutoff_ae b u] with z h0 h1
  rw [h0,h1]
  by_cases hb : z ∈ insert 0 (cutoffPhaseSet b)
  · have ha : z ∈ insert 0 (cutoffPhaseSet a) := by
      rcases mem_insert_iff.mp hb with rfl | hb
      · exact mem_insert 0 _
      · apply mem_insert_of_mem
        change Real.exp a ≤ |z|
        exact (Real.exp_le_exp.mpr hab).trans hb
    simp [rawComplexGraphCutoffSymbol,Set.indicator_of_mem ha,Set.indicator_of_mem hb]
  · simp [rawComplexGraphCutoffSymbol,Set.indicator_of_notMem hb]

/-- The concrete spectral cutoff is an actual projection on L². -/
theorem rawComplexGraphCutoff_idempotent (a : ℝ) (u : Lp ℂ 2 (volume : Measure ℝ)) :
    rawComplexGraphCutoff a (rawComplexGraphCutoff a u) = rawComplexGraphCutoff a u := by
  apply Lp.ext
  filter_upwards [coreCutoff_ae a (rawComplexGraphCutoff a u),coreCutoff_ae a u] with z h0 h1
  rw [h0,h1,← mul_assoc,coreSymbol_idempotent]

/-- The canonical raw entire orbit of a spectrally cut off vector. -/
def rawComplexCoreOrbit (a : ℝ) (u : Lp ℂ 2 (volume : Measure ℝ)) (n : ℕ) (τ : ℂ) :
    Lp ℂ 2 (volume : Measure ℝ) :=
  cutoffComplexOperator a n τ (rawComplexGraphCutoff a u)

/-- Every canonical core orbit equals the genuine raw complex multiplier almost everywhere. -/
theorem rawComplexCoreOrbit_ae (a : ℝ) (u : Lp ℂ 2 (volume : Measure ℝ)) (n : ℕ) (τ : ℂ) :
    (rawComplexCoreOrbit a u n τ : ℝ → ℂ) =ᵐ[volume]
      fun z => rawComplexSymbol n τ z * rawComplexGraphCutoff a u z := by
  filter_upwards [cutoffComplexOperator_ae a n τ (rawComplexGraphCutoff a u),coreCutoff_ae a u]
    with z h0 h1
  change cutoffComplexOperator a n τ (rawComplexGraphCutoff a u) z = _
  rw [h0,h1,← mul_assoc,coreSymbol_agreement,mul_assoc]

/-- One cutoff input belongs to every raw graph, with its actual complex orbit as output. -/
theorem rawComplexCoreOrbit_mem_graph (a : ℝ) (u : Lp ℂ 2 (volume : Measure ℝ)) (n : ℕ) (τ : ℂ) :
    (rawComplexGraphCutoff a u,rawComplexCoreOrbit a u n τ) ∈ rawComplexGraph n τ :=
  rawComplexCoreOrbit_ae a u n τ

/-- Actual Hilbert-space differentiation advances the raw hierarchy by one order. -/
theorem rawComplexCoreOrbit_hasDerivAt (a : ℝ) (u : Lp ℂ 2 (volume : Measure ℝ)) (n : ℕ) (τ : ℂ) :
    HasDerivAt (rawComplexCoreOrbit a u n) (rawComplexCoreOrbit a u (n+1) τ) τ := by
  exact (ContinuousLinearMap.apply ℂ (Lp ℂ 2 (volume : Measure ℝ))
    (rawComplexGraphCutoff a u)).hasFDerivAt.comp_hasDerivAt τ
      (cutoffComplexOperator_hasDerivAt a n τ)

/-- The actual raw L² orbit is entire in complex time at every derivative order. -/
theorem rawComplexCoreOrbit_analyticAt (a : ℝ) (u : Lp ℂ 2 (volume : Measure ℝ)) (n : ℕ) (τ : ℂ) :
    AnalyticAt ℂ (rawComplexCoreOrbit a u n) τ := by
  exact ((ContinuousLinearMap.apply ℂ (Lp ℂ 2 (volume : Measure ℝ))
    (rawComplexGraphCutoff a u)).analyticAt _).comp (cutoffComplexOperator_analyticAt a n τ)

/-- Every raw core derivative is the literal iterated derivative of the same entire orbit. -/
theorem iteratedDeriv_rawComplexCoreOrbit (a : ℝ) (u : Lp ℂ 2 (volume : Measure ℝ)) (n : ℕ) :
    iteratedDeriv n (rawComplexCoreOrbit a u 0) = rawComplexCoreOrbit a u n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iteratedDeriv_succ,ih]
    funext τ
    exact (rawComplexCoreOrbit_hasDerivAt a u n τ).deriv

/-- The entire zeroth orbit starts at the actual core input. -/
theorem rawComplexCoreOrbit_initial (a : ℝ) (u : Lp ℂ 2 (volume : Measure ℝ)) :
    rawComplexCoreOrbit a u 0 0 = rawComplexGraphCutoff a u := by
  change cutoffComplexOperator a 0 ((0 : ℝ) : ℂ) (rawComplexGraphCutoff a u) = _
  rw [cutoffComplexOperator_zero_ofReal,cutoffEvolution_zero,ContinuousLinearMap.id_apply]

/-- Every complex orbit and derivative retains the same concrete spectral cutoff. -/
theorem rawComplexCoreOrbit_cutoff_fixed (a : ℝ) (u : Lp ℂ 2 (volume : Measure ℝ)) (n : ℕ) (τ : ℂ) :
    rawComplexGraphCutoff a (rawComplexCoreOrbit a u n τ) = rawComplexCoreOrbit a u n τ := by
  apply Lp.ext
  filter_upwards [coreCutoff_ae a (rawComplexCoreOrbit a u n τ),
    rawComplexCoreOrbit_ae a u n τ,coreCutoff_ae a u] with z h0 h1 h2
  rw [h0,h1,h2]
  calc
    _ = rawComplexSymbol n τ z * (rawComplexGraphCutoffSymbol a z * rawComplexGraphCutoffSymbol a z) * u z := by ring
    _ = _ := by rw [coreSymbol_idempotent,mul_assoc]

/-- The common core consists of the actual ranges of the spectral cutoff projections. -/
def rawComplexEntireCore : Submodule ℂ (Lp ℂ 2 (volume : Measure ℝ)) where
  carrier := Set.range (fun p : ℝ × Lp ℂ 2 (volume : Measure ℝ) => rawComplexGraphCutoff p.1 p.2)
  zero_mem' := ⟨(0,0),map_zero _⟩
  add_mem' := by
    rintro _ _ ⟨⟨a,u⟩,rfl⟩ ⟨⟨b,v⟩,rfl⟩
    refine ⟨(min a b,rawComplexGraphCutoff a u + rawComplexGraphCutoff b v),?_⟩
    change rawComplexGraphCutoff (min a b) (rawComplexGraphCutoff a u + rawComplexGraphCutoff b v) = _
    rw [map_add,coreCutoff_absorb (min_le_left a b),coreCutoff_absorb (min_le_right a b)]
  smul_mem' := by
    rintro c _ ⟨⟨a,u⟩,rfl⟩
    exact ⟨(a,c • u),map_smul _ _ _⟩

/-- The common core is invariant under every actual complex orbit and derivative. -/
theorem rawComplexCoreOrbit_mem_core (a : ℝ) (u : Lp ℂ 2 (volume : Measure ℝ)) (n : ℕ) (τ : ℂ) :
    rawComplexCoreOrbit a u n τ ∈ rawComplexEntireCore :=
  ⟨(a,rawComplexCoreOrbit a u n τ),rawComplexCoreOrbit_cutoff_fixed a u n τ⟩

/-- Actual entire vectors form a dense subset of the original Hilbert space. -/
theorem dense_rawComplexEntireCore : Dense (rawComplexEntireCore : Set (Lp ℂ 2 (volume : Measure ℝ))) := by
  intro u
  exact mem_closure_of_tendsto (rawComplexGraphCutoff_tendsto u)
    (Eventually.of_forall (fun a => ⟨(a,u),rfl⟩))

/-- Every common-core vector has an actual output in every raw complex derivative graph. -/
theorem rawComplexEntireCore_mem_all_graph_domains (u : rawComplexEntireCore) (n : ℕ) (τ : ℂ) :
    u.val ∈ Set.range (rawComplexGraphInput n τ) := by
  obtain ⟨⟨a,w⟩,hw⟩ := u.property
  exact ⟨⟨(rawComplexGraphCutoff a w,rawComplexCoreOrbit a w n τ),
    rawComplexCoreOrbit_mem_graph a w n τ⟩,hw⟩

/-- The same spectral cutoff commutes with actual raw graph multiplication. -/
theorem rawComplexGraph_corePair_mem (n : ℕ) (τ : ℂ) (p : rawComplexGraph n τ) (a : ℝ) :
    (rawComplexGraphCutoff a (rawComplexGraphInput n τ p),
      rawComplexGraphCutoff a (rawComplexGraphOutput n τ p)) ∈ rawComplexGraph n τ := by
  have hp : (rawComplexGraphOutput n τ p : ℝ → ℂ) =ᵐ[volume]
    fun z => rawComplexSymbol n τ z * rawComplexGraphInput n τ p z := p.property
  filter_upwards [coreCutoff_ae a (rawComplexGraphInput n τ p),
    coreCutoff_ae a (rawComplexGraphOutput n τ p),hp] with z hu hv hpz
  change rawComplexGraphCutoff a (rawComplexGraphOutput n τ p) z = _
  rw [hv,hu,hpz]
  ring

/-- Canonical approximants inside the actual complete raw graph. -/
def rawComplexGraphCoreApprox (n : ℕ) (τ : ℂ) (p : rawComplexGraph n τ) (a : ℝ) : rawComplexGraph n τ :=
  ⟨(rawComplexGraphCutoff a (rawComplexGraphInput n τ p),
    rawComplexGraphCutoff a (rawComplexGraphOutput n τ p)),rawComplexGraph_corePair_mem n τ p a⟩

/-- Core approximation converges in the complete graph norm, controlling input and output together. -/
theorem rawComplexGraphCoreApprox_tendsto (n : ℕ) (τ : ℂ) (p : rawComplexGraph n τ) :
    Tendsto (rawComplexGraphCoreApprox n τ p) atBot (𝓝 p) := by
  apply tendsto_subtype_rng.mpr
  exact (rawComplexGraphCutoff_tendsto (rawComplexGraphInput n τ p)).prodMk_nhds
    (rawComplexGraphCutoff_tendsto (rawComplexGraphOutput n τ p))

/-- Every graph approximant has input in the same common entire-vector core. -/
theorem rawComplexGraphCoreApprox_input_mem_core (n : ℕ) (τ : ℂ) (p : rawComplexGraph n τ) (a : ℝ) :
    rawComplexGraphInput n τ (rawComplexGraphCoreApprox n τ p a) ∈ rawComplexEntireCore :=
  ⟨(a,rawComplexGraphInput n τ p),rfl⟩

/-- A single common entire-vector core is dense in every raw operator's complete graph norm. -/
theorem rawComplexGraph_core_dense (n : ℕ) (τ : ℂ) :
    Dense {p : rawComplexGraph n τ | rawComplexGraphInput n τ p ∈ rawComplexEntireCore} := by
  intro p
  exact mem_closure_of_tendsto (rawComplexGraphCoreApprox_tendsto n τ p)
    (Eventually.of_forall (rawComplexGraphCoreApprox_input_mem_core n τ p))

/-- Closing the restriction to the one common entire core recovers each full maximal raw graph. -/
theorem rawComplexGraph_eq_closure_core (n : ℕ) (τ : ℂ) :
    closure {p : Lp ℂ 2 (volume : Measure ℝ) × Lp ℂ 2 (volume : Measure ℝ) |
      p ∈ rawComplexGraph n τ ∧ p.1 ∈ rawComplexEntireCore} = rawComplexGraph n τ := by
  apply Set.Subset.antisymm
  · exact closure_minimal (fun _ h => h.1) (isClosed_rawComplexGraph n τ)
  · intro p hp
    let q : rawComplexGraph n τ := ⟨p,hp⟩
    have ht := (tendsto_subtype_rng.mp (rawComplexGraphCoreApprox_tendsto n τ q))
    exact mem_closure_of_tendsto ht (Eventually.of_forall (fun a =>
      ⟨(rawComplexGraphCoreApprox n τ q a).property,rawComplexGraphCoreApprox_input_mem_core n τ q a⟩))

end
end GaloisForLFunctions.HTGeometry.FokasLenells
