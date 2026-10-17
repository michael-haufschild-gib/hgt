import GaloisForLFunctions.RHTower.PrimeBurnolAccretiveSymbol

/-! # Exact closure and maximality of the literal prime graph -/

open Complex Set Filter Topology
noncomputable section
namespace RHTower.BurnolAccretiveSymbol
open GaloisForLFunctions.HTGeometry _root_.HTGeometry
variable (ψ : BurnolAccretiveSymbol)

def primeGraphSpan : Submodule ℂ (BurnolHalfLineL2 × BurnolHalfLineL2) :=
  Submodule.span ℂ (Set.range (fun p : Nat.Primes =>
    (primeLogCriticalLaplaceFeatureL2 p,
      -ψ (Real.log (p : ℝ)) • primeLogCriticalLaplaceFeatureL2 p)))

def graph : Submodule ℂ (BurnolHalfLineL2 × BurnolHalfLineL2) :=
  ψ.primeGraphSpan.topologicalClosure

def resolventGraphMap : BurnolHalfLineL2 →L[ℂ] (BurnolHalfLineL2 × BurnolHalfLineL2) :=
  ψ.resolvent.prod (ψ.resolvent-1)

private theorem resolventFn_identity {z : ℂ} (hz : 0 < z.re) :
    ψ.resolventFn z - 1 = ψ.resolventFn z * -ψ z := by
  rw [resolventFn]
  field_simp [ψ.one_add_ne_zero hz]
  ring

private theorem resolventGraphMap_prime (p : Nat.Primes) :
    ψ.resolventGraphMap (primeLogCriticalLaplaceFeatureL2 p) =
      ψ.resolventFn (Real.log (p : ℝ)) •
        (primeLogCriticalLaplaceFeatureL2 p,
          -ψ (Real.log (p : ℝ)) • primeLogCriticalLaplaceFeatureL2 p) := by
  apply Prod.ext
  · exact ψ.resolvent_prime p
  · change ψ.resolvent (primeLogCriticalLaplaceFeatureL2 p) -
      primeLogCriticalLaplaceFeatureL2 p = _
    rw [ψ.resolvent_prime]
    change _ = ψ.resolventFn (Real.log (p : ℝ)) •
      (-ψ (Real.log (p : ℝ)) • primeLogCriticalLaplaceFeatureL2 p)
    rw [smul_smul, ← ψ.resolventFn_identity (Real.log_pos (by exact_mod_cast p.property.one_lt)),
      sub_smul, one_smul]

private theorem primeGraphSpan_le : ψ.primeGraphSpan ≤ cayleyResolventGraph ψ.resolvent := by
  apply Submodule.span_le.mpr
  rintro _ ⟨p, rfl⟩
  change ψ.resolvent (primeLogCriticalLaplaceFeatureL2 p -
    -ψ (Real.log (p : ℝ)) • primeLogCriticalLaplaceFeatureL2 p) = _
  rw [neg_smul, sub_neg_eq_add, map_add, map_smul, ψ.resolvent_prime, smul_smul]
  rw [← add_smul]
  have he : ψ.resolventFn (Real.log (p : ℝ)) +
      ψ (Real.log (p : ℝ)) * ψ.resolventFn (Real.log (p : ℝ)) = 1 := by
    simpa only [resolventFn, add_mul, one_mul] using
      mul_inv_cancel₀ (ψ.one_add_ne_zero (Real.log_pos (by exact_mod_cast p.property.one_lt)))
  rw [he, one_smul]

/-- Literal finite-prime graph closure is exactly the bounded-resolvent graph. -/
theorem graph_eq_cayley : ψ.graph = cayleyResolventGraph ψ.resolvent := by
  apply le_antisymm
  · exact ψ.primeGraphSpan.topologicalClosure_minimal ψ.primeGraphSpan_le
      (isClosed_cayleyResolventGraph ψ.resolvent)
  · let S := ψ.graph.comap ψ.resolventGraphMap.toLinearMap
    have hclosed : IsClosed (S : Set BurnolHalfLineL2) :=
      ψ.primeGraphSpan.isClosed_topologicalClosure.preimage ψ.resolventGraphMap.continuous
    have hspan : Submodule.span ℂ (Set.range primeLogCriticalLaplaceFeatureL2) ≤ S := by
      apply Submodule.span_le.mpr
      rintro _ ⟨p, rfl⟩
      change ψ.resolventGraphMap (primeLogCriticalLaplaceFeatureL2 p) ∈ ψ.graph
      rw [ψ.resolventGraphMap_prime]
      apply ψ.graph.smul_mem
      exact ψ.primeGraphSpan.le_topologicalClosure (Submodule.subset_span ⟨p, rfl⟩)
    have hall : ∀ w : BurnolHalfLineL2, w ∈ S := by
      have h := closure_minimal hspan hclosed
      rw [dense_primeLogCriticalLaplaceFeature_span.closure_eq] at h
      exact fun w => h (Set.mem_univ w)
    rintro ⟨u,v⟩ huv
    obtain ⟨w, rfl, rfl⟩ := (cayleyResolventGraph_mem_iff ψ.resolvent u v).mp huv
    exact hall w

theorem graph_mem_iff (u v : BurnolHalfLineL2) :
    (u,v) ∈ ψ.graph ↔ ψ.resolvent (u-v) = u := by
  rw [ψ.graph_eq_cayley]
  rfl

theorem graph_mem_iff_param (u v : BurnolHalfLineL2) :
    (u,v) ∈ ψ.graph ↔ ∃ w, u = ψ.resolvent w ∧ v = ψ.resolvent w-w := by
  rw [ψ.graph_eq_cayley]
  exact cayleyResolventGraph_mem_iff _ _ _

theorem graph_isClosed : IsClosed (ψ.graph : Set (BurnolHalfLineL2 × BurnolHalfLineL2)) :=
  ψ.primeGraphSpan.isClosed_topologicalClosure

theorem graph_singleValued {u v w : BurnolHalfLineL2}
    (hv : (u,v) ∈ ψ.graph) (hw : (u,w) ∈ ψ.graph) : v = w := by
  rw [ψ.graph_eq_cayley] at hv hw
  exact cayleyResolventGraph_singleValued _ ψ.resolvent_injective hv hw

theorem graph_domain : {u : BurnolHalfLineL2 | ∃ v, (u,v) ∈ ψ.graph} =
    Set.range ψ.resolvent := by
  ext u
  simp only [Set.mem_setOf_eq, ψ.graph_mem_iff_param, Set.mem_range]
  constructor
  · rintro ⟨v,w,hu,_⟩
    exact ⟨w,hu.symm⟩
  · rintro ⟨w,rfl⟩
    exact ⟨_,w,rfl,rfl⟩

theorem graph_dense_domain : Dense {u : BurnolHalfLineL2 | ∃ v, (u,v) ∈ ψ.graph} := by
  rw [ψ.graph_domain]
  exact ψ.resolvent_denseRange

theorem graph_dissipative {u v : BurnolHalfLineL2} (h : (u,v) ∈ ψ.graph) :
    (inner ℂ u v).re ≤ 0 := by
  rw [ψ.graph_eq_cayley] at h
  exact cayleyResolventGraph_dissipative _ ψ.norm_cayley_le h

theorem graph_maximal_dissipative (S : Submodule ℂ (BurnolHalfLineL2 × BurnolHalfLineL2))
    (hGS : ψ.graph ≤ S) (hS : ∀ p ∈ S, (inner ℂ p.1 p.2).re ≤ 0) : S = ψ.graph := by
  apply le_antisymm _ hGS
  rw [ψ.graph_eq_cayley] at hGS ⊢
  exact le_cayleyResolventGraph_of_dissipative_extension _ S hGS hS

theorem graph_feature (z : ℂ) (hz : 0 < z.re) :
    (burnolComplexFeature z hz, -ψ z • burnolComplexFeature z hz) ∈ ψ.graph := by
  rw [ψ.graph_mem_iff, neg_smul, sub_neg_eq_add, map_add, map_smul, ψ.resolvent_feature,
    smul_smul, ← add_smul]
  have he : ψ.resolventFn z + ψ z * ψ.resolventFn z = 1 := by
    simpa only [resolventFn, add_mul, one_mul] using mul_inv_cancel₀ (ψ.one_add_ne_zero hz)
  rw [he, one_smul]

end RHTower.BurnolAccretiveSymbol
