import GaloisForLFunctions.RHTower.PrimeBurnolAccretiveIntegral

/-! # The complete derivative domain equals the literal prime graph closure -/

open Complex Set Filter Topology
noncomputable section
namespace RHTower.BurnolAccretiveSymbol
open GaloisForLFunctions.HTGeometry _root_.HTGeometry
variable (ψ : BurnolAccretiveSymbol)

private theorem evolution_eq_primitive_add {u v : BurnolHalfLineL2}
    (h : (u,v) ∈ ψ.graph) {s : ℝ} (hs : 0 ≤ s) :
    ψ.evolution s.toNNReal u = ψ.orbitPrimitive s v+u := by
  have hi := ψ.graph_orbit_integral h s.toNNReal
  rw [Real.coe_toNNReal s hs] at hi
  exact sub_eq_iff_eq_add.mp hi

theorem hasDerivWithinAt_of_graph {u v : BurnolHalfLineL2} (h : (u,v) ∈ ψ.graph) :
    HasDerivWithinAt (fun s : ℝ => ψ.evolution s.toNNReal u) v (Ioi 0) 0 := by
  have hd : HasDerivWithinAt (fun x : ℝ => ψ.orbitPrimitive x v+u) v (Ioi 0) 0 :=
    (ψ.orbitPrimitive_hasDerivAt_zero v).hasDerivWithinAt.add_const u
  apply hd.congr
  · intro s hs
    exact ψ.evolution_eq_primitive_add h (le_of_lt hs)
  · simp only [Real.toNNReal_zero, ψ.evolution_zero, one_apply_eq_self,
      ψ.orbitPrimitive_zero, zero_add]

/-- No other right-differentiable data lie outside the literal finite-prime graph closure. -/
theorem graph_of_hasDerivWithinAt {u v : BurnolHalfLineL2}
    (h : HasDerivWithinAt (fun s : ℝ => ψ.evolution s.toNNReal u) v (Ioi 0) 0) :
    (u,v) ∈ ψ.graph := by
  have hp : (ψ.resolvent u, ψ.resolvent u-u) ∈ ψ.graph :=
    (ψ.graph_mem_iff_param _ _).mpr ⟨u,rfl,rfl⟩
  have hd := ψ.hasDerivWithinAt_of_graph hp
  have hm := (ψ.resolvent.restrictScalars ℝ).hasFDerivAt.comp_hasDerivWithinAt 0 h
  have hc : HasDerivWithinAt (fun s : ℝ => ψ.evolution s.toNNReal (ψ.resolvent u))
      (ψ.resolvent v) (Ioi 0) 0 := by
    apply hm.congr
    · intro s _
      exact congrArg (fun A : BurnolHalfLineL2 →L[ℂ] BurnolHalfLineL2 => A u)
        (ψ.evolution_resolvent s.toNNReal)
    · exact congrArg (fun A : BurnolHalfLineL2 →L[ℂ] BurnolHalfLineL2 => A u)
        (ψ.evolution_resolvent (0 : ℝ).toNNReal)
  have he : ψ.resolvent v = ψ.resolvent u-u :=
    (uniqueDiffWithinAt_Ioi 0).eq_deriv (Ioi 0) hc hd
  rw [ψ.graph_mem_iff, map_sub, he]
  abel

/-- The full generator domain, with no core or source-admission premise. -/
theorem hasDerivWithinAt_iff_graph (u v : BurnolHalfLineL2) :
    HasDerivWithinAt (fun s : ℝ => ψ.evolution s.toNNReal u) v (Ioi 0) 0 ↔
      (u,v) ∈ ψ.graph :=
  ⟨ψ.graph_of_hasDerivWithinAt, ψ.hasDerivWithinAt_of_graph⟩

theorem differentiable_domain_eq_resolvent_range :
    {u : BurnolHalfLineL2 | ∃ v, HasDerivWithinAt
      (fun s : ℝ => ψ.evolution s.toNNReal u) v (Ioi 0) 0} = Set.range ψ.resolvent := by
  simp only [ψ.hasDerivWithinAt_iff_graph]
  exact ψ.graph_domain

/-- The literal prime actions determine a unique closed dissipative realization. -/
theorem existsUnique_closed_dissipative_prime_graph :
    ∃! S : Submodule ℂ (BurnolHalfLineL2 × BurnolHalfLineL2),
      IsClosed (S : Set (BurnolHalfLineL2 × BurnolHalfLineL2)) ∧
      (∀ p : Nat.Primes, (primeLogCriticalLaplaceFeatureL2 p,
        -ψ (Real.log (p : ℝ)) • primeLogCriticalLaplaceFeatureL2 p) ∈ S) ∧
      (∀ q ∈ S, (inner ℂ q.1 q.2).re ≤ 0) := by
  refine ⟨ψ.graph, ⟨ψ.graph_isClosed, ?_, ?_⟩, ?_⟩
  · intro p
    exact ψ.primeGraphSpan.le_topologicalClosure (Submodule.subset_span ⟨p,rfl⟩)
  · rintro ⟨u,v⟩ huv
    exact ψ.graph_dissipative huv
  · intro S hS
    apply ψ.graph_maximal_dissipative S _ hS.2.2
    apply ψ.primeGraphSpan.topologicalClosure_minimal _ hS.1
    apply Submodule.span_le.mpr
    rintro _ ⟨p,rfl⟩
    exact hS.2.1 p

end RHTower.BurnolAccretiveSymbol
