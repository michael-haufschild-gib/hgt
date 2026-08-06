import GaloisForLFunctions.HTGeometry.SiteFactorInteractionCoordinates
import GaloisForLFunctions.HTGeometry.DisjointPacketSpectrum
import GaloisForLFunctions.HTGeometry.SiteFactorSubsystemTransport

/-!
# Splitting a subsystem Hamiltonian over its components

Every admissible interaction term of a graph is supported on a single site or on
one interaction edge, so a term contained in a vertex subset is contained in one
connected component of the induced graph.  Consequently the Hamiltonian read by
a vertex subset is the sum of the Hamiltonians read by the components, and those
act on pairwise disjoint site packets.

The splitting is stated for an arbitrary family of pairwise disjoint packets
covering the admissible terms, so that the graph-theoretic input — that an
induced edge joins vertices of the same component — enters only once.
-/

open scoped Matrix BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
    (A : V → Type*) [∀ v, Fintype (A v)] [∀ v, DecidableEq (A v)]

variable {A}

theorem nonempty_of_mem_interactionPackets {G : SimpleGraph V}
    [DecidableRel G.Adj] {P : Finset V} (hP : P ∈ interactionPackets G) :
    P.Nonempty := by
  rcases Finset.mem_union.1 hP with hsingle | hpair
  · obtain ⟨v, -, rfl⟩ := Finset.mem_image.1 hsingle
    exact Finset.singleton_nonempty v
  · obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hpair
    exact Finset.insert_nonempty _ _

variable (A)

/-- Hamiltonian read by a vertex subset from the ambient interaction
parameters. -/
def subsystemHamiltonian (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (p : Fin (interactionCoordinateCount A G) → ℝ) :
    Matrix (∀ v, A v) (∀ v, A v) ℂ :=
  liftLocalMatrix S (realAffineMatrix 0 (restrictedGeneratorFin A G S) p)

theorem subsystemHamiltonian_eq_sum [∀ v, Nonempty (A v)]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V)
    (p : Fin (interactionCoordinateCount A G) → ℝ) :
    subsystemHamiltonian A G S p =
      ∑ i ∈ Finset.univ.filter
          (fun i => ((interactionCoordinateEquiv A G).symm i).1.1 ⊆ S),
        p i • ambientGeneratorFin A G i :=
  liftLocalMatrix_realAffineMatrix_restricted A G S p

/-- **Component splitting of a subsystem Hamiltonian.**  If a family of
pairwise disjoint packets inside a vertex subset absorbs every admissible
interaction term of that subset, then the subsystem Hamiltonian is the sum of
the Hamiltonians of those packets. -/
theorem subsystemHamiltonian_eq_sum_packets [∀ v, Nonempty (A v)]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V)
    {C : Type*} [Fintype C] [DecidableEq C] (block : C → Finset V)
    (hsub : ∀ c, block c ⊆ S)
    (hdisj : ∀ c d, c ≠ d → Disjoint (block c) (block d))
    (hcover : ∀ P ∈ interactionPackets G, P ⊆ S → ∃ c, P ⊆ block c)
    (p : Fin (interactionCoordinateCount A G) → ℝ) :
    subsystemHamiltonian A G S p =
      ∑ c, subsystemHamiltonian A G (block c) p := by
  classical
  simp only [subsystemHamiltonian_eq_sum]
  have hfilter :
      Finset.univ.filter
          (fun i => ((interactionCoordinateEquiv A G).symm i).1.1 ⊆ S) =
        Finset.univ.biUnion (fun c =>
          Finset.univ.filter
            (fun i => ((interactionCoordinateEquiv A G).symm i).1.1 ⊆
              block c)) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_biUnion]
    constructor
    · intro hi
      obtain ⟨c, hc⟩ := hcover _
        ((interactionCoordinateEquiv A G).symm i).1.2 hi
      exact ⟨c, hc⟩
    · rintro ⟨c, hc⟩
      exact hc.trans (hsub c)
  rw [hfilter, Finset.sum_biUnion]
  intro c _ d _ hcd
  refine Finset.disjoint_left.2 fun i hi hi' => ?_
  have hic := (Finset.mem_filter.1 hi).2
  have hid := (Finset.mem_filter.1 hi').2
  obtain ⟨v, hv⟩ := nonempty_of_mem_interactionPackets
    ((interactionCoordinateEquiv A G).symm i).1.2
  exact Finset.disjoint_left.1 (hdisj c d hcd) (hic hv) (hid hv)

/-- Block of the subsystem Hamiltonian, living on the subsystem carrier. -/
def subsystemBlock (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V)
    (p : Fin (interactionCoordinateCount A G) → ℝ) :
    Matrix (LocalConfiguration A S) (LocalConfiguration A S) ℂ :=
  realAffineMatrix 0 (restrictedGeneratorFin A G S) p

theorem subsystemBlock_isHermitian (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (p : Fin (interactionCoordinateCount A G) → ℝ) :
    (subsystemBlock A G S p).IsHermitian :=
  realAffineMatrix_isHermitian 0 (restrictedGeneratorFin A G S)
    Matrix.isHermitian_zero (restrictedGeneratorFin_isHermitian A G S) p

theorem subsystemHamiltonian_eq_lift (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (p : Fin (interactionCoordinateCount A G) → ℝ) :
    subsystemHamiltonian A G S p =
      liftLocalMatrix S (subsystemBlock A G S p) := rfl

omit [Fintype V] [∀ v, DecidableEq (A v)] in
theorem card_localConfiguration (T : Finset V) :
    Fintype.card (LocalConfiguration A T) = ∏ v ∈ T, Fintype.card (A v) := by
  classical
  rw [Fintype.card_pi]
  exact Finset.prod_attach T (fun v => Fintype.card (A v))

/-- **Temporal rank of a subsystem Hamiltonian.**  Once the admissible terms of
a vertex subset are absorbed by pairwise disjoint packets whose spectra are
mutually projectively independent, the temporal rank of the subsystem
Hamiltonian is the sum of the packet ranks. -/
theorem anchoredTemporalRank_subsystemHamiltonian [∀ v, Nonempty (A v)]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V)
    {C : Type*} [Fintype C] [DecidableEq C] (block : C → Finset V)
    (hsub : ∀ c, block c ⊆ S)
    (hdisj : ∀ c d, c ≠ d → Disjoint (block c) (block d))
    (hcover : ∀ P ∈ interactionPackets G, P ⊆ S → ∃ c, P ⊆ block c)
    (p : Fin (interactionCoordinateCount A G) → ℝ)
    (hindep : ComponentProjectivelyIndependent
      (fun c => (subsystemBlock_isHermitian A G (block c) p).eigenvalues))
    (hHerm : (subsystemHamiltonian A G S p).IsHermitian)
    (r : ∀ v, A v) :
    anchoredTemporalRank hHerm.eigenvalues r =
      ∑ c, ((∏ v ∈ block c, Fintype.card (A v)) - 1) := by
  classical
  have hsplit : subsystemHamiltonian A G S p =
      ∑ c, liftLocalMatrix (block c) (subsystemBlock A G (block c) p) := by
    rw [subsystemHamiltonian_eq_sum_packets A G S block hsub hdisj hcover p]
    rfl
  have hsumHerm := isHermitian_sum_liftLocalMatrix block
    (fun c => subsystemBlock A G (block c) p)
    (fun c => subsystemBlock_isHermitian A G (block c) p) Finset.univ
  have heigen : hHerm.eigenvalues = hsumHerm.eigenvalues := by
    apply (Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff hHerm
      hsumHerm).2
    rw [hsplit]
  rw [heigen, anchoredTemporalRank_sum_liftLocalMatrix block hdisj
    (fun c => subsystemBlock A G (block c) p)
    (fun c => subsystemBlock_isHermitian A G (block c) p) hindep r]
  simp only [card_localConfiguration]

/-! ### The connected components of an induced subsystem -/

variable {A}

/-- Interaction graph induced on a vertex subset, on the subtype of that
subset. -/
def inducedSubsystemGraph (G : SimpleGraph V) (S : Finset V) :
    SimpleGraph {v : V // v ∈ S} :=
  G.comap (Function.Embedding.subtype (fun v : V => v ∈ S))

/-- Ambient sites of the connected component of one subsystem site. -/
noncomputable def sitePacketOf (G : SimpleGraph V) (S : Finset V)
    (v : {x : V // x ∈ S}) : Finset V :=
  subsystemPacketImage
    (((inducedSubsystemGraph G S).connectedComponentMk v).supp.toFinite.toFinset)

/-- The connected components of an induced subsystem, as ambient site
packets. -/
noncomputable def componentPackets (G : SimpleGraph V) (S : Finset V) :
    Finset (Finset V) :=
  S.attach.image (sitePacketOf G S)

theorem sitePacketOf_subset (G : SimpleGraph V) (S : Finset V)
    (v : {x : V // x ∈ S}) : sitePacketOf G S v ⊆ S :=
  subsystemPacketImage_subset _

theorem mem_sitePacketOf_iff (G : SimpleGraph V) (S : Finset V)
    (v : {x : V // x ∈ S}) (x : V) :
    x ∈ sitePacketOf G S v ↔ ∃ y : {x : V // x ∈ S},
      (inducedSubsystemGraph G S).connectedComponentMk y =
        (inducedSubsystemGraph G S).connectedComponentMk v ∧ y.1 = x := by
  rw [sitePacketOf, subsystemPacketImage]
  simp [Set.Finite.mem_toFinset, SimpleGraph.ConnectedComponent.mem_supp_iff]

theorem mem_sitePacketOf_of_component (G : SimpleGraph V) (S : Finset V)
    {v w : {x : V // x ∈ S}}
    (h : (inducedSubsystemGraph G S).connectedComponentMk w =
      (inducedSubsystemGraph G S).connectedComponentMk v) :
    w.1 ∈ sitePacketOf G S v :=
  (mem_sitePacketOf_iff G S v w.1).2 ⟨w, h, rfl⟩

theorem self_mem_sitePacketOf (G : SimpleGraph V) (S : Finset V)
    (v : {x : V // x ∈ S}) : v.1 ∈ sitePacketOf G S v :=
  mem_sitePacketOf_of_component G S rfl

theorem sitePacketOf_eq_of_mem (G : SimpleGraph V) (S : Finset V)
    {v w : {x : V // x ∈ S}} (h : w.1 ∈ sitePacketOf G S v) :
    sitePacketOf G S w = sitePacketOf G S v := by
  obtain ⟨y, hy, hyw⟩ := (mem_sitePacketOf_iff G S v w.1).1 h
  have hcomp : (inducedSubsystemGraph G S).connectedComponentMk w =
      (inducedSubsystemGraph G S).connectedComponentMk v := by
    rw [show w = y from Subtype.ext hyw.symm]
    exact hy
  ext x
  rw [mem_sitePacketOf_iff, mem_sitePacketOf_iff]
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z, hz.trans hcomp, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z, hz.trans hcomp.symm, rfl⟩

theorem componentPackets_subset (G : SimpleGraph V) (S : Finset V)
    {P : Finset V} (hP : P ∈ componentPackets G S) : P ⊆ S := by
  obtain ⟨v, -, hv⟩ := Finset.mem_image.1 hP
  rw [← hv]
  exact sitePacketOf_subset G S v

theorem componentPackets_disjoint (G : SimpleGraph V) (S : Finset V)
    {P Q : Finset V} (hP : P ∈ componentPackets G S)
    (hQ : Q ∈ componentPackets G S) (hPQ : P ≠ Q) : Disjoint P Q := by
  classical
  obtain ⟨v, -, hv⟩ := Finset.mem_image.1 hP
  obtain ⟨w, -, hw⟩ := Finset.mem_image.1 hQ
  subst hv
  subst hw
  refine Finset.disjoint_left.2 fun x hxv hxw => ?_
  have hxS : x ∈ S := sitePacketOf_subset G S v hxv
  have h1 : sitePacketOf G S ⟨x, hxS⟩ = sitePacketOf G S v :=
    sitePacketOf_eq_of_mem G S (v := v) (w := ⟨x, hxS⟩) hxv
  have h2 : sitePacketOf G S ⟨x, hxS⟩ = sitePacketOf G S w :=
    sitePacketOf_eq_of_mem G S (v := w) (w := ⟨x, hxS⟩) hxw
  exact hPQ (h1.symm.trans h2)

/-- **Admissible terms of a subsystem lie in one component.** -/
theorem componentPackets_cover (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) {P : Finset V} (hP : P ∈ interactionPackets G)
    (hPS : P ⊆ S) :
    ∃ Q ∈ componentPackets G S, P ⊆ Q := by
  classical
  rcases Finset.mem_union.1 hP with hsingle | hpair
  · obtain ⟨u, -, hu⟩ := Finset.mem_image.1 hsingle
    have huP : u ∈ P := by
      rw [← hu]
      exact Finset.mem_singleton_self u
    have huS : u ∈ S := hPS huP
    refine ⟨sitePacketOf G S ⟨u, huS⟩,
      Finset.mem_image_of_mem _ (Finset.mem_attach _ _), ?_⟩
    intro x hx
    rw [← hu, Finset.mem_singleton] at hx
    rw [hx]
    exact self_mem_sitePacketOf G S ⟨u, huS⟩
  · obtain ⟨q, hq, hqP⟩ := Finset.mem_image.1 hpair
    have hadj : G.Adj q.1 q.2 := (Finset.mem_filter.1 hq).2
    have h1P : q.1 ∈ P := by
      rw [← hqP]
      exact Finset.mem_insert_self _ _
    have h2P : q.2 ∈ P := by
      rw [← hqP]
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    have h1S : q.1 ∈ S := hPS h1P
    have h2S : q.2 ∈ S := hPS h2P
    refine ⟨sitePacketOf G S ⟨q.1, h1S⟩,
      Finset.mem_image_of_mem _ (Finset.mem_attach _ _), ?_⟩
    intro x hx
    rw [← hqP] at hx
    rcases Finset.mem_insert.1 hx with rfl | hx
    · exact self_mem_sitePacketOf G S ⟨q.1, h1S⟩
    · rw [Finset.mem_singleton] at hx
      subst hx
      refine mem_sitePacketOf_of_component G S
        (v := ⟨q.1, h1S⟩) (w := ⟨q.2, h2S⟩) ?_
      refine SimpleGraph.ConnectedComponent.sound ?_
      exact (SimpleGraph.Adj.symm (show (inducedSubsystemGraph G S).Adj
        ⟨q.1, h1S⟩ ⟨q.2, h2S⟩ from hadj)).reachable

/-- Sites of a component packet are the vertices of that component. -/
def componentPacketEquiv (G : SimpleGraph V) (S : Finset V)
    (v : {x : V // x ∈ S}) :
    ((inducedSubsystemGraph G S).connectedComponentMk v).supp ≃
      {x : V // x ∈ sitePacketOf G S v} where
  toFun w := ⟨w.1.1, (mem_sitePacketOf_iff G S v w.1.1).2
    ⟨w.1, SimpleGraph.ConnectedComponent.mem_supp_iff _ _ |>.1 w.2, rfl⟩⟩
  invFun x :=
    ⟨⟨x.1, sitePacketOf_subset G S v x.2⟩, by
      obtain ⟨y, hy, hyx⟩ := (mem_sitePacketOf_iff G S v x.1).1 x.2
      rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
      rw [show (⟨x.1, sitePacketOf_subset G S v x.2⟩ :
        {x : V // x ∈ S}) = y from Subtype.ext hyx.symm]
      exact hy⟩
  left_inv w := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv x := by
    apply Subtype.ext
    rfl

/-- **The induced network on a component is connected.** -/
theorem connected_induce_sitePacketOf (G : SimpleGraph V) (S : Finset V)
    (v : {x : V // x ∈ S}) :
    (G.comap (Function.Embedding.subtype
      (fun x : V => x ∈ sitePacketOf G S v))).Connected := by
  classical
  have hbase :
      (SimpleGraph.induce
        ((inducedSubsystemGraph G S).connectedComponentMk v).supp
        (inducedSubsystemGraph G S)).Connected :=
    (SimpleGraph.ConnectedComponent.maximal_connected_induce_supp
      ((inducedSubsystemGraph G S).connectedComponentMk v)).1
  refine (SimpleGraph.Iso.connected_iff
    (G := SimpleGraph.induce
      ((inducedSubsystemGraph G S).connectedComponentMk v).supp
      (inducedSubsystemGraph G S))
    (H := G.comap (Function.Embedding.subtype
      (fun x : V => x ∈ sitePacketOf G S v)))
    ⟨componentPacketEquiv G S v, ?_⟩).1 hbase
  intro a b
  exact Iff.rfl

variable (A)

/-- **Equation (5).**  For a coefficient vector whose component spectra are
mutually projectively independent, the temporal rank read by a vertex subset is
the sum, over the connected components of the induced graph, of the component
tensor dimension minus one. -/
theorem anchoredTemporalRank_subsystemHamiltonian_components
    [∀ v, Nonempty (A v)] (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (p : Fin (interactionCoordinateCount A G) → ℝ)
    (hindep : ComponentProjectivelyIndependent
      (fun c : {P : Finset V // P ∈ componentPackets G S} =>
        (subsystemBlock_isHermitian A G c.1 p).eigenvalues))
    (hHerm : (subsystemHamiltonian A G S p).IsHermitian)
    (r : ∀ v, A v) :
    anchoredTemporalRank hHerm.eigenvalues r =
      ∑ c ∈ componentPackets G S,
        ((∏ v ∈ c, Fintype.card (A v)) - 1) := by
  classical
  have hmain := anchoredTemporalRank_subsystemHamiltonian A G S
    (fun c : {P : Finset V // P ∈ componentPackets G S} => c.1)
    (fun c => componentPackets_subset G S c.2)
    (fun c d hcd => componentPackets_disjoint G S c.2 d.2
      (fun h => hcd (Subtype.ext h)))
    (fun P hP hPS => by
      obtain ⟨Q, hQ, hPQ⟩ := componentPackets_cover G S hP hPS
      exact ⟨⟨Q, hQ⟩, hPQ⟩)
    p hindep hHerm r
  rw [hmain]
  exact Finset.sum_attach (componentPackets G S)
    (fun c => (∏ v ∈ c, Fintype.card (A v)) - 1)

end

end GaloisForLFunctions.HTGeometry
