import GaloisForLFunctions.HTGeometry.HypergraphLocalHamiltonian
import GaloisForLFunctions.HTGeometry.SubsystemComponentDecomposition

/-!
# Component factorization of a hyperedge-local Hamiltonian

No admissible term of an interaction hypergraph crosses two connected
components of its two-section graph: a one-site term lives at one site, and a
hyperedge is pairwise adjacent in the two-section graph, hence lies inside a
single component.  Consequently every hyperedge-local Hamiltonian is the sum of
Hamiltonians supported on pairwise disjoint component packets, and its anchored
projective rational spectral rank is the sum of the component ranks as soon as
the component gap modules are mutually transverse.

This file constructs the component packets, the ambient component-local
Hamiltonian spaces, the exact block decomposition, and the resulting rank
formula

```
τ(H) = ∑_{C ∈ π₀(𝔥)} (D_C - 1),      D_C = ∏_{v ∈ C} q_v.
```
-/

open Set SimpleGraph MeasureTheory Topology Filter
open scoped Matrix BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### Connected components of the two-section graph -/

/-- Site packet of the two-section connected component of one site. -/
def hypergraphComponentOf (𝔥 : Finset (Finset V)) (v : V) : Finset V :=
  sitePacketOf (twoSection 𝔥) Finset.univ ⟨v, Finset.mem_univ v⟩

/-- The connected components of the two-section graph, as site packets. -/
def hypergraphComponents (𝔥 : Finset (Finset V)) : Finset (Finset V) :=
  componentPackets (twoSection 𝔥) Finset.univ

theorem hypergraphComponentOf_mem (𝔥 : Finset (Finset V)) (v : V) :
    hypergraphComponentOf 𝔥 v ∈ hypergraphComponents 𝔥 :=
  Finset.mem_image_of_mem _ (Finset.mem_attach _ _)

theorem self_mem_hypergraphComponentOf (𝔥 : Finset (Finset V)) (v : V) :
    v ∈ hypergraphComponentOf 𝔥 v :=
  self_mem_sitePacketOf (twoSection 𝔥) Finset.univ ⟨v, Finset.mem_univ v⟩

theorem hypergraphComponents_disjoint (𝔥 : Finset (Finset V))
    {P Q : Finset V} (hP : P ∈ hypergraphComponents 𝔥)
    (hQ : Q ∈ hypergraphComponents 𝔥) (hPQ : P ≠ Q) : Disjoint P Q :=
  componentPackets_disjoint (twoSection 𝔥) Finset.univ hP hQ hPQ

omit [DecidableEq V] in
theorem inducedSubsystemGraph_univ_adj {𝔥 : Finset (Finset V)}
    {u w : {x : V // x ∈ (Finset.univ : Finset V)}} :
    (inducedSubsystemGraph (twoSection 𝔥) Finset.univ).Adj u w ↔
      (twoSection 𝔥).Adj u.1 w.1 := Iff.rfl

theorem mem_hypergraphComponentOf_of_adj {𝔥 : Finset (Finset V)} {u w : V}
    (h : (twoSection 𝔥).Adj w u) : w ∈ hypergraphComponentOf 𝔥 u :=
  mem_sitePacketOf_of_component (twoSection 𝔥) Finset.univ
    (v := ⟨u, Finset.mem_univ u⟩) (w := ⟨w, Finset.mem_univ w⟩)
    (SimpleGraph.ConnectedComponent.sound
      (SimpleGraph.Adj.reachable
        (inducedSubsystemGraph_univ_adj.2 h)))

/-- **A hyperedge lies inside one component.** -/
theorem hyperedge_subset_hypergraphComponentOf {𝔥 : Finset (Finset V)}
    {X : Finset V} (hX : X ∈ 𝔥) {u : V} (hu : u ∈ X) :
    X ⊆ hypergraphComponentOf 𝔥 u := by
  intro w hw
  by_cases hwu : w = u
  · subst hwu
    exact self_mem_hypergraphComponentOf 𝔥 w
  · exact mem_hypergraphComponentOf_of_adj
      (twoSection_adj_of_mem_hyperedge hX hw hu hwu)

/-- The site packets of the two-section components are connected networks. -/
theorem connected_comap_hypergraphComponentOf (𝔥 : Finset (Finset V))
    (v : V) :
    ((twoSection 𝔥).comap (Function.Embedding.subtype
      (fun x : V => x ∈ hypergraphComponentOf 𝔥 v))).Connected :=
  connected_induce_sitePacketOf (twoSection 𝔥) Finset.univ
    ⟨v, Finset.mem_univ v⟩

/-- Index type of the two-section components. -/
abbrev HypergraphComponent (𝔥 : Finset (Finset V)) : Type _ :=
  {P : Finset V // P ∈ hypergraphComponents 𝔥}

/-- **The two-section components cover the site set.** -/
theorem biUnion_hypergraphComponents (𝔥 : Finset (Finset V)) :
    (hypergraphComponents 𝔥).biUnion id = Finset.univ := by
  classical
  refine Finset.eq_univ_of_forall fun v => ?_
  exact Finset.mem_biUnion.2 ⟨hypergraphComponentOf 𝔥 v,
    hypergraphComponentOf_mem 𝔥 v, self_mem_hypergraphComponentOf 𝔥 v⟩

/-- **The two-section components partition the site set.**  Consequently the
product of the component tensor dimensions is the total tensor dimension. -/
theorem prod_hypergraphComponents_prod (𝔥 : Finset (Finset V)) (f : V → ℕ) :
    (∏ P ∈ hypergraphComponents 𝔥, ∏ v ∈ P, f v) = ∏ v, f v := by
  classical
  have hdisj : (hypergraphComponents 𝔥 : Set (Finset V)).PairwiseDisjoint id :=
    fun P hP Q hQ hPQ => hypergraphComponents_disjoint 𝔥 hP hQ hPQ
  have hkey := Finset.prod_biUnion (s := hypergraphComponents 𝔥) (t := id)
    (f := f) hdisj
  rw [biUnion_hypergraphComponents 𝔥] at hkey
  exact hkey.symm

/-! ### Ambient component-local Hamiltonian spaces -/

variable (A : V → Type*) [∀ v, Fintype (A v)] [∀ v, DecidableEq (A v)]

/-- Hermitian one-site and hyperedge generators whose support lies inside a
prescribed site packet. -/
def componentLocalGenerator (𝔥 : Finset (Finset V)) (P : Finset V) :
    Set (Matrix (∀ v, A v) (∀ v, A v) ℂ) :=
  {H : Matrix (∀ v, A v) (∀ v, A v) ℂ | H.IsHermitian ∧
    ((∃ v ∈ P, IsSiteSupported {v} H) ∨ ∃ X ∈ 𝔥, X ⊆ P ∧ IsSiteSupported X H)}

/-- Hyperedge-local Hamiltonians whose admissible terms all lie inside one site
packet, read inside the ambient carrier. -/
def componentLocalSubmodule (𝔥 : Finset (Finset V)) (P : Finset V) :
    Submodule ℝ (Matrix (∀ v, A v) (∀ v, A v) ℂ) :=
  Submodule.span ℝ (componentLocalGenerator A 𝔥 P)

omit [Fintype V] [DecidableEq V] [∀ v, Fintype (A v)] [∀ v, DecidableEq (A v)] in
theorem componentLocalSubmodule_le_hypergraphLocalSubmodule
    (𝔥 : Finset (Finset V)) (P : Finset V) :
    componentLocalSubmodule A 𝔥 P ≤ hypergraphLocalSubmodule A 𝔥 := by
  refine Submodule.span_le.2 ?_
  rintro H ⟨hH, hcase⟩
  refine Submodule.subset_span ⟨hH, ?_⟩
  rcases hcase with ⟨v, -, hv⟩ | ⟨X, hX, -, hsupp⟩
  · exact Or.inl ⟨v, hv⟩
  · exact Or.inr ⟨X, hX, hsupp⟩

omit [Fintype V] [DecidableEq V] [∀ v, Fintype (A v)] [∀ v, DecidableEq (A v)] in
theorem componentLocalSubmodule_le_selfAdjoint (𝔥 : Finset (Finset V))
    (P : Finset V) :
    componentLocalSubmodule A 𝔥 P ≤
      selfAdjoint.submodule ℝ (Matrix (∀ v, A v) (∀ v, A v) ℂ) := by
  refine Submodule.span_le.2 ?_
  rintro H ⟨hH, -⟩
  exact hH

omit [Fintype V] [DecidableEq V] [∀ v, Fintype (A v)] [∀ v, DecidableEq (A v)] in
theorem isHermitian_of_mem_componentLocalSubmodule {𝔥 : Finset (Finset V)}
    {P : Finset V} {H : Matrix (∀ v, A v) (∀ v, A v) ℂ}
    (hH : H ∈ componentLocalSubmodule A 𝔥 P) : H.IsHermitian :=
  componentLocalSubmodule_le_selfAdjoint A 𝔥 P hH

omit [Fintype V] [DecidableEq V] [∀ v, Fintype (A v)] [∀ v, DecidableEq (A v)] in
/-- **Every component-local Hamiltonian is supported on its packet.** -/
theorem isSiteSupported_of_mem_componentLocalSubmodule
    {𝔥 : Finset (Finset V)} {P : Finset V}
    {H : Matrix (∀ v, A v) (∀ v, A v) ℂ}
    (hH : H ∈ componentLocalSubmodule A 𝔥 P) : IsSiteSupported P H := by
  induction hH using Submodule.span_induction with
  | mem X hX =>
      rcases hX.2 with ⟨v, hv, hsupp⟩ | ⟨Y, -, hYP, hsupp⟩
      · exact hsupp.mono (Finset.singleton_subset_iff.2 hv)
      · exact hsupp.mono hYP
  | zero => exact IsSiteSupported.zero P
  | add X Y _ _ hX hY => exact hX.add hY
  | smul c X _ hX => exact hX.smul c

/-! ### The exact component decomposition -/

omit [∀ v, Fintype (A v)] [∀ v, DecidableEq (A v)] in
/-- **Component splitting.**  Every hyperedge-local Hamiltonian is a finite sum
of Hamiltonians local to the two-section components. -/
theorem exists_componentDecomposition (𝔥 : Finset (Finset V)) [Nonempty V]
    {H : Matrix (∀ v, A v) (∀ v, A v) ℂ}
    (hH : H ∈ hypergraphLocalSubmodule A 𝔥) :
    ∃ f : HypergraphComponent 𝔥 → Matrix (∀ v, A v) (∀ v, A v) ℂ,
      (∀ c, f c ∈ componentLocalSubmodule A 𝔥 c.1) ∧ H = ∑ c, f c := by
  classical
  induction hH using Submodule.span_induction with
  | mem X hX =>
      obtain ⟨hHerm, hcase⟩ := hX
      obtain ⟨c₀, hmem⟩ :
          ∃ c₀ : HypergraphComponent 𝔥, X ∈ componentLocalGenerator A 𝔥 c₀.1 := by
        rcases hcase with ⟨v, hsupp⟩ | ⟨Y, hY, hsupp⟩
        · exact ⟨⟨hypergraphComponentOf 𝔥 v, hypergraphComponentOf_mem 𝔥 v⟩,
            hHerm, Or.inl ⟨v, self_mem_hypergraphComponentOf 𝔥 v, hsupp⟩⟩
        · rcases Finset.eq_empty_or_nonempty Y with rfl | ⟨u, hu⟩
          · obtain ⟨v₀⟩ := ‹Nonempty V›
            exact ⟨⟨hypergraphComponentOf 𝔥 v₀,
                hypergraphComponentOf_mem 𝔥 v₀⟩,
              hHerm, Or.inr ⟨∅, hY, Finset.empty_subset _, hsupp⟩⟩
          · exact ⟨⟨hypergraphComponentOf 𝔥 u, hypergraphComponentOf_mem 𝔥 u⟩,
              hHerm, Or.inr ⟨Y, hY,
                hyperedge_subset_hypergraphComponentOf hY hu, hsupp⟩⟩
      refine ⟨fun c => if c = c₀ then X else 0, fun c => ?_, ?_⟩
      · by_cases hc : c = c₀
        · subst hc
          show (if c = c then X else 0) ∈ componentLocalSubmodule A 𝔥 c.1
          rw [if_pos rfl]
          exact Submodule.subset_span hmem
        · simp only [if_neg hc]
          exact Submodule.zero_mem (componentLocalSubmodule A 𝔥 c.1)
      · simp
  | zero => exact ⟨0, fun c => Submodule.zero_mem _, by simp⟩
  | add X Y _ _ hX hY =>
      obtain ⟨f, hf, hfsum⟩ := hX
      obtain ⟨g, hg, hgsum⟩ := hY
      exact ⟨f + g, fun c => Submodule.add_mem _ (hf c) (hg c), by
        rw [hfsum, hgsum, ← Finset.sum_add_distrib]; rfl⟩
  | smul r X _ hX =>
      obtain ⟨f, hf, hfsum⟩ := hX
      exact ⟨r • f, fun c => Submodule.smul_mem _ r (hf c), by
        rw [hfsum, Finset.smul_sum]; rfl⟩

/-- **Component blocks.**  Every hyperedge-local Hamiltonian is the sum of
Hermitian blocks lifted from pairwise disjoint component packets. -/
theorem exists_hermitian_componentBlocks (𝔥 : Finset (Finset V)) [Nonempty V]
    [∀ v, Nonempty (A v)]
    {H : Matrix (∀ v, A v) (∀ v, A v) ℂ}
    (hH : H ∈ hypergraphLocalSubmodule A 𝔥) :
    ∃ B : ∀ c : HypergraphComponent 𝔥,
        Matrix (LocalConfiguration A c.1) (LocalConfiguration A c.1) ℂ,
      (∀ c, (B c).IsHermitian) ∧
        (∀ c, liftLocalMatrix c.1 (B c) ∈ componentLocalSubmodule A 𝔥 c.1) ∧
        H = ∑ c, liftLocalMatrix c.1 (B c) := by
  classical
  obtain ⟨f, hf, hfsum⟩ := exists_componentDecomposition A 𝔥 hH
  choose B hB using fun c =>
    exists_liftLocalMatrix_of_isSiteSupported
      (isSiteSupported_of_mem_componentLocalSubmodule A (hf c))
  refine ⟨B, fun c => ?_, fun c => ?_, ?_⟩
  · refine isHermitian_of_isHermitian_liftLocalMatrix c.1 ?_
    rw [← hB c]
    exact isHermitian_of_mem_componentLocalSubmodule A (hf c)
  · rw [← hB c]
    exact hf c
  · rw [hfsum]
    exact Finset.sum_congr rfl fun c _ => hB c

/-! ### The disconnected rank formula -/

/-- **Equation `(1)`.**  Once the component gap modules of a hyperedge-local
Hamiltonian are mutually projectively independent, its anchored projective
rational spectral rank is the sum over the two-section components of the
component tensor dimension minus one. -/
theorem anchoredTemporalRank_eq_sum_hypergraphComponents
    (𝔥 : Finset (Finset V)) [∀ v, Nonempty (A v)]
    (B : ∀ c : HypergraphComponent 𝔥,
      Matrix (LocalConfiguration A c.1) (LocalConfiguration A c.1) ℂ)
    (hB : ∀ c, (B c).IsHermitian)
    (hindep : ComponentProjectivelyIndependent (fun c => (hB c).eigenvalues))
    {H : Matrix (∀ v, A v) (∀ v, A v) ℂ} (hHerm : H.IsHermitian)
    (hsum : H = ∑ c, liftLocalMatrix c.1 (B c)) (r : ∀ v, A v) :
    anchoredTemporalRank hHerm.eigenvalues r =
      ∑ P ∈ hypergraphComponents 𝔥, ((∏ v ∈ P, Fintype.card (A v)) - 1) := by
  classical
  have hsumHerm := isHermitian_sum_liftLocalMatrix
    (fun c : HypergraphComponent 𝔥 => c.1) B hB Finset.univ
  have heigen : hHerm.eigenvalues = hsumHerm.eigenvalues := by
    apply (Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff hHerm
      hsumHerm).2
    rw [hsum]
  rw [heigen, anchoredTemporalRank_sum_liftLocalMatrix
    (fun c : HypergraphComponent 𝔥 => c.1)
    (fun c d hcd => hypergraphComponents_disjoint 𝔥 c.2 d.2
      (fun h => hcd (Subtype.ext h)))
    B hB hindep r]
  simp only [card_localConfiguration]
  exact Finset.sum_coe_sort (hypergraphComponents 𝔥)
    (fun P => (∏ v ∈ P, Fintype.card (A v)) - 1)

/-! ### Simplicity of the total spectrum -/

/-- **Transverse component gap modules force distinct total levels.** -/
theorem injective_finiteComponentSumEnergy_of_componentProjectivelyIndependent
    {C : Type*} [Fintype C] {I : C → Type*} [∀ c, Fintype (I c)]
    [∀ c, DecidableEq (I c)] {energy : ∀ c, I c → ℝ}
    (hindep : ComponentProjectivelyIndependent energy) :
    Function.Injective (finiteComponentSumEnergy energy) := by
  classical
  intro x y hxy
  funext c
  by_contra hne
  have hzero := hindep
    (fun c i => (if i = x c then 1 else 0) - if i = y c then 1 else 0)
    (fun c => by
      show (∑ i, ((if i = x c then (1 : ℤ) else 0) - if i = y c then 1 else 0)) = 0
      rw [Finset.sum_sub_distrib,
        Finset.sum_ite_eq' Finset.univ (x c) fun _ => (1 : ℤ),
        Finset.sum_ite_eq' Finset.univ (y c) fun _ => (1 : ℤ)]
      simp)
    (by
      have hexpand : ∀ (d : C) (i : I d),
          (((if i = x d then (1 : ℤ) else 0) - if i = y d then 1 else 0 : ℤ) : ℝ) *
              energy d i =
            (if i = x d then energy d i else 0) -
              if i = y d then energy d i else 0 := by
        intro d i
        by_cases h₁ : i = x d <;> by_cases h₂ : i = y d <;>
          simp [h₁, h₂, sub_mul, ite_mul]
      have hstep : ∀ d : C,
          (∑ i, (((if i = x d then (1 : ℤ) else 0) -
              if i = y d then 1 else 0 : ℤ) : ℝ) * energy d i) =
            energy d (x d) - energy d (y d) := by
        intro d
        rw [Finset.sum_congr rfl fun i _ => hexpand d i, Finset.sum_sub_distrib,
          Finset.sum_ite_eq' Finset.univ (x d) (energy d),
          Finset.sum_ite_eq' Finset.univ (y d) (energy d)]
        simp
      rw [Finset.sum_congr rfl fun d _ => hstep d, Finset.sum_sub_distrib]
      exact sub_eq_zero.2 hxy)
    c
  have hx := congrFun hzero (x c)
  rw [if_pos rfl, if_neg (fun h : x c = y c => hne h)] at hx
  simp at hx

/-- Total levels of a family of disjoint packets are distinct once the
component gap modules are transverse. -/
theorem injective_eigenvalues_sum_liftLocalMatrix_of_componentProjectivelyIndependent
    [∀ v, Nonempty (A v)] (𝔥 : Finset (Finset V))
    (B : ∀ c : HypergraphComponent 𝔥,
      Matrix (LocalConfiguration A c.1) (LocalConfiguration A c.1) ℂ)
    (hB : ∀ c, (B c).IsHermitian)
    (hindep : ComponentProjectivelyIndependent (fun c => (hB c).eigenvalues))
    {H : Matrix (∀ v, A v) (∀ v, A v) ℂ} (hHerm : H.IsHermitian)
    (hsum : H = ∑ c, liftLocalMatrix c.1 (B c)) :
    Function.Injective hHerm.eigenvalues := by
  classical
  have hsumHerm := isHermitian_sum_liftLocalMatrix
    (fun c : HypergraphComponent 𝔥 => c.1) B hB Finset.univ
  have heigen : hHerm.eigenvalues = hsumHerm.eigenvalues := by
    apply (Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff hHerm hsumHerm).2
    rw [hsum]
  have hrange := range_eigenvalues_sum_liftLocalMatrix
    (fun c : HypergraphComponent 𝔥 => c.1)
    (fun c d hcd => hypergraphComponents_disjoint 𝔥 c.2 d.2
      (fun h => hcd (Subtype.ext h)))
    B hB Finset.univ
  have hsumInj :
      Function.Injective
        (finiteComponentSumEnergy (fun c => (hB c).eigenvalues)) :=
    injective_finiteComponentSumEnergy_of_componentProjectivelyIndependent hindep
  have hcard :
      Fintype.card (∀ c : HypergraphComponent 𝔥, LocalConfiguration A c.1) =
        Fintype.card (∀ v, A v) := by
    rw [Fintype.card_pi, Fintype.card_pi]
    have hblocks : ∀ c : HypergraphComponent 𝔥,
        Fintype.card (LocalConfiguration A c.1) =
          ∏ v ∈ c.1, Fintype.card (A v) :=
      fun c => card_localConfiguration A c.1
    rw [Finset.prod_congr rfl fun c _ => hblocks c]
    rw [Finset.prod_coe_sort (hypergraphComponents 𝔥)
      (fun P => ∏ v ∈ P, Fintype.card (A v))]
    exact prod_hypergraphComponents_prod 𝔥 (fun v => Fintype.card (A v))
  have himage :
      (Finset.univ.image hsumHerm.eigenvalues) =
        Finset.univ.image
          (finiteComponentSumEnergy (fun c => (hB c).eigenvalues)) := by
    apply Finset.coe_injective
    rw [Finset.coe_image, Finset.coe_image, Finset.coe_univ, Finset.coe_univ,
      Set.image_univ, Set.image_univ]
    exact hrange
  have hcardImage :
      (Finset.univ.image hsumHerm.eigenvalues).card =
        Fintype.card (∀ v, A v) := by
    rw [himage, Finset.card_image_of_injective _ hsumInj, Finset.card_univ, hcard]
  have hinj : Set.InjOn hsumHerm.eigenvalues (Finset.univ : Finset (∀ v, A v)) := by
    refine Finset.card_image_iff.1 ?_
    rw [hcardImage, Finset.card_univ]
  rw [heigen]
  intro a b hab
  exact hinj (Finset.mem_univ a) (Finset.mem_univ b) hab

/-- **Equation `(1)` simplicity half.**  A hyperedge-local Hamiltonian with
transverse component gap modules has a simple spectrum. -/
theorem injective_eigenvalues_of_componentProjectivelyIndependent
    [∀ v, Nonempty (A v)] (𝔥 : Finset (Finset V))
    (B : ∀ c : HypergraphComponent 𝔥,
      Matrix (LocalConfiguration A c.1) (LocalConfiguration A c.1) ℂ)
    (hB : ∀ c, (B c).IsHermitian)
    (hindep : ComponentProjectivelyIndependent (fun c => (hB c).eigenvalues))
    {H : Matrix (∀ v, A v) (∀ v, A v) ℂ} (hHerm : H.IsHermitian)
    (hsum : H = ∑ c, liftLocalMatrix c.1 (B c)) :
    Function.Injective hHerm.eigenvalues :=
  injective_eigenvalues_sum_liftLocalMatrix_of_componentProjectivelyIndependent
    A 𝔥 B hB hindep hHerm hsum

end

end GaloisForLFunctions.HTGeometry
