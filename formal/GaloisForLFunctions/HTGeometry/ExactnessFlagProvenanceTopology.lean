import Mathlib.Topology.Order.ScottTopology
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.Prod
import Mathlib.Tactic.Module
import Mathlib.Tactic.LinearCombination

/-!
# Provenance-exactness flag topology

An *exactness flag* on a module is a pair of submodules `B ≤ Z`: a boundary space inside a cycle
space.  Its spectral content is the quotient `Z / B`, and the two coordinates carry opposite
information variance.  Membership in the cycle space is a positive, directed-supremum accessible
test; nonmembership in the boundary space is a negative test.

This file equips the flag space with the mixed topology obtained by giving the boundary coordinate
the lower topology and the cycle coordinate the Scott topology, and proves:

* the negative tests `v ∉ B` generate exactly the lower topology on the submodule lattice, and the
  positive tests `v ∈ Z` generate exactly its Scott topology;
* the mixed topology is therefore the coarsest one making every such test open;
* the flag space is `T₀`, with specialization order `B ⊆ B'` together with `Z' ⊆ Z`;
* the framed survival locus `v ∈ Z ∧ v ∉ B` is open and detects a nonzero class in `Z / B`, and the
  dimension of that quotient is monotone along specialization;
* every invariant factoring through the cycle coordinate alone is constant on a whole fibre, so it
  cannot separate a flag from its falsely exact companion `(Z, Z)`;
* pullback of flags along a linear map is continuous, pushforward along an injective map is
  continuous, and pushforward along a coordinate projection of a plane over an infinite field is
  not.
-/

namespace GaloisForLFunctions.HTGeometry

open Set Topology TopologicalSpace

/-! ## Generators of the two lattice topologies -/

section Lattice

variable (R M : Type*) [Semiring R] [AddCommMonoid M] [Module R M]

/-- **Negative membership tests generate the lower topology.**  A principal upper set of the
submodule lattice is cut out by a single vector when the vector spans, and the complement of an
arbitrary principal upper set is the union of the negative tests at its members. -/
theorem lower_submodule_eq_generateFrom :
    Topology.lower (Submodule R M) =
      generateFrom {s | ∃ v : M, s = {B : Submodule R M | v ∉ B}} := by
  have hlow : Topology.lower (Submodule R M) =
      generateFrom {s | ∃ a : Submodule R M, (Ici a)ᶜ = s} := rfl
  rw [hlow]
  refine le_antisymm (le_generateFrom ?_) (le_generateFrom ?_)
  · rintro s ⟨v, rfl⟩
    letI : TopologicalSpace (Submodule R M) :=
      generateFrom {s | ∃ a : Submodule R M, (Ici a)ᶜ = s}
    have hset : {B : Submodule R M | v ∉ B} = (Ici (Submodule.span R {v}))ᶜ := by
      ext B
      simp [Submodule.span_singleton_le_iff_mem]
    rw [hset]
    exact isOpen_generateFrom_of_mem ⟨Submodule.span R {v}, rfl⟩
  · rintro s ⟨N, rfl⟩
    letI : TopologicalSpace (Submodule R M) :=
      generateFrom {s | ∃ v : M, s = {B : Submodule R M | v ∉ B}}
    have hset : ((Ici N)ᶜ : Set (Submodule R M)) =
        ⋃ v ∈ (N : Set M), {B : Submodule R M | v ∉ B} := by
      ext B
      simp only [mem_compl_iff, mem_Ici, mem_iUnion, mem_setOf_eq, exists_prop, SetLike.mem_coe]
      exact SetLike.not_le_iff_exists
    rw [hset]
    exact isOpen_biUnion fun v _ => isOpen_generateFrom_of_mem ⟨v, rfl⟩

/-- Scott openness in the submodule lattice, unfolded to its order content. -/
theorem isOpen_scott_submodule_iff {W : Set (Submodule R M)} :
    IsOpen[Topology.scott (Submodule R M) univ] W ↔ IsUpperSet W ∧ DirSupInacc W := by
  letI : TopologicalSpace (Submodule R M) := Topology.scott (Submodule R M) univ
  haveI : Topology.IsScott (Submodule R M) univ := ⟨rfl⟩
  show IsOpen W ↔ IsUpperSet W ∧ DirSupInacc W
  rw [Topology.IsScott.isOpen_iff_isUpperSet_and_dirSupInaccOn (D := univ), dirSupInaccOn_univ]

variable {R M}

/-- A principal upper set of the submodule lattice is Scott open: a vector of a directed supremum
already lies in one member of the family. -/
theorem isOpen_scott_Ici_span_singleton (v : M) :
    IsOpen[Topology.scott (Submodule R M) univ] {Z : Submodule R M | v ∈ Z} := by
  rw [isOpen_scott_submodule_iff]
  refine ⟨fun A B hAB hA => hAB hA, ?_⟩
  intro d hne hdir a hlub ha
  have hsup : sSup d = a := hlub.sSup_eq
  rw [← hsup] at ha
  obtain ⟨y, hyd, hy⟩ := (Submodule.mem_sSup_of_directed hne hdir).1 ha
  exact ⟨y, hyd, hy⟩

/-- Every Scott open set of submodules is a union of principal upper sets of finitely generated
submodules: a Scott open set is inaccessible by the directed family of finitely generated
submodules of any of its members. -/
theorem exists_finset_span_mem_of_scott {W : Set (Submodule R M)}
    (hInacc : DirSupInacc W) {Z : Submodule R M} (hZ : Z ∈ W) :
    ∃ s : Finset M, (↑s : Set M) ⊆ (Z : Set M) ∧ Submodule.span R (↑s : Set M) ∈ W := by
  classical
  set d : Set (Submodule R M) := {N : Submodule R M | N ≤ Z ∧ N.FG} with hd
  have hne : d.Nonempty := ⟨⊥, bot_le, Submodule.fg_bot⟩
  have hdir : DirectedOn (· ≤ ·) d := by
    rintro N₁ ⟨hN₁, hfg₁⟩ N₂ ⟨hN₂, hfg₂⟩
    exact ⟨N₁ ⊔ N₂, ⟨sup_le hN₁ hN₂, hfg₁.sup hfg₂⟩, le_sup_left, le_sup_right⟩
  have hlub : IsLUB d Z := by
    constructor
    · rintro N ⟨hN, -⟩
      exact hN
    · intro u hu v hv
      have hmem : Submodule.span R {v} ∈ d :=
        ⟨by rwa [Submodule.span_singleton_le_iff_mem], Submodule.fg_span_singleton v⟩
      exact hu hmem (Submodule.mem_span_singleton_self v)
  obtain ⟨K, hKd, hKW⟩ := hInacc hne hdir hlub hZ
  obtain ⟨s, hs⟩ := hKd.2
  refine ⟨s, ?_, ?_⟩
  · intro x hx
    exact hKd.1 (hs ▸ Submodule.subset_span hx)
  · rwa [hs]

variable (R M)

/-- **Positive membership tests generate the Scott topology.**  Principal upper sets of finitely
generated submodules are finite intersections of positive tests, and they cover every Scott open
set. -/
theorem scott_submodule_eq_generateFrom :
    Topology.scott (Submodule R M) univ =
      generateFrom {s | ∃ v : M, s = {Z : Submodule R M | v ∈ Z}} := by
  refine le_antisymm (le_generateFrom ?_) ?_
  · rintro s ⟨v, rfl⟩
    exact isOpen_scott_Ici_span_singleton v
  · intro W hW
    letI : TopologicalSpace (Submodule R M) :=
      generateFrom {s | ∃ v : M, s = {Z : Submodule R M | v ∈ Z}}
    rw [isOpen_scott_submodule_iff] at hW
    obtain ⟨hUp, hInacc⟩ := hW
    have hcover : W = ⋃ s : {s : Finset M // Submodule.span R (↑s : Set M) ∈ W},
        {Z : Submodule R M | ∀ v ∈ (s : Finset M), v ∈ Z} := by
      ext Z
      constructor
      · intro hZ
        obtain ⟨s, hsZ, hsW⟩ := exists_finset_span_mem_of_scott hInacc hZ
        exact mem_iUnion.2 ⟨⟨s, hsW⟩, fun v hv => hsZ hv⟩
      · intro hZ
        obtain ⟨⟨s, hsW⟩, hs⟩ := mem_iUnion.1 hZ
        refine hUp ?_ hsW
        rw [Submodule.span_le]
        intro v hv
        exact hs v hv
    show IsOpen W
    rw [hcover]
    refine isOpen_iUnion fun s => ?_
    have hEq : {Z : Submodule R M | ∀ v ∈ (s : Finset M), v ∈ Z} =
        ⋂ v ∈ ((s : Finset M) : Set M), {Z : Submodule R M | v ∈ Z} := by
      ext Z; simp
    rw [hEq]
    exact Set.Finite.isOpen_biInter (s : Finset M).finite_toSet
      fun v _ => isOpen_generateFrom_of_mem ⟨v, rfl⟩

end Lattice

/-! ## Exactness flags -/

/-- An exactness flag: a boundary submodule contained in a cycle submodule. -/
@[ext]
structure ExFlag (R M : Type*) [Semiring R] [AddCommMonoid M] [Module R M] where
  /-- The arithmetic boundary space. -/
  boundary : Submodule R M
  /-- The geometric cycle space. -/
  cycle : Submodule R M
  /-- Boundaries are cycles. -/
  boundary_le_cycle : boundary ≤ cycle

namespace ExFlag

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

/-- Negative provenance test: the vector is not a boundary. -/
def boundaryTest (v : M) : Set (ExFlag R M) := {p | v ∉ p.boundary}

/-- Positive provenance test: the vector is a cycle. -/
def cycleTest (v : M) : Set (ExFlag R M) := {p | v ∈ p.cycle}

/-- Framed survival locus: the vector is a cycle and is not a boundary. -/
def survival (v : M) : Set (ExFlag R M) := {p | v ∈ p.cycle ∧ v ∉ p.boundary}

variable (R M) in
/-- The subbasis of provenance tests. -/
def provSubbasis : Set (Set (ExFlag R M)) :=
  {s | ∃ v : M, s = boundaryTest (R := R) v} ∪ {s | ∃ v : M, s = cycleTest (R := R) v}

/-- The provenance-exactness topology: generated by the negative boundary tests and the positive
cycle tests. -/
instance instTopologicalSpace : TopologicalSpace (ExFlag R M) :=
  generateFrom (provSubbasis R M)

theorem isOpen_boundaryTest (v : M) : IsOpen (boundaryTest (R := R) (M := M) v) :=
  isOpen_generateFrom_of_mem (Or.inl ⟨v, rfl⟩)

theorem isOpen_cycleTest (v : M) : IsOpen (cycleTest (R := R) (M := M) v) :=
  isOpen_generateFrom_of_mem (Or.inr ⟨v, rfl⟩)

theorem survival_eq (v : M) :
    survival (R := R) (M := M) v = cycleTest v ∩ boundaryTest v := rfl

theorem isOpen_survival (v : M) : IsOpen (survival (R := R) (M := M) v) :=
  (isOpen_cycleTest v).inter (isOpen_boundaryTest v)

/-- **The provenance topology is the coarsest one making all provenance tests open.** -/
theorem le_of_isOpen_tests {t : TopologicalSpace (ExFlag R M)}
    (hb : ∀ v : M, IsOpen[t] (boundaryTest v)) (hc : ∀ v : M, IsOpen[t] (cycleTest v)) :
    t ≤ instTopologicalSpace := by
  refine le_generateFrom ?_
  rintro s (⟨v, rfl⟩ | ⟨v, rfl⟩)
  · exact hb v
  · exact hc v

/-- **The provenance topology is the mixed lower–Scott topology.**  The boundary coordinate carries
the lower topology and the cycle coordinate carries the Scott topology. -/
theorem provTopology_eq_inf :
    (instTopologicalSpace : TopologicalSpace (ExFlag R M)) =
      induced boundary (Topology.lower (Submodule R M)) ⊓
        induced cycle (Topology.scott (Submodule R M) univ) := by
  refine le_antisymm (le_inf ?_ ?_) ?_
  · rw [lower_submodule_eq_generateFrom, induced_generateFrom_eq]
    refine le_generateFrom ?_
    rintro s ⟨t, ⟨v, rfl⟩, rfl⟩
    exact isOpen_boundaryTest v
  · rw [← coinduced_le_iff_le_induced, scott_submodule_eq_generateFrom]
    intro s hs
    show IsOpen (cycle ⁻¹' s)
    induction hs with
    | basic s hs =>
      obtain ⟨v, rfl⟩ := hs
      exact isOpen_cycleTest v
    | univ =>
      rw [Set.preimage_univ]
      exact isOpen_univ
    | inter s t _ _ ihs iht =>
      rw [Set.preimage_inter]
      exact ihs.inter iht
    | sUnion S _ ih =>
      rw [Set.preimage_sUnion]
      exact isOpen_biUnion fun s hs => ih s hs
  · have hleB : induced boundary (Topology.lower (Submodule R M)) ⊓
        induced cycle (Topology.scott (Submodule R M) univ) ≤
        induced (boundary (R := R) (M := M)) (Topology.lower (Submodule R M)) := inf_le_left
    have hleZ : induced boundary (Topology.lower (Submodule R M)) ⊓
        induced cycle (Topology.scott (Submodule R M) univ) ≤
        induced (cycle (R := R) (M := M)) (Topology.scott (Submodule R M) univ) := inf_le_right
    refine le_of_isOpen_tests (fun v => ?_) (fun v => ?_)
    · refine hleB _ ⟨{B : Submodule R M | v ∉ B}, ?_, rfl⟩
      rw [lower_submodule_eq_generateFrom]
      exact isOpen_generateFrom_of_mem ⟨v, rfl⟩
    · exact hleZ _ ⟨{Z : Submodule R M | v ∈ Z}, isOpen_scott_Ici_span_singleton v, rfl⟩

/-- The comparison map into the mixed lower–Scott product. -/
def toMixed (p : ExFlag R M) :
    Topology.WithLower (Submodule R M) × Topology.WithScott (Submodule R M) :=
  (Topology.WithLower.toLower p.boundary, Topology.WithScott.toScott p.cycle)

/-- **The provenance topology is the subspace topology of the mixed lower–Scott product.** -/
theorem provTopology_eq_induced_toMixed :
    (instTopologicalSpace : TopologicalSpace (ExFlag R M)) =
      induced toMixed inferInstance := by
  rw [provTopology_eq_inf]
  show _ = induced toMixed (induced Prod.fst _ ⊓ induced Prod.snd _)
  rw [induced_inf, induced_compose, induced_compose]
  rfl

/-! ## Separation and specialization -/

/-- **Specialization order of the provenance topology.**  Specialization contracts the boundary
range and expands the cycle space. -/
theorem specializes_iff {p q : ExFlag R M} :
    p ⤳ q ↔ p.boundary ≤ q.boundary ∧ q.cycle ≤ p.cycle := by
  rw [specializes_iff_forall_open]
  constructor
  · intro h
    constructor
    · intro v hv
      by_contra hq
      exact (h (boundaryTest v) (isOpen_boundaryTest v) hq) hv
    · intro v hv
      exact h (cycleTest v) (isOpen_cycleTest v) hv
  · rintro ⟨hB, hZ⟩ s hs hq
    induction hs with
    | basic s hs =>
      rcases hs with ⟨v, rfl⟩ | ⟨v, rfl⟩
      · exact fun hv => hq (hB hv)
      · exact hZ hq
    | univ => exact mem_univ _
    | inter s t _ _ ihs iht => exact ⟨ihs hq.1, iht hq.2⟩
    | sUnion S _ ih =>
      obtain ⟨s, hsS, hqs⟩ := hq
      exact ⟨s, hsS, ih s hsS hqs⟩

/-- The provenance topology separates flags. -/
instance : T0Space (ExFlag R M) := by
  refine ⟨fun p q h => ?_⟩
  rw [inseparable_iff_specializes_and] at h
  obtain ⟨h₁, h₂⟩ := h
  rw [specializes_iff] at h₁ h₂
  exact ExFlag.ext (le_antisymm h₁.1 h₂.1) (le_antisymm h₂.2 h₁.2)

/-- Membership in the framed survival locus. -/
theorem mem_survival_iff {p : ExFlag R M} {v : M} :
    p ∈ survival v ↔ v ∈ p.cycle ∧ v ∉ p.boundary := Iff.rfl

/-- The falsely exact flag attached to a cycle space. -/
def falselyExact (Z : Submodule R M) : ExFlag R M := ⟨Z, Z, le_refl Z⟩

@[simp] theorem falselyExact_boundary (Z : Submodule R M) : (falselyExact Z).boundary = Z := rfl

@[simp] theorem falselyExact_cycle (Z : Submodule R M) : (falselyExact Z).cycle = Z := rfl

/-- **A cycle-only reporter is blind to provenance.**  Any invariant factoring through the cycle
coordinate takes the same value on a flag and on its falsely exact companion. -/
theorem eq_of_factorsThrough_cycle {α : Type*} (g : Submodule R M → α) (p : ExFlag R M) :
    (g ∘ cycle) p = (g ∘ cycle) (falselyExact p.cycle) := rfl

/-- **Provenance separation.**  A flag with a strictly smaller boundary space is separated from its
falsely exact companion by a framed survival locus, although the two flags have the same cycle
coordinate and therefore the same image under every cycle-only reporter. -/
theorem exists_survival_separating {p : ExFlag R M} (h : p.boundary < p.cycle) :
    ∃ v : M, p ∈ survival v ∧ falselyExact p.cycle ∉ survival v := by
  obtain ⟨v, hvZ, hvB⟩ := SetLike.exists_of_lt h
  exact ⟨v, ⟨hvZ, hvB⟩, fun hc => hc.2 hvZ⟩

end ExFlag

/-! ## Spectral quotient of a flag -/

namespace ExFlag

section Quotient

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]

/-- The spectral quotient `Z / B` of an exactness flag. -/
abbrev homology (p : ExFlag R M) : Type _ :=
  p.cycle ⧸ Submodule.comap p.cycle.subtype p.boundary

/-- The class of a cycle in the spectral quotient. -/
def homologyClass (p : ExFlag R M) {v : M} (hv : v ∈ p.cycle) : p.homology :=
  Submodule.Quotient.mk ⟨v, hv⟩

/-- **The framed survival locus detects a nonzero spectral class.** -/
theorem mem_survival_iff_homologyClass_ne_zero {p : ExFlag R M} {v : M} (hv : v ∈ p.cycle) :
    p ∈ survival v ↔ p.homologyClass hv ≠ 0 := by
  have h0 : p.homologyClass hv = 0 ↔ v ∈ p.boundary := by
    rw [homologyClass, Submodule.Quotient.mk_eq_zero]
    simp
  rw [mem_survival_iff, ne_eq, h0]
  exact ⟨fun h => h.2, fun h => ⟨hv, h⟩⟩

end Quotient

section Dimension

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- The spectral quotient dimension splits the flag. -/
theorem finrank_homology_add_finrank_boundary (p : ExFlag K V) :
    Module.finrank K p.homology + Module.finrank K p.boundary = Module.finrank K p.cycle := by
  have h := Submodule.finrank_quotient_add_finrank
    (Submodule.comap p.cycle.subtype p.boundary)
  rw [(Submodule.comapSubtypeEquivOfLe p.boundary_le_cycle).finrank_eq] at h
  exact h

/-- **Spectral dimension is monotone along specialization.**  Contracting the boundary range and
expanding the cycle space cannot decrease the dimension of the spectral quotient. -/
theorem finrank_homology_mono {p q : ExFlag K V} (hB : q.boundary ≤ p.boundary)
    (hZ : p.cycle ≤ q.cycle) :
    Module.finrank K p.homology ≤ Module.finrank K q.homology := by
  have hp := finrank_homology_add_finrank_boundary p
  have hq := finrank_homology_add_finrank_boundary q
  have h₁ : Module.finrank K q.boundary ≤ Module.finrank K p.boundary :=
    Submodule.finrank_mono hB
  have h₂ : Module.finrank K p.cycle ≤ Module.finrank K q.cycle :=
    Submodule.finrank_mono hZ
  omega

end Dimension

/-! ## Variance of pullback and pushforward -/

section Functoriality

variable {R M N : Type*} [Semiring R] [AddCommMonoid M] [AddCommMonoid N] [Module R M]
  [Module R N]

/-- Pullback of an exactness flag along a linear map. -/
def pullback (f : M →ₗ[R] N) (p : ExFlag R N) : ExFlag R M :=
  ⟨Submodule.comap f p.boundary, Submodule.comap f p.cycle,
    Submodule.comap_mono p.boundary_le_cycle⟩

@[simp] theorem pullback_boundary (f : M →ₗ[R] N) (p : ExFlag R N) :
    (pullback f p).boundary = Submodule.comap f p.boundary := rfl

@[simp] theorem pullback_cycle (f : M →ₗ[R] N) (p : ExFlag R N) :
    (pullback f p).cycle = Submodule.comap f p.cycle := rfl

/-- **Constraint pullback is continuous.**  Each provenance test pulls back to the provenance test
at the image vector. -/
theorem continuous_pullback (f : M →ₗ[R] N) : Continuous (pullback f) := by
  refine continuous_generateFrom_iff.2 ?_
  rintro s (⟨v, rfl⟩ | ⟨v, rfl⟩)
  · have hset : pullback f ⁻¹' boundaryTest v = boundaryTest (f v) := rfl
    rw [hset]
    exact isOpen_boundaryTest _
  · have hset : pullback f ⁻¹' cycleTest v = cycleTest (f v) := rfl
    rw [hset]
    exact isOpen_cycleTest _

/-- Pushforward of an exactness flag along a linear map. -/
def pushforward (f : M →ₗ[R] N) (p : ExFlag R M) : ExFlag R N :=
  ⟨Submodule.map f p.boundary, Submodule.map f p.cycle,
    Submodule.map_mono p.boundary_le_cycle⟩

@[simp] theorem pushforward_boundary (f : M →ₗ[R] N) (p : ExFlag R M) :
    (pushforward f p).boundary = Submodule.map f p.boundary := rfl

@[simp] theorem pushforward_cycle (f : M →ₗ[R] N) (p : ExFlag R M) :
    (pushforward f p).cycle = Submodule.map f p.cycle := rfl

/-- **Source range formation is continuous along an injective map.**  A target test at a vector in
the image is the source test at its unique preimage; off the image the two tests are trivial. -/
theorem continuous_pushforward_of_injective {f : M →ₗ[R] N} (hf : Function.Injective f) :
    Continuous (pushforward f) := by
  refine continuous_generateFrom_iff.2 ?_
  rintro s (⟨w, rfl⟩ | ⟨w, rfl⟩)
  · by_cases hw : ∃ v : M, f v = w
    · obtain ⟨v, rfl⟩ := hw
      have hset : pushforward f ⁻¹' boundaryTest (f v) = boundaryTest v := by
        ext p
        simp only [mem_preimage, boundaryTest, mem_setOf_eq, pushforward_boundary]
        constructor
        · intro h hv
          exact h (Submodule.mem_map_of_mem hv)
        · intro h hmem
          obtain ⟨u, hu, huv⟩ := Submodule.mem_map.1 hmem
          exact h (hf huv ▸ hu)
      rw [hset]
      exact isOpen_boundaryTest v
    · have hset : pushforward f ⁻¹' boundaryTest w = univ := by
        ext p
        simp only [mem_preimage, boundaryTest, mem_setOf_eq, pushforward_boundary, mem_univ,
          iff_true]
        intro hmem
        obtain ⟨u, -, huw⟩ := Submodule.mem_map.1 hmem
        exact hw ⟨u, huw⟩
      rw [hset]
      exact isOpen_univ
  · by_cases hw : ∃ v : M, f v = w
    · obtain ⟨v, rfl⟩ := hw
      have hset : pushforward f ⁻¹' cycleTest (f v) = cycleTest v := by
        ext p
        simp only [mem_preimage, cycleTest, mem_setOf_eq, pushforward_cycle]
        constructor
        · intro hmem
          obtain ⟨u, hu, huv⟩ := Submodule.mem_map.1 hmem
          exact hf huv ▸ hu
        · intro h
          exact Submodule.mem_map_of_mem h
      rw [hset]
      exact isOpen_cycleTest v
    · have hset : pushforward f ⁻¹' cycleTest w = (∅ : Set (ExFlag R M)) := by
        ext p
        simp only [mem_preimage, cycleTest, mem_setOf_eq, pushforward_cycle,
          mem_empty_iff_false, iff_false]
        intro hmem
        obtain ⟨u, -, huw⟩ := Submodule.mem_map.1 hmem
        exact hw ⟨u, huw⟩
      rw [hset]
      exact isOpen_empty

end Functoriality

/-! ## The boundary-containment locus is not open -/

section BoundaryContainment

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]

/-- The locus of flags whose boundary space is contained in a fixed subspace. -/
def boundaryLe (K : Submodule k V) : Set (ExFlag k V) := {p | p.boundary ≤ K}

/-- The affine family of lines through `u` in the direction of `w`. -/
private def affineLine (u w : V) (a : k) : Submodule k V := Submodule.span k {u + a • w}

private theorem indep_of_notMem {K : Submodule k V} {u w : V} (hu : u ∉ K) (hwK : w ∈ K)
    (hw : w ≠ 0) {c d : k} (h : c • u + d • w = 0) : c = 0 ∧ d = 0 := by
  have hc : c = 0 := by
    by_contra hc
    refine hu ?_
    have h1 : c • u = -(d • w) := by
      rw [eq_neg_iff_add_eq_zero]; exact h
    have h2 : u = c⁻¹ • (-(d • w)) := by
      rw [← h1, smul_smul, inv_mul_cancel₀ hc, one_smul]
    rw [h2]
    exact Submodule.smul_mem _ _ (Submodule.neg_mem _ (Submodule.smul_mem _ _ hwK))
  refine ⟨hc, ?_⟩
  rw [hc, zero_smul, zero_add] at h
  exact (smul_eq_zero.1 h).resolve_right hw

private theorem affineLine_not_le {K : Submodule k V} {u w : V} (hu : u ∉ K) (hwK : w ∈ K)
    (a : k) : ¬ affineLine u w a ≤ K := by
  intro h
  refine hu ?_
  have hmem : u + a • w ∈ K := h (Submodule.mem_span_singleton_self _)
  have hrw : u = (u + a • w) - a • w := by abel
  rw [hrw]
  exact Submodule.sub_mem _ hmem (Submodule.smul_mem _ _ hwK)

private theorem affineLine_param_subsingleton {K : Submodule k V} {u w : V} (hu : u ∉ K)
    (hwK : w ∈ K) (hw : w ≠ 0) {v : V} (hv : v ∉ K) :
    {a : k | v ∈ affineLine u w a}.Subsingleton := by
  intro a ha a' ha'
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 ha
  obtain ⟨c', hc'⟩ := Submodule.mem_span_singleton.1 ha'
  have hcne : c ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hc
    exact hv (hc ▸ Submodule.zero_mem K)
  have heq : c • (u + a • w) = c' • (u + a' • w) := by rw [hc, hc']
  have hcomb : (c - c') • u + (c * a - c' * a') • w = 0 := by
    linear_combination (norm := module) heq
  obtain ⟨h1, h2⟩ := indep_of_notMem hu hwK hw hcomb
  have hcc' : c = c' := sub_eq_zero.1 h1
  subst hcc'
  have h3 : c * (a - a') = 0 := by rw [mul_sub]; exact h2
  rcases mul_eq_zero.1 h3 with h | h
  · exact absurd h hcne
  · exact sub_eq_zero.1 h

/-- Every provenance-open set containing the flag `(K, ⊤)` contains all but finitely many of the
affine lines framed by the full cycle space. -/
private theorem cofinite_affineLine_of_isOpen {K : Submodule k V} {u w : V} (hu : u ∉ K)
    (hwK : w ∈ K) (hw : w ≠ 0) {U : Set (ExFlag k V)} (hU : IsOpen U)
    (hmem : (⟨K, ⊤, le_top⟩ : ExFlag k V) ∈ U) :
    ∃ S : Set k, S.Finite ∧ ∀ a : k, a ∉ S →
      (⟨affineLine u w a, ⊤, le_top⟩ : ExFlag k V) ∈ U := by
  induction hU with
  | basic s hs =>
    rcases hs with ⟨v, rfl⟩ | ⟨v, rfl⟩
    · have hv : v ∉ K := hmem
      exact ⟨{a : k | v ∈ affineLine u w a},
        (affineLine_param_subsingleton hu hwK hw hv).finite, fun a ha => ha⟩
    · exact ⟨∅, Set.finite_empty,
        fun a _ => show v ∈ (⊤ : Submodule k V) from Submodule.mem_top⟩
  | univ => exact ⟨∅, Set.finite_empty, fun a _ => mem_univ _⟩
  | inter s t _ _ ihs iht =>
    obtain ⟨S₁, hS₁, h₁⟩ := ihs hmem.1
    obtain ⟨S₂, hS₂, h₂⟩ := iht hmem.2
    exact ⟨S₁ ∪ S₂, hS₁.union hS₂, fun a ha =>
      ⟨h₁ a fun h => ha (Or.inl h), h₂ a fun h => ha (Or.inr h)⟩⟩
  | sUnion S _ ih =>
    obtain ⟨s, hsS, hms⟩ := hmem
    obtain ⟨T, hT, h⟩ := ih s hsS hms
    exact ⟨T, hT, fun a ha => ⟨s, hsS, h a ha⟩⟩

variable [Infinite k]

/-- **Universal annihilation of a boundary space is not a provenance-open condition.**  Whenever
`K` is neither zero nor everything, the flags whose boundary lies in `K` do not form an open set:
every provenance neighbourhood of `(K, ⊤)` already contains a line transverse to `K`. -/
theorem not_isOpen_boundaryLe {K : Submodule k V} {u w : V} (hu : u ∉ K) (hwK : w ∈ K)
    (hw : w ≠ 0) : ¬ IsOpen (boundaryLe K) := by
  intro hopen
  have hmem : (⟨K, ⊤, le_top⟩ : ExFlag k V) ∈ boundaryLe K := le_refl K
  obtain ⟨S, hSfin, hS⟩ := cofinite_affineLine_of_isOpen hu hwK hw hopen hmem
  obtain ⟨a, ha⟩ := (hSfin.infinite_compl).nonempty
  exact affineLine_not_le hu hwK a (hS a ha)

end BoundaryContainment

/-! ## Pushforward along a plane projection is discontinuous -/

section Projection

variable {k : Type*} [Field k] [Infinite k]

/-- **Source range formation is not continuous.**  Pushforward along the first coordinate
projection of a plane over an infinite field fails to be continuous for the provenance topology:
the negative boundary test at `1` pulls back to the boundary-containment locus of `ker p`, which is
not open. -/
theorem not_continuous_pushforward_fst :
    ¬ Continuous (pushforward (LinearMap.fst k k k)) := by
  intro hcont
  have hpre : pushforward (LinearMap.fst k k k) ⁻¹' boundaryTest (1 : k) =
      boundaryLe (LinearMap.ker (LinearMap.fst k k k)) := by
    ext p
    simp only [mem_preimage, boundaryTest, mem_setOf_eq, pushforward_boundary, boundaryLe]
    constructor
    · intro h v hv
      simp only [LinearMap.mem_ker, LinearMap.fst_apply]
      by_contra hne
      refine h ?_
      have hmem : ((v.1)⁻¹ • v) ∈ p.boundary := p.boundary.smul_mem _ hv
      have hval : (LinearMap.fst k k k) ((v.1)⁻¹ • v) = 1 := by
        simp [inv_mul_cancel₀ hne]
      exact hval ▸ Submodule.mem_map_of_mem hmem
    · intro h hmem
      obtain ⟨v, hv, hv1⟩ := Submodule.mem_map.1 hmem
      have := h hv
      simp only [LinearMap.mem_ker, LinearMap.fst_apply] at this
      rw [LinearMap.fst_apply, this] at hv1
      exact one_ne_zero hv1.symm
  have hopen : IsOpen (boundaryLe (LinearMap.ker (LinearMap.fst k k k))) := by
    rw [← hpre]
    exact hcont.isOpen_preimage _ (isOpen_boundaryTest 1)
  refine not_isOpen_boundaryLe (u := ((1 : k), (0 : k))) (w := ((0 : k), (1 : k)))
    ?_ ?_ ?_ hopen
  · simp [LinearMap.mem_ker]
  · simp [LinearMap.mem_ker]
  · simp

end Projection

end ExFlag

end GaloisForLFunctions.HTGeometry
