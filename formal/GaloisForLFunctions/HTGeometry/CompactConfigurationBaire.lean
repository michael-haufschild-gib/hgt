import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Topology.GDelta.Basic

/-!
# Compact-configuration avoidance and countable Baire assembly

Fixed-configuration polynomial escape does not by itself control an uncountable configuration
space.  This module isolates the exact topological passage used after parametric transversality.

For a jointly continuous defect map, avoidance of a closed bad set uniformly over a compact
configuration patch is open in the parameter.  The proof is the generalized tube lemma, not a
pointwise continuity argument.  If a configuration space is exhausted by countably many compact
patches and every patchwise avoidance set is dense, Baire category gives simultaneous avoidance
of every configuration.  A dependent countable-pattern theorem performs both countable
intersections at once.

Thus the remaining analytic-geometric input in applications is precisely patchwise density
(normally supplied by finite stratification and parametric transversality); openness, the
uncountable compact-patch quantifier, and countable Baire assembly are unconditional.
-/

namespace GaloisForLFunctions.HTGeometry

open Set Topology

noncomputable section

/-- Parameters whose entire compact configuration patch avoids a prescribed bad set. -/
def compactConfigurationAvoidance
    {X H Y : Type*} (F : X × H → Y) (bad : Set Y) (K : Set H) : Set X :=
  {x | ∀ h ∈ K, F (x, h) ∉ bad}

/-- Parameters which avoid the bad set at every point of the full configuration space. -/
def globalConfigurationAvoidance
    {X H Y : Type*} (F : X × H → Y) (bad : Set Y) : Set X :=
  {x | ∀ h, F (x, h) ∉ bad}

/-- Uniform avoidance on a compact configuration patch is open.  Joint continuity is essential:
the tube lemma upgrades the pointwise open neighborhoods to one parameter neighborhood valid for
the whole compact patch. -/
theorem compactConfigurationAvoidance_isOpen
    {X H Y : Type*} [TopologicalSpace X] [TopologicalSpace H] [TopologicalSpace Y]
    (F : X × H → Y) (hF : Continuous F) (bad : Set Y) (hbad : IsClosed bad)
    (K : Set H) (hK : IsCompact K) :
    IsOpen (compactConfigurationAvoidance F bad K) := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  let U : Set (X × H) := F ⁻¹' badᶜ
  have hUopen : IsOpen U := hbad.isOpen_compl.preimage hF
  have hprod : ({x} : Set X) ×ˢ K ⊆ U := by
    rintro ⟨x', h⟩ ⟨hx', hh⟩
    simp only [mem_singleton_iff] at hx'
    subst x'
    exact hx h hh
  obtain ⟨V, W, hVopen, hWopen, hxV, hKW, hVW⟩ :=
    generalized_tube_lemma isCompact_singleton hK hUopen hprod
  refine Filter.mem_of_superset (hVopen.mem_nhds (hxV (mem_singleton x))) ?_
  intro x' hx' h hh
  have hpair : (x', h) ∈ V ×ˢ W := ⟨hx', hKW hh⟩
  exact hVW hpair

/-- A countable compact exhaustion turns patchwise avoidance into avoidance of the whole
configuration space. -/
theorem iInter_compactConfigurationAvoidance_eq_global
    {X H Y : Type*} (F : X × H → Y) (bad : Set Y)
    (K : ℕ → Set H) (hcover : (⋃ n, K n) = Set.univ) :
    (⋂ n, compactConfigurationAvoidance F bad (K n)) =
      globalConfigurationAvoidance F bad := by
  ext x
  simp only [mem_iInter, compactConfigurationAvoidance, globalConfigurationAvoidance,
    mem_setOf_eq]
  constructor
  · intro hx h
    have hh : h ∈ ⋃ n, K n := by rw [hcover]; exact mem_univ h
    obtain ⟨n, hn⟩ := mem_iUnion.mp hh
    exact hx n h hn
  · intro hx n h _
    exact hx h

/-- **Compact-configuration Baire law.**  If every member of a countable compact exhaustion has
dense avoidance and the defect map is jointly continuous, then parameters avoiding the closed bad
set for every configuration form a dense residual set. -/
theorem globalConfigurationAvoidance_dense_residual
    {X H Y : Type*} [TopologicalSpace X] [BaireSpace X]
    [TopologicalSpace H] [TopologicalSpace Y]
    (F : X × H → Y) (hF : Continuous F) (bad : Set Y) (hbad : IsClosed bad)
    (K : ℕ → Set H) (hK : ∀ n, IsCompact (K n))
    (hcover : (⋃ n, K n) = Set.univ)
    (hdense : ∀ n, Dense (compactConfigurationAvoidance F bad (K n))) :
    Dense (globalConfigurationAvoidance F bad) ∧
      globalConfigurationAvoidance F bad ∈ residual X := by
  have hopen : ∀ n, IsOpen (compactConfigurationAvoidance F bad (K n)) :=
    fun n ↦ compactConfigurationAvoidance_isOpen F hF bad hbad (K n) (hK n)
  have hres : (⋂ n, compactConfigurationAvoidance F bad (K n)) ∈ residual X :=
    countable_iInter_mem.mpr fun n ↦ residual_of_dense_open (hopen n) (hdense n)
  rw [iInter_compactConfigurationAvoidance_eq_global F bad K hcover] at hres
  exact ⟨dense_of_mem_residual hres, hres⟩

/-- Sigma-compactness supplies the countable compact exhaustion automatically.  Therefore
patchwise density on every compact set is already sufficient for global uncountable-configuration
avoidance. -/
theorem globalConfigurationAvoidance_dense_residual_of_sigmaCompact
    {X H Y : Type*} [TopologicalSpace X] [BaireSpace X]
    [TopologicalSpace H] [SigmaCompactSpace H] [TopologicalSpace Y]
    (F : X × H → Y) (hF : Continuous F) (bad : Set Y) (hbad : IsClosed bad)
    (hdense : ∀ K : Set H, IsCompact K → Dense (compactConfigurationAvoidance F bad K)) :
    Dense (globalConfigurationAvoidance F bad) ∧
      globalConfigurationAvoidance F bad ∈ residual X := by
  obtain ⟨K, hK, hcover⟩ := SigmaCompactSpace.exists_compact_covering (X := H)
  exact globalConfigurationAvoidance_dense_residual
    F hF bad hbad K hK hcover (fun n ↦ hdense (K n) (hK n))

/-- **Countable-pattern compact-configuration Baire law.**  Relation patterns may have different
configuration and target spaces.  If each pattern has a countable compact exhaustion and every
pattern--patch avoidance set is dense, then one dense residual set simultaneously avoids every
closed bad locus at every configuration of every pattern. -/
theorem countablePattern_globalConfigurationAvoidance_dense_residual
    {X : Type*} [TopologicalSpace X] [BaireSpace X]
    (H Y : ℕ → Type*) [∀ n, TopologicalSpace (H n)] [∀ n, TopologicalSpace (Y n)]
    (F : (n : ℕ) → X × H n → Y n) (hF : ∀ n, Continuous (F n))
    (bad : (n : ℕ) → Set (Y n)) (hbad : ∀ n, IsClosed (bad n))
    (K : (n m : ℕ) → Set (H n)) (hK : ∀ n m, IsCompact (K n m))
    (hcover : ∀ n, (⋃ m, K n m) = Set.univ)
    (hdense : ∀ n m, Dense (compactConfigurationAvoidance (F n) (bad n) (K n m))) :
    Dense {x | ∀ n h, F n (x, h) ∉ bad n} ∧
      {x | ∀ n h, F n (x, h) ∉ bad n} ∈ residual X := by
  let A : Set X := ⋂ n, ⋂ m, compactConfigurationAvoidance (F n) (bad n) (K n m)
  have hopen : ∀ n m, IsOpen (compactConfigurationAvoidance (F n) (bad n) (K n m)) :=
    fun n m ↦ compactConfigurationAvoidance_isOpen
      (F n) (hF n) (bad n) (hbad n) (K n m) (hK n m)
  have hres : A ∈ residual X := by
    apply countable_iInter_mem.mpr
    intro n
    apply countable_iInter_mem.mpr
    intro m
    exact residual_of_dense_open (hopen n m) (hdense n m)
  have hA : A = {x | ∀ n h, F n (x, h) ∉ bad n} := by
    ext x
    simp only [A, mem_iInter, compactConfigurationAvoidance, mem_setOf_eq]
    constructor
    · intro hx n h
      have hh : h ∈ ⋃ m, K n m := by rw [hcover n]; exact mem_univ h
      obtain ⟨m, hm⟩ := mem_iUnion.mp hh
      exact hx n m h hm
    · intro hx n m h _
      exact hx n h
  rw [hA] at hres
  exact ⟨dense_of_mem_residual hres, hres⟩

/-- Sigma-compact configuration spaces eliminate the exhaustion data from the dependent
countable-pattern theorem.  This is the direct interface for countably many relation patterns:
the sole remaining input is density of avoidance on each compact configuration patch. -/
theorem countablePattern_globalConfigurationAvoidance_dense_residual_of_sigmaCompact
    {X : Type*} [TopologicalSpace X] [BaireSpace X]
    (H Y : ℕ → Type*) [∀ n, TopologicalSpace (H n)] [∀ n, SigmaCompactSpace (H n)]
    [∀ n, TopologicalSpace (Y n)]
    (F : (n : ℕ) → X × H n → Y n) (hF : ∀ n, Continuous (F n))
    (bad : (n : ℕ) → Set (Y n)) (hbad : ∀ n, IsClosed (bad n))
    (hdense : ∀ (n : ℕ) (K : Set (H n)), IsCompact K →
      Dense (compactConfigurationAvoidance (F n) (bad n) K)) :
    Dense {x | ∀ n h, F n (x, h) ∉ bad n} ∧
      {x | ∀ n h, F n (x, h) ∉ bad n} ∈ residual X := by
  let K : (n m : ℕ) → Set (H n) := fun n ↦
    Classical.choose (SigmaCompactSpace.exists_compact_covering (X := H n))
  have hK : ∀ n m, IsCompact (K n m) := by
    intro n
    exact (Classical.choose_spec
      (SigmaCompactSpace.exists_compact_covering (X := H n))).1
  have hcover : ∀ n, (⋃ m, K n m) = Set.univ := by
    intro n
    exact (Classical.choose_spec
      (SigmaCompactSpace.exists_compact_covering (X := H n))).2
  exact countablePattern_globalConfigurationAvoidance_dense_residual
    H Y F hF bad hbad K hK hcover (fun n m ↦ hdense n (K n m) (hK n m))

end

end GaloisForLFunctions.HTGeometry
