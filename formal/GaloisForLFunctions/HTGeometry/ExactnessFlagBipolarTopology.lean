import GaloisForLFunctions.HTGeometry.ExactnessFlagDaggerDuality

/-!
# Bipolar provenance topology

The one-sided provenance topology tests a vector for nonmembership in the boundary space.  The
dagger asks instead for the universal condition that a whole boundary space be annihilated by a
covector, and that condition is not lower open: over an infinite field, every provenance
neighbourhood of the flag `(ker φ, ⊤)` already contains a line transverse to `ker φ`.

The minimal repair is the bipolar topology, the provenance topology refined by the pullback of the
provenance topology along the dagger.  It is the coarsest refinement making the dagger continuous,
it adds exactly one new generator type — the boundary annihilation loci `B ⊆ ker φ` — it leaves the
specialization order unchanged, and on a finite-dimensional space the dagger is a homeomorphism for
it.
-/

namespace GaloisForLFunctions.HTGeometry

namespace ExFlag

open Set Topology TopologicalSpace

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-! ## The dagger pullback of the provenance generators -/

/-- The dagger pullback of a positive dual cycle test is a boundary annihilation locus. -/
theorem dagger_preimage_cycleTest (φ : Module.Dual K V) :
    dagger ⁻¹' cycleTest φ = boundaryLe (LinearMap.ker φ) := by
  ext p
  simp only [mem_preimage, cycleTest, mem_setOf_eq, dagger_cycle,
    Submodule.mem_dualAnnihilator, boundaryLe]
  exact ⟨fun h v hv => h v hv, fun h v hv => h hv⟩

/-- The dagger pullback of a negative dual boundary test is already a union of positive source
cycle tests. -/
theorem dagger_preimage_boundaryTest (φ : Module.Dual K V) :
    dagger ⁻¹' boundaryTest φ = ⋃ v ∈ {v : V | φ v ≠ 0}, cycleTest v := by
  ext p
  simp only [mem_preimage, boundaryTest, mem_setOf_eq, dagger_boundary,
    Submodule.mem_dualAnnihilator, mem_iUnion, cycleTest, exists_prop]
  constructor
  · intro h
    by_contra hc
    refine h fun v hv => ?_
    by_contra hne
    exact hc ⟨v, hne, hv⟩
  · rintro ⟨v, hv, hvZ⟩ h
    exact hv (h v hvZ)

/-! ## The dagger is not provenance continuous -/

section Discontinuity

variable [Infinite K]

/-- **The dagger is not continuous for the one-sided provenance topology.**  Its pullback of a
positive dual cycle test is a boundary annihilation locus, and such a locus is not provenance
open. -/
theorem not_continuous_dagger_of_exists {φ : Module.Dual K V} {u w : V}
    (hu : u ∉ LinearMap.ker φ) (hwK : w ∈ LinearMap.ker φ) (hw : w ≠ 0) :
    ¬ Continuous (dagger : ExFlag K V → ExFlag K (Module.Dual K V)) := by
  intro hcont
  refine not_isOpen_boundaryLe hu hwK hw ?_
  rw [← dagger_preimage_cycleTest φ]
  exact hcont.isOpen_preimage _ (isOpen_cycleTest φ)

/-- **The dagger is not continuous whenever the space has dimension at least two.** -/
theorem not_continuous_dagger (h : 1 < Module.rank K V) :
    ¬ Continuous (dagger : ExFlag K V → ExFlag K (Module.Dual K V)) := by
  have hnt : Nontrivial V := by
    rw [← rank_pos_iff_nontrivial (R := K)]
    exact lt_trans zero_lt_one h
  obtain ⟨w, hw⟩ := exists_ne (0 : V)
  have hspan : Submodule.span K ({w} : Set V) ≠ ⊤ := by
    intro htop
    have hle : Module.rank K V ≤ 1 := by
      have h1 : Module.rank K (Submodule.span K ({w} : Set V)) ≤ 1 := by
        simpa using rank_span_le (R := K) ({w} : Set V)
      rw [htop] at h1
      simpa using h1
    exact absurd hle (not_le.2 h)
  obtain ⟨u, -, hu⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.2 hspan)
  have hex : ∃ φ : Module.Dual K V,
      φ ∈ (Submodule.span K ({w} : Set V)).dualAnnihilator ∧ φ u ≠ 0 := by
    by_contra hc
    refine hu ((Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff
      (Submodule.span K ({w} : Set V)) u).1 fun ψ hψ => ?_)
    by_contra hne
    exact hc ⟨ψ, hψ, hne⟩
  obtain ⟨φ, hφann, hφu⟩ := hex
  refine not_continuous_dagger_of_exists (φ := φ) (u := u) (w := w) ?_ ?_ hw
  · simpa only [LinearMap.mem_ker] using hφu
  · rw [LinearMap.mem_ker]
    exact (Submodule.mem_dualAnnihilator φ).1 hφann w (Submodule.mem_span_singleton_self w)

end Discontinuity

/-! ## Transport of flags along a linear equivalence -/

section Congr

variable {W : Type*} [AddCommGroup W] [Module K W]

/-- Transport of exactness flags along a linear equivalence. -/
def congr (e : V ≃ₗ[K] W) : ExFlag K V ≃ₜ ExFlag K W where
  toFun := pushforward (e : V →ₗ[K] W)
  invFun := pushforward (e.symm : W →ₗ[K] V)
  left_inv := by
    intro p
    refine ExFlag.ext ?_ ?_ <;>
      · simp only [pushforward_boundary, pushforward_cycle, ← Submodule.map_comp]
        simp [LinearEquiv.comp_coe]
  right_inv := by
    intro p
    refine ExFlag.ext ?_ ?_ <;>
      · simp only [pushforward_boundary, pushforward_cycle, ← Submodule.map_comp]
        simp [LinearEquiv.comp_coe]
  continuous_toFun := continuous_pushforward_of_injective e.injective
  continuous_invFun := continuous_pushforward_of_injective e.symm.injective

@[simp] theorem congr_apply (e : V ≃ₗ[K] W) (p : ExFlag K V) :
    congr e p = pushforward (e : V →ₗ[K] W) p := rfl

/-- Transport along a linear equivalence does not change the provenance topology. -/
theorem induced_pushforward_equiv (e : V ≃ₗ[K] W) :
    TopologicalSpace.induced (pushforward (e : V →ₗ[K] W)) instTopologicalSpace =
      (instTopologicalSpace : TopologicalSpace (ExFlag K V)) :=
  ((congr e).isInducing.eq_induced).symm

end Congr

/-! ## The bipolar topology -/

variable (K V) in
/-- The bipolar topology: the provenance topology joined with its dagger pullback. -/
@[reducible] def biTopology : TopologicalSpace (ExFlag K V) :=
  instTopologicalSpace ⊓ TopologicalSpace.induced dagger instTopologicalSpace

/-- The bipolar topology refines the provenance topology. -/
theorem biTopology_le_prov : biTopology K V ≤ instTopologicalSpace := inf_le_left

/-- The dagger is continuous from the bipolar topology to the provenance topology of the dual. -/
theorem continuous_dagger_bi :
    Continuous[biTopology K V, instTopologicalSpace] dagger :=
  (@continuous_iff_le_induced _ _ dagger (biTopology K V) instTopologicalSpace).2 inf_le_right

/-- **The bipolar topology is the coarsest refinement of the provenance topology making the dagger
continuous.** -/
theorem le_biTopology {t : TopologicalSpace (ExFlag K V)} (hprov : t ≤ instTopologicalSpace)
    (hdag : Continuous[t, instTopologicalSpace] dagger) : t ≤ biTopology K V :=
  le_inf hprov ((@continuous_iff_le_induced _ _ dagger t instTopologicalSpace).1 hdag)

/-- The boundary annihilation loci, the only new generator type of the bipolar topology. -/
def daggerPhaseTests (K V : Type*) [Field K] [AddCommGroup V] [Module K V] :
    Set (Set (ExFlag K V)) :=
  {s | ∃ φ : Module.Dual K V, s = boundaryLe (LinearMap.ker φ)}

/-- **The bipolar topology adds exactly the boundary annihilation loci.**  The pullback of a
negative dual boundary test is already a union of positive source cycle tests, so the only new
generator is the phase test `B ⊆ ker φ`. -/
theorem biTopology_eq_generateFrom :
    biTopology K V =
      TopologicalSpace.generateFrom (provSubbasis K V ∪ daggerPhaseTests K V) := by
  have hind : TopologicalSpace.induced (dagger (K := K) (V := V)) instTopologicalSpace =
      TopologicalSpace.generateFrom
        (Set.image (Set.preimage dagger) (provSubbasis K (Module.Dual K V))) :=
    induced_generateFrom_eq
  have hbi : biTopology K V =
      TopologicalSpace.generateFrom (provSubbasis K V ∪
        Set.image (Set.preimage dagger) (provSubbasis K (Module.Dual K V))) := by
    rw [biTopology, hind, generateFrom_union]
    rfl
  rw [hbi]
  refine le_antisymm (le_generateFrom ?_) (le_generateFrom ?_)
  · letI : TopologicalSpace (ExFlag K V) :=
      TopologicalSpace.generateFrom (provSubbasis K V ∪
        Set.image (Set.preimage dagger) (provSubbasis K (Module.Dual K V)))
    rintro s (hs | ⟨φ, rfl⟩)
    · exact isOpen_generateFrom_of_mem (Or.inl hs)
    · exact isOpen_generateFrom_of_mem
        (Or.inr ⟨cycleTest φ, Or.inr ⟨φ, rfl⟩, dagger_preimage_cycleTest φ⟩)
  · letI : TopologicalSpace (ExFlag K V) :=
      TopologicalSpace.generateFrom (provSubbasis K V ∪ daggerPhaseTests K V)
    rintro s (hs | ⟨t, (⟨φ, rfl⟩ | ⟨φ, rfl⟩), rfl⟩)
    · exact isOpen_generateFrom_of_mem (Or.inl hs)
    · rw [dagger_preimage_boundaryTest φ]
      exact isOpen_biUnion fun v _ => isOpen_generateFrom_of_mem (Or.inl (Or.inr ⟨v, rfl⟩))
    · rw [dagger_preimage_cycleTest φ]
      exact isOpen_generateFrom_of_mem (Or.inr ⟨φ, rfl⟩)

/-- **The bipolar topology has the same specialization order as the provenance topology.**  Every
boundary annihilation locus is downward closed in the boundary coordinate. -/
theorem bi_specializes_iff {p q : ExFlag K V} :
    @Specializes _ (biTopology K V) p q ↔ p.boundary ≤ q.boundary ∧ q.cycle ≤ p.cycle := by
  constructor
  · intro h
    refine specializes_iff.1 (specializes_iff_forall_open.2 fun s hs hq => ?_)
    exact (@specializes_iff_forall_open _ (biTopology K V) p q).1 h s
      (biTopology_le_prov s hs) hq
  · rintro ⟨hB, hZ⟩
    refine (@specializes_iff_forall_open _ (biTopology K V) p q).2 fun s hs hq => ?_
    rw [biTopology_eq_generateFrom] at hs
    induction hs with
    | basic s hs =>
      rcases hs with (⟨v, rfl⟩ | ⟨v, rfl⟩) | ⟨φ, rfl⟩
      · exact fun hv => hq (hB hv)
      · exact hZ hq
      · exact le_trans hB hq
    | univ => exact Set.mem_univ _
    | inter s t _ _ ihs iht => exact ⟨ihs hq.1, iht hq.2⟩
    | sUnion S _ ih =>
      obtain ⟨s, hsS, hqs⟩ := hq
      exact ⟨s, hsS, ih s hsS hqs⟩

/-! ## Dagger stability of the bipolar topology -/

variable [FiniteDimensional K V]

/-- The bipolar topology is stable under the dagger pullback. -/
theorem induced_dagger_biTopology :
    TopologicalSpace.induced (dagger (K := K) (V := V))
        (biTopology K (Module.Dual K V)) = biTopology K V := by
  have hcomp : (dagger (K := K) (V := Module.Dual K V)) ∘ (dagger (K := K) (V := V)) =
      pushforward ((Module.evalEquiv K V : V ≃ₗ[K] Module.Dual K (Module.Dual K V)) :
        V →ₗ[K] Module.Dual K (Module.Dual K V)) := by
    funext p
    rw [Function.comp_apply, dagger_dagger, Module.evalEquiv_toLinearMap]
  rw [biTopology, biTopology, induced_inf, induced_compose, hcomp,
    induced_pushforward_equiv, inf_comm]

/-- The bipolar topology is stable under the inverse dagger pullback. -/
theorem induced_daggerSymm_biTopology :
    TopologicalSpace.induced (daggerSymm (K := K) (V := V)) (biTopology K V) =
      biTopology K (Module.Dual K V) := by
  have hcomp : (dagger (K := K) (V := V)) ∘ (daggerSymm (K := K) (V := V)) = id := by
    funext q
    exact dagger_daggerSymm q
  rw [← induced_dagger_biTopology (K := K) (V := V), induced_compose, hcomp,
    @induced_id _ (biTopology K (Module.Dual K V))]

/-- **The dagger is a bipolar homeomorphism.** -/
def daggerBiHomeomorph :
    @Homeomorph (ExFlag K V) (ExFlag K (Module.Dual K V)) (biTopology K V)
      (biTopology K (Module.Dual K V)) :=
  @Homeomorph.mk _ _ (biTopology K V) (biTopology K (Module.Dual K V)) (daggerEquiv K V)
    ((@continuous_iff_le_induced _ _ (daggerEquiv K V) (biTopology K V)
        (biTopology K (Module.Dual K V))).2 (le_of_eq induced_dagger_biTopology.symm))
    ((@continuous_iff_le_induced _ _ (daggerEquiv K V).symm (biTopology K (Module.Dual K V))
        (biTopology K V)).2 (le_of_eq induced_daggerSymm_biTopology.symm))

end ExFlag

end GaloisForLFunctions.HTGeometry
