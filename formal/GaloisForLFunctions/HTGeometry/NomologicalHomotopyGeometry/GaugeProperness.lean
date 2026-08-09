import Mathlib.Topology.Algebra.Group.Pointwise
import Mathlib.Topology.Algebra.ProperAction.Basic

/-!
# Gauge-orbit nonproperness and reduced coercivity

This file uses exactly the compact-preimage definition of properness used by the paper card.  It
proves that a noncompact orbit closure obstructs every invariant proper map, proves the free proper
action corollary, and establishes both directions of the reduction law.  The compact-group branch
is discharged by proving the orbit projection proper, rather than assuming that fact.
-/

namespace HTGeometry.NomologicalHomotopyGeometry

open Function Set Topology
open scoped Pointwise

/-- Properness in the card's stated sense: inverse images of compact sets are compact. -/
def CompactPreimageProper {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) : Prop :=
  ∀ ⦃K : Set Y⦄, IsCompact K → IsCompact (f ⁻¹' K)

namespace CompactPreimageProper

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
variable {f : X → Y} {g : Y → Z}

/-- Bourbaki properness implies compact-preimage properness. -/
theorem of_isProperMap (hf : IsProperMap f) : CompactPreimageProper f :=
  fun _ hK ↦ hf.isCompact_preimage hK

/-- Compact-preimage proper maps are closed under composition. -/
theorem comp (hg : CompactPreimageProper g) (hf : CompactPreimageProper f) :
    CompactPreimageProper (g ∘ f) := by
  intro K hK
  exact hf (hg hK)

/-- Properness descends through a continuous surjection.  This is the abstract reduction step:
the reduced compact inverse image is the projection of the unreduced compact inverse image. -/
theorem descend_of_comp (hπ : Continuous f) (hπsurj : Surjective f)
    (hgf : CompactPreimageProper (g ∘ f)) : CompactPreimageProper g := by
  intro K hK
  have himage : g ⁻¹' K = f '' ((g ∘ f) ⁻¹' K) := by
    ext y
    constructor
    · intro hy
      rcases hπsurj y with ⟨x, rfl⟩
      exact ⟨x, hy, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact hx
  rw [himage]
  exact (hgf hK).image hπ

end CompactPreimageProper

section OrbitObstruction

variable {G X Y Z : Type*} [Group G] [MulAction G X]
variable [TopologicalSpace X] [T2Space X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- An invariant map is constant on each orbit. -/
theorem orbit_subset_fiber_of_invariant (f : X → Y)
    (hinv : ∀ (g : G) (x : X), f (g • x) = f x) (x : X) :
    MulAction.orbit G x ⊆ f ⁻¹' {f x} := by
  intro y hy
  rw [MulAction.mem_orbit_iff] at hy
  rcases hy with ⟨g, rfl⟩
  simpa using hinv g x

/-- Invisible noncompact orbit closure kills compact-preimage properness. -/
theorem invariant_not_compactPreimageProper_of_noncompact_orbitClosure
    (f : X → Y) (hinv : ∀ (g : G) (x : X), f (g • x) = f x) (x : X)
    (hnoncompact : ¬ IsCompact (closure (MulAction.orbit G x))) :
    ¬ CompactPreimageProper f := by
  intro hf
  have hfiberCompact : IsCompact (f ⁻¹' ({f x} : Set Y)) := hf isCompact_singleton
  have hfiberClosed : IsClosed (f ⁻¹' ({f x} : Set Y)) := hfiberCompact.isClosed
  apply hnoncompact
  exact hfiberCompact.of_isClosed_subset isClosed_closure
    (closure_minimal (orbit_subset_fiber_of_invariant f hinv x) hfiberClosed)

/-- Gauge invariance of both components makes the observer--action pair invariant. -/
theorem pair_invariant (q : X → Y) (S : X → Z)
    (hq : ∀ (g : G) (x : X), q (g • x) = q x) (hS : ∀ (g : G) (x : X), S (g • x) = S x) :
    ∀ (g : G) (x : X), (q (g • x), S (g • x)) = (q x, S x) := by
  intro g x
  exact Prod.ext (hq g x) (hS g x)

/-- Theorem 2.1: one noncompact orbit closure simultaneously obstructs the invariant action and
the invariant observer--action pair. -/
theorem gaugeOrbit_nonproperness (q : X → Y) (S : X → Z)
    (hq : ∀ (g : G) (x : X), q (g • x) = q x) (hS : ∀ (g : G) (x : X), S (g • x) = S x) (x : X)
    (hnoncompact : ¬ IsCompact (closure (MulAction.orbit G x))) :
    ¬ CompactPreimageProper S ∧ ¬ CompactPreimageProper (fun y ↦ (q y, S y)) := by
  exact ⟨
    invariant_not_compactPreimageProper_of_noncompact_orbitClosure S hS x hnoncompact,
    invariant_not_compactPreimageProper_of_noncompact_orbitClosure (fun y ↦ (q y, S y))
      (pair_invariant q S hq hS) x hnoncompact⟩

end OrbitObstruction

section FreeProperAction

variable {G X : Type*} [Group G] [MulAction G X]
variable [TopologicalSpace G] [TopologicalSpace X] [T2Space X]
variable [ProperSMul G X] [IsCancelSMul G X]

/-- The orbit map of a proper action is closed. -/
theorem orbitMap_isClosedMap (x : X) : IsClosedMap (fun g : G ↦ g • x) := by
  intro s hs
  simpa [Set.smul_singleton] using
    (hs.smul_right_of_isCompact (G := G) (X := X) isCompact_singleton)

/-- For a free proper action, every orbit map is a closed embedding. -/
theorem orbitMap_isClosedEmbedding (x : X) : IsClosedEmbedding (fun g : G ↦ g • x) :=
  IsClosedEmbedding.of_continuous_injective_isClosedMap
    (continuous_smul.comp (continuous_id.prodMk continuous_const))
    (fun _ _ h ↦ IsCancelSMul.right_cancel _ _ x h)
    (orbitMap_isClosedMap x)

/-- A free proper orbit is homeomorphic to the acting group. -/
noncomputable def orbitHomeomorph (x : X) : G ≃ₜ MulAction.orbit G x :=
  (orbitMap_isClosedEmbedding x).isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (by ext y; simp [MulAction.mem_orbit_iff]))

/-- Every orbit of a free proper action is closed. -/
theorem orbit_isClosed (x : X) : IsClosed (MulAction.orbit G x) := by
  have hrange : IsClosed (Set.range (fun g : G ↦ g • x)) :=
    (orbitMap_isClosedEmbedding x).isClosed_range
  exact hrange

/-- If the acting group is noncompact, every free proper orbit is noncompact. -/
theorem orbit_not_isCompact_of_group_not_compact (hG : ¬ CompactSpace G) (x : X) :
    ¬ IsCompact (MulAction.orbit G x) := by
  intro horbit
  letI : CompactSpace (MulAction.orbit G x) := isCompact_iff_compactSpace.mp horbit
  have hpre : IsCompact ((orbitHomeomorph x) ⁻¹' (Set.univ : Set (MulAction.orbit G x))) :=
    (orbitHomeomorph x).isCompact_preimage.mpr isCompact_univ
  have hGuniv : IsCompact (Set.univ : Set G) := by simpa using hpre
  exact hG ⟨hGuniv⟩

/-- Corollary 2.2: free proper noncompact gauge actions have noncompact closed orbit closures, so
no invariant action or observer--action pair is compact-preimage proper. -/
theorem freeProperNoncompact_gaugeOrbit_nonproperness
    [IsTopologicalGroup G] [LocallyCompactSpace G]
    {Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z]
    (hG : ¬ CompactSpace G) (q : X → Y) (S : X → Z)
    (hq : ∀ (g : G) (x : X), q (g • x) = q x) (hS : ∀ (g : G) (x : X), S (g • x) = S x) (x : X) :
    ¬ CompactPreimageProper S ∧ ¬ CompactPreimageProper (fun y ↦ (q y, S y)) := by
  apply gaugeOrbit_nonproperness q S hq hS x
  rw [closure_eq_iff_isClosed.mpr (orbit_isClosed x)]
  exact orbit_not_isCompact_of_group_not_compact hG x

end FreeProperAction

section Reduction

variable {X Q Y Z : Type*}
variable [TopologicalSpace X] [TopologicalSpace Q] [TopologicalSpace Y] [TopologicalSpace Z]

/-- Theorem 3.1(1): properness of an unreduced invariant pair implies properness of its reduced
factor through a continuous surjective quotient map. -/
theorem reducedPair_proper_of_unreducedPair_proper
    (π : X → Q) (qbar : Q → Y) (Sbar : Q → Z)
    (hπ : Continuous π) (hπsurj : Surjective π)
    (hunreduced : CompactPreimageProper (fun x ↦ (qbar (π x), Sbar (π x)))) :
    CompactPreimageProper (fun u ↦ (qbar u, Sbar u)) := by
  exact CompactPreimageProper.descend_of_comp hπ hπsurj (by simpa [Function.comp_def])

/-- If the quotient projection and reduced pair are proper, their unreduced composite is proper. -/
theorem unreducedPair_proper_of_projection_and_reducedPair_proper
    (π : X → Q) (qbar : Q → Y) (Sbar : Q → Z)
    (hπ : CompactPreimageProper π)
    (hreduced : CompactPreimageProper (fun u ↦ (qbar u, Sbar u))) :
    CompactPreimageProper (fun x ↦ (qbar (π x), Sbar (π x))) := by
  exact CompactPreimageProper.comp hreduced hπ

end Reduction

section CompactGroupReduction

variable {G X : Type*} [Group G] [MulAction G X]
variable [TopologicalSpace G] [TopologicalSpace X]
variable [ContinuousInv G] [ContinuousSMul G X] [CompactSpace G]

/-- An orbit of a compact continuously acting group is compact. -/
theorem orbit_isCompact_of_compact_group (x : X) : IsCompact (MulAction.orbit G x) := by
  have hrange : MulAction.orbit G x = Set.range (fun g : G ↦ g • x) := rfl
  rw [hrange, ← Set.image_univ]
  exact isCompact_univ.image (continuous_smul.comp (continuous_id.prodMk continuous_const))

/-- The orbit projection of a compact continuous group action is Bourbaki proper. -/
theorem compactGroup_orbitProjection_isProperMap :
    IsProperMap (Quotient.mk (MulAction.orbitRel G X)) := by
  rw [isProperMap_iff_isClosedMap_and_compact_fibers]
  refine ⟨continuous_quot_mk, MulAction.isClosedMap_quotient, ?_⟩
  intro u
  obtain ⟨x, rfl⟩ := Quotient.exists_rep u
  have hfiber :
      Quotient.mk (MulAction.orbitRel G X) ⁻¹' {Quotient.mk (MulAction.orbitRel G X) x}
        = MulAction.orbit G x := by
    ext y
    simp only [mem_preimage, mem_singleton_iff, Quotient.eq, MulAction.orbitRel_apply]
  rw [hfiber]
  exact orbit_isCompact_of_compact_group x

/-- Theorem 3.1(2), infrastructure clause: compact gauge-group orbit projection is proper in the
card's compact-preimage sense.  No local-compactness assumption on `X` is needed. -/
theorem compactGroup_orbitProjection_compactPreimageProper :
    CompactPreimageProper (Quotient.mk (MulAction.orbitRel G X)) :=
  CompactPreimageProper.of_isProperMap compactGroup_orbitProjection_isProperMap

/-- Theorem 3.1(2): reduced properness implies unreduced properness for a compact gauge group. -/
theorem compactGroup_unreducedPair_proper_of_reducedPair_proper
    {Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z]
    (qbar : Quotient (MulAction.orbitRel G X) → Y)
    (Sbar : Quotient (MulAction.orbitRel G X) → Z)
    (hreduced : CompactPreimageProper (fun u ↦ (qbar u, Sbar u))) :
    CompactPreimageProper
      (fun x ↦ (qbar (Quotient.mk (MulAction.orbitRel G X) x),
        Sbar (Quotient.mk (MulAction.orbitRel G X) x))) :=
  unreducedPair_proper_of_projection_and_reducedPair_proper
    (Quotient.mk (MulAction.orbitRel G X)) qbar Sbar
    compactGroup_orbitProjection_compactPreimageProper hreduced

end CompactGroupReduction

section ProductReductionWitness

/-- The left gauge action on the first factor of `G × Y`. -/
@[reducible] def firstFactorMulAction (G Y : Type*) [Group G] : MulAction G (G × Y) where
  smul g p := (g * p.1, p.2)
  one_smul p := by
    show ((1 : G) * p.1, p.2) = p
    simp
  mul_smul g h p := by
    show ((g * h) * p.1, p.2) = (g * (h * p.1), p.2)
    rw [mul_assoc]

variable {G Y Z : Type*} [Group G]

local instance : MulAction G (G × Y) := firstFactorMulAction G Y

/-- The first-factor action is free. -/
theorem firstFactorMulAction_isCancelSMul : IsCancelSMul G (G × Y) where
  right_cancel' g h p hgh := by
    exact mul_right_cancel (congrArg Prod.fst hgh)

/-- Its orbits are exactly the fibres of the second projection. -/
theorem mem_firstFactor_orbit_iff_snd_eq (p q : G × Y) :
    q ∈ MulAction.orbit G p ↔ q.2 = p.2 := by
  rw [MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨g, rfl⟩
    rfl
  · intro h
    refine ⟨q.1 * p.1⁻¹, ?_⟩
    show ((q.1 * p.1⁻¹) * p.1, p.2) = q
    rw [inv_mul_cancel_right]
    exact Prod.ext rfl h.symm

variable [TopologicalSpace G] [TopologicalSpace Y]

/-- Closed target cut out by equality of the two base coordinates. -/
def firstFactorActionRange : Set ((G × Y) × (G × Y)) :=
  {p | p.1.2 = p.2.2}

/-- The action graph is homeomorphic to its closed range. -/
def firstFactorActionHomeomorph [IsTopologicalGroup G] :
    G × (G × Y) ≃ₜ firstFactorActionRange (G := G) (Y := Y) where
  toFun p := ⟨((p.1 * p.2.1, p.2.2), p.2), rfl⟩
  invFun p := (p.1.1.1 * p.1.2.1⁻¹, p.1.2)
  left_inv p := by ext <;> simp
  right_inv p := by
    apply Subtype.ext
    rcases p with ⟨⟨⟨a, y⟩, ⟨b, y'⟩⟩, hy⟩
    simp only [firstFactorActionRange, mem_setOf_eq] at hy
    simp [hy]
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- The first-factor action is proper when the base is Hausdorff. -/
theorem firstFactorMulAction_proper [IsTopologicalGroup G] [T2Space Y] :
    ProperSMul G (G × Y) := by
  constructor
  have hrange : IsClosed (firstFactorActionRange (G := G) (Y := Y)) := by
    exact isClosed_eq (continuous_snd.comp continuous_fst) (continuous_snd.comp continuous_snd)
  have hemb : IsClosedEmbedding
      (fun p : G × (G × Y) ↦ ((p.1 * p.2.1, p.2.2), p.2)) := by
    exact hrange.isClosedEmbedding_subtypeVal.comp
      (firstFactorActionHomeomorph (G := G) (Y := Y)).isClosedEmbedding
  exact hemb.isProperMap

/-- The graph of a continuous map into a Hausdorff space is compact-preimage proper. -/
theorem graph_compactPreimageProper [TopologicalSpace Z] [T2Space Z]
    (Sbar : Y → Z) (hSbar : Continuous Sbar) :
    CompactPreimageProper (fun y ↦ (y, Sbar y)) := by
  apply CompactPreimageProper.of_isProperMap
  apply IsClosedEmbedding.isProperMap
  refine ⟨isEmbedding_graph hSbar, ?_⟩
  have hrange : Set.range (fun y ↦ (y, Sbar y)) = {p : Y × Z | Sbar p.1 = p.2} := by
    ext p
    constructor
    · rintro ⟨y, rfl⟩
      rfl
    · intro hp
      exact ⟨p.1, Prod.ext rfl hp⟩
  rw [hrange]
  exact isClosed_eq (hSbar.comp continuous_fst) continuous_snd

/-- A map constant along a noncompact first factor is not compact-preimage proper. -/
theorem firstFactor_invariantPair_not_compactPreimageProper
    [TopologicalSpace Z] [T1Space Y] [Nonempty Y]
    (hG : ¬ CompactSpace G) (Sbar : Y → Z) :
    ¬ CompactPreimageProper (fun p : G × Y ↦ (p.2, Sbar p.2)) := by
  intro hproper
  let y : Y := Classical.choice inferInstance
  have hfiber : IsCompact
      ((fun p : G × Y ↦ (p.2, Sbar p.2)) ⁻¹' ({(y, Sbar y)} : Set (Y × Z))) :=
    hproper isCompact_singleton
  have hverticalClosed : IsClosed ((Set.univ : Set G) ×ˢ ({y} : Set Y)) :=
    isClosed_univ.prod isClosed_singleton
  have hverticalSubset :
      (Set.univ : Set G) ×ˢ ({y} : Set Y) ⊆
        (fun p : G × Y ↦ (p.2, Sbar p.2)) ⁻¹' ({(y, Sbar y)} : Set (Y × Z)) := by
    rintro ⟨g, y'⟩ ⟨-, hy'⟩
    simp only [mem_singleton_iff] at hy'
    subst y'
    simp
  have hvertical : IsCompact ((Set.univ : Set G) ×ˢ ({y} : Set Y)) :=
    hfiber.of_isClosed_subset hverticalClosed hverticalSubset
  have hGuniv : IsCompact (Set.univ : Set G) := by
    have himage := hvertical.image continuous_fst
    rwa [Set.fst_image_prod _ (Set.singleton_nonempty y)] at himage
  exact hG ⟨hGuniv⟩

/-- Theorem 3.1(3): for the free proper first-factor action of a noncompact group, the reduced
observer--action graph is proper while its invariant lift is not. -/
theorem noncompactProduct_reducedProper_unreducedNotProper
    [IsTopologicalGroup G] [T2Space Y] [Nonempty Y]
    [TopologicalSpace Z] [T2Space Z]
    (hG : ¬ CompactSpace G) (Sbar : Y → Z) (hSbar : Continuous Sbar) :
    CompactPreimageProper (fun y ↦ (y, Sbar y)) ∧
      ¬ CompactPreimageProper (fun p : G × Y ↦ (p.2, Sbar p.2)) := by
  have _hfree : IsCancelSMul G (G × Y) := firstFactorMulAction_isCancelSMul
  have _hproper : ProperSMul G (G × Y) := firstFactorMulAction_proper
  exact ⟨graph_compactPreimageProper Sbar hSbar,
    firstFactor_invariantPair_not_compactPreimageProper hG Sbar⟩

end ProductReductionWitness

end HTGeometry.NomologicalHomotopyGeometry
