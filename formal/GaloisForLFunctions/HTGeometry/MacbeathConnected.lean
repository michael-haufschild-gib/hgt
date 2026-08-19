import GaloisForLFunctions.HTGeometry.MacbeathCovering

/-!
# The developed space is connected

Each sheet of the developed space is a continuous image of `V`, hence connected when `V` is; and the
sheets at `g` and at `g · s_γ` always meet, because a point of the overlap `V ∩ γ·V` lies on both.
Since the generators `s_γ` generate Macbeath's group, all the sheets lie in one connected component,
and they exhaust the space.

* `isPreconnected_sheet` : a sheet is connected.
* `preconnectedSpace_devSpace` : **the developed space is connected.**
-/

namespace GaloisForLFunctions.HTGeometry

open Set Pointwise Topology

variable {G X : Type*} [Group G] [TopologicalSpace X] [MulAction G X] [ContinuousConstSMul G X]

omit [TopologicalSpace X] [ContinuousConstSMul G X] in
theorem sheetImage_self_eq_range (V : Set X) (g : MacbeathGroup (G := G) V) :
    sheetImage (G := G) V g V
      = Set.range (fun y : V => (Quot.mk (DevRel (G := G) V) ⟨g, y⟩ : DevSpace (G := G) V)) := by
  ext z
  constructor
  · rintro ⟨y, -, rfl⟩
    exact ⟨y, rfl⟩
  · rintro ⟨y, rfl⟩
    exact ⟨y, y.2, rfl⟩

omit [ContinuousConstSMul G X] in
/-- A sheet of the developed space is connected. -/
theorem isPreconnected_sheet {V : Set X} (hVconn : IsPreconnected V)
    (g : MacbeathGroup (G := G) V) : IsPreconnected (sheetImage (G := G) V g V) := by
  haveI : PreconnectedSpace V := Subtype.preconnectedSpace hVconn
  rw [sheetImage_self_eq_range]
  exact isPreconnected_range (continuous_quot_mk.comp (continuous_sigmaMk (i := g)))

omit [ContinuousConstSMul G X] in
/-- **The developed space is connected.** -/
theorem preconnectedSpace_devSpace {V : Set X} (hVne : V.Nonempty) (hVconn : IsPreconnected V) :
    PreconnectedSpace (DevSpace (G := G) V) := by
  classical
  obtain ⟨x₀, hx₀⟩ := hVne
  set y₀ : DevSpace (G := G) V := Quot.mk _ ⟨1, ⟨x₀, hx₀⟩⟩ with hy₀
  set P : MacbeathGroup (G := G) V → Prop :=
    fun g => sheetImage (G := G) V g V ⊆ connectedComponent y₀ with hP
  have hsub : ∀ g : MacbeathGroup (G := G) V,
      (sheetImage (G := G) V g V ∩ connectedComponent y₀).Nonempty → P g := by
    rintro g ⟨z, hz1, hz2⟩
    have hcc : connectedComponent z = connectedComponent y₀ := (connectedComponent_eq hz2).symm
    rw [hP, ← hcc]
    exact (isPreconnected_sheet hVconn g).subset_connectedComponent hz1
  have hP1 : P 1 :=
    hsub 1 ⟨y₀, ⟨⟨x₀, hx₀⟩, hx₀, rfl⟩, mem_connectedComponent⟩
  have hstep : ∀ (g : MacbeathGroup (G := G) V) (γ : meetSet (G := G) V),
      P g → P (g * macbeathOf V γ) := by
    intro g γ hg
    obtain ⟨z, hz1, hz2⟩ := γ.2
    obtain ⟨w, hw, hwz⟩ := hz1
    refine hsub _ ⟨Quot.mk _ ⟨g * macbeathOf V γ, ⟨w, hw⟩⟩, ⟨⟨w, hw⟩, hw, rfl⟩, ?_⟩
    have hlink : (Quot.mk (DevRel (G := G) V) ⟨g, ⟨z, hz2⟩⟩ : DevSpace (G := G) V)
        = Quot.mk _ ⟨g * macbeathOf V γ, ⟨w, hw⟩⟩ := by
      refine Quot.sound ?_
      refine DevRel.move g γ ⟨z, hz2⟩ ⟨w, hw⟩ ?_
      show w = ((γ : G))⁻¹ • z
      rw [← hwz, inv_smul_smul]
    rw [← hlink]
    exact hg ⟨⟨z, hz2⟩, hz2, rfl⟩
  set H : Subgroup (MacbeathGroup (G := G) V) :=
    { carrier := {a | ∀ k, P k ↔ P (k * a)}
      one_mem' := by intro k; rw [mul_one]
      mul_mem' := by
        intro a b ha hb k
        rw [← mul_assoc]
        exact (ha k).trans (hb (k * a))
      inv_mem' := by
        intro a ha k
        have h2 := ha (k * a⁻¹)
        rw [inv_mul_cancel_right] at h2
        exact h2.symm } with hH
  have hgen : ∀ γ : meetSet (G := G) V, macbeathOf V γ ∈ H := by
    intro γ k
    refine ⟨hstep k γ, ?_⟩
    intro hk
    have hinv := hstep (k * macbeathOf V γ) ⟨((γ : G))⁻¹, inv_mem_meetSet γ.2⟩ hk
    rwa [mul_assoc, show macbeathOf V ⟨((γ : G))⁻¹, inv_mem_meetSet γ.2⟩
      = (macbeathOf V γ)⁻¹ from macbeathOf_inv ⟨x₀, hx₀⟩ γ, mul_inv_cancel, mul_one] at hinv
  have hHtop : H = ⊤ := by
    refine top_le_iff.1 ?_
    rw [show (⊤ : Subgroup (MacbeathGroup (G := G) V))
        = Subgroup.closure (Set.range (PresentedGroup.of :
          meetSet (G := G) V → MacbeathGroup (G := G) V)) from
      (PresentedGroup.closure_range_of (macbeathRels (G := G) V)).symm]
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨γ, rfl⟩
    exact hgen γ
  have hall : ∀ g : MacbeathGroup (G := G) V, P g := by
    intro g
    have hg : g ∈ H := by rw [hHtop]; trivial
    have h1 := (hg 1).1 hP1
    rwa [one_mul] at h1
  have huniv : (univ : Set (DevSpace (G := G) V)) ⊆ connectedComponent y₀ := by
    intro z _
    obtain ⟨p, rfl⟩ := Quot.exists_rep z
    exact hall p.1 ⟨p.2, p.2.2, rfl⟩
  have hCuniv : connectedComponent y₀ = (univ : Set (DevSpace (G := G) V)) :=
    Subset.antisymm (subset_univ _) huniv
  refine ⟨?_⟩
  rw [← hCuniv]
  exact isPreconnected_connectedComponent

/-- **MACBEATH'S THEOREM.**  For a group acting on a simply connected, locally path-connected space
with a connected fundamental open set, the canonical map from Macbeath's group is injective — so the
overlaps of the fundamental open set **present** the group. -/
theorem macbeathHom_injective [SimplyConnectedSpace X] [LocallyPathConnectedSpace X]
    [ConnectedSpace X] {V : Set X} (hVopen : IsOpen V) (hVne : V.Nonempty)
    (hVconn : IsPreconnected V) (hcover : ⋃ g : G, g • V = (univ : Set X)) :
    Function.Injective (macbeathHom (G := G) V) := by
  haveI : PreconnectedSpace (DevSpace (G := G) V) := preconnectedSpace_devSpace hVne hVconn
  obtain ⟨x₀, hx₀⟩ := hVne
  exact macbeathHom_injective_of_isCoveringMap ⟨x₀, hx₀⟩
    (isCoveringMap_devMap hVopen ⟨x₀, hx₀⟩ hcover)
    (Quot.mk _ ⟨1, ⟨x₀, hx₀⟩⟩)

/-- **A group acting properly discontinuously and cocompactly on a simply connected, locally
path-connected space, with a connected fundamental open set, is FINITELY PRESENTED.** -/
theorem isFinitelyPresented_of_macbeath [SimplyConnectedSpace X] [LocallyPathConnectedSpace X]
    [ConnectedSpace X] [ProperlyDiscontinuousSMul G X] {V K : Set X}
    (hVopen : IsOpen V) (hVne : V.Nonempty) (hVconn : IsPreconnected V) (hVK : V ⊆ K)
    (hK : IsCompact K) (hcover : ⋃ g : G, g • V = (univ : Set X)) :
    IsFinitelyPresented G :=
  isFinitelyPresented_of_properlyDiscontinuousSMul hVopen hVne hVK hK hcover
    (macbeathHom_injective hVopen hVne hVconn hcover)

end GaloisForLFunctions.HTGeometry
