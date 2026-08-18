import GaloisForLFunctions.HTGeometry.GroupActionGeneration
import GaloisForLFunctions.HTGeometry.FinitelyPresentedBasic
import Mathlib.GroupTheory.PresentedGroup

/-!
# Macbeath's presentation of a group acting with a fundamental open set

For a group acting on a space with an open set `V` whose translates cover, the elements moving `V`
to a set meeting `V` generate (`closure_meetSet_eq_top`).  Macbeath's theorem says that they present
the group, the relations being the obvious ones: `s_a · s_b = s_{ab}` whenever `a`, `b`, `ab` all
move `V` to a set meeting `V` and the three translates `V`, `a·V`, `ab·V` have a common point.

This file builds the presented group, the canonical surjection onto the acting group, and the
observation that the presentation is **finite** as soon as only finitely many elements move `V` to a
set meeting `V` — which is what a cocompact, properly discontinuous action provides.

* `macbeathRels`, `MacbeathGroup` : the presentation.
* `macbeathHom`, `macbeathHom_surjective` : the canonical surjection onto the acting group.
* `isFinitelyPresented_macbeathGroup` : **finitely many overlaps give a finite presentation.**
-/

namespace GaloisForLFunctions.HTGeometry

open Set Pointwise

variable {G X : Type*} [Group G] [TopologicalSpace X] [MulAction G X] [ContinuousConstSMul G X]

/-- Macbeath's relators: `s_a · s_b · s_{ab}⁻¹` whenever `V`, `a·V` and `ab·V` have a common
point. -/
def macbeathRels (V : Set X) : Set (FreeGroup (meetSet (G := G) V)) :=
  {w | ∃ a b c : meetSet (G := G) V, ((a : G) * (b : G) = (c : G)) ∧
    (((a : G) • V) ∩ (((a : G) * (b : G)) • V) ∩ V).Nonempty ∧
    w = FreeGroup.of a * FreeGroup.of b * (FreeGroup.of c)⁻¹}

/-- **Macbeath's group**: the group presented by the elements that move `V` to a set meeting `V`,
subject to the relations coming from triple overlaps. -/
def MacbeathGroup (V : Set X) : Type _ := PresentedGroup (macbeathRels (G := G) V)

instance (V : Set X) : Group (MacbeathGroup (G := G) V) := by
  unfold MacbeathGroup
  infer_instance

omit [TopologicalSpace X] [ContinuousConstSMul G X] in
/-- A generator of Macbeath's group. -/
def macbeathOf (V : Set X) (s : meetSet (G := G) V) : MacbeathGroup (G := G) V :=
  PresentedGroup.of s

omit [TopologicalSpace X] [ContinuousConstSMul G X] in
/-- The relators are relations in the acting group. -/
theorem macbeathRels_lift (V : Set X) :
    ∀ r ∈ macbeathRels (G := G) V,
      FreeGroup.lift (fun s : meetSet (G := G) V => (s : G)) r = 1 := by
  rintro r ⟨a, b, c, habc, -, rfl⟩
  simp only [map_mul, map_inv]
  simp only [show ∀ x : meetSet (G := G) V,
    (FreeGroup.lift fun s : meetSet (G := G) V => (s : G)) (FreeGroup.of x) = (x : G) from
      fun x => by simp]
  rw [habc, mul_inv_cancel]

/-- **The canonical surjection of Macbeath's group onto the acting group.** -/
def macbeathHom (V : Set X) : MacbeathGroup (G := G) V →* G :=
  PresentedGroup.toGroup (macbeathRels_lift V)

omit [TopologicalSpace X] [ContinuousConstSMul G X] in
@[simp]
theorem macbeathHom_of (V : Set X) (s : meetSet (G := G) V) :
    macbeathHom V (macbeathOf V s) = (s : G) :=
  PresentedGroup.toGroup.of _

theorem macbeathHom_surjective [ConnectedSpace X] {V : Set X} (hVopen : IsOpen V)
    (hVne : V.Nonempty) (hcover : ⋃ g : G, g • V = (univ : Set X)) :
    Function.Surjective (macbeathHom (G := G) V) := by
  rw [← MonoidHom.range_eq_top]
  refine top_le_iff.1 ?_
  rw [← closure_meetSet_eq_top hVopen hVne hcover]
  refine (Subgroup.closure_le _).2 ?_
  intro g hg
  exact ⟨macbeathOf V ⟨g, hg⟩, macbeathHom_of V ⟨g, hg⟩⟩

omit [TopologicalSpace X] [ContinuousConstSMul G X] in
theorem macbeathRels_finite {V : Set X} (hfin : (meetSet (G := G) V).Finite) :
    (macbeathRels (G := G) V).Finite := by
  classical
  haveI : Finite (meetSet (G := G) V) := hfin.to_subtype
  refine Set.Finite.subset (Set.finite_range (fun p : meetSet (G := G) V × meetSet (G := G) V
      × meetSet (G := G) V =>
    FreeGroup.of p.1 * FreeGroup.of p.2.1 * (FreeGroup.of p.2.2)⁻¹)) ?_
  rintro w ⟨a, b, c, -, -, rfl⟩
  exact ⟨(a, b, c), rfl⟩

omit [TopologicalSpace X] [ContinuousConstSMul G X] in
/-- **Finitely many overlaps give a finite presentation.** -/
theorem isFinitelyPresented_macbeathGroup {V : Set X} (hfin : (meetSet (G := G) V).Finite) :
    IsFinitelyPresented (MacbeathGroup (G := G) V) := by
  haveI : Finite (meetSet (G := G) V) := hfin.to_subtype
  refine isFinitelyPresented_of_free_presentation
    (QuotientGroup.mk' (Subgroup.normalClosure (macbeathRels (G := G) V)))
    (QuotientGroup.mk'_surjective _) (macbeathRels_finite hfin) ?_
  exact QuotientGroup.ker_mk' _

/-- **Macbeath's criterion, in the form it is used.**  If the overlaps are finite and the canonical
surjection from Macbeath's group is injective, the acting group is finitely presented. -/
theorem isFinitelyPresented_of_macbeathHom_injective [ConnectedSpace X] {V : Set X}
    (hVopen : IsOpen V) (hVne : V.Nonempty) (hcover : ⋃ g : G, g • V = (univ : Set X))
    (hfin : (meetSet (G := G) V).Finite)
    (hinj : Function.Injective (macbeathHom (G := G) V)) :
    IsFinitelyPresented G :=
  IsFinitelyPresented.of_mulEquiv
    (MulEquiv.ofBijective _ ⟨hinj, macbeathHom_surjective hVopen hVne hcover⟩)
    (isFinitelyPresented_macbeathGroup hfin)

omit [ContinuousConstSMul G X] in
/-- A properly discontinuous action with a relatively compact fundamental open set has finite
overlaps. -/
theorem meetSet_finite_of_properlyDiscontinuousSMul [ProperlyDiscontinuousSMul G X] {V K : Set X}
    (hVK : V ⊆ K) (hK : IsCompact K) : (meetSet (G := G) V).Finite := by
  refine Set.Finite.subset
    (ProperlyDiscontinuousSMul.finite_disjoint_inter_image (Γ := G) hK hK) ?_
  rintro g ⟨x, hx1, hx2⟩
  refine ⟨x, ?_, hVK hx2⟩
  rw [Set.image_smul]
  exact Set.smul_set_mono hVK hx1

/-- **Macbeath's criterion for a properly discontinuous, cocompact action.** -/
theorem isFinitelyPresented_of_properlyDiscontinuousSMul [ConnectedSpace X]
    [ProperlyDiscontinuousSMul G X] {V K : Set X} (hVopen : IsOpen V) (hVne : V.Nonempty)
    (hVK : V ⊆ K) (hK : IsCompact K) (hcover : ⋃ g : G, g • V = (univ : Set X))
    (hinj : Function.Injective (macbeathHom (G := G) V)) :
    IsFinitelyPresented G :=
  isFinitelyPresented_of_macbeathHom_injective hVopen hVne hcover
    (meetSet_finite_of_properlyDiscontinuousSMul hVK hK) hinj

omit [TopologicalSpace X] [ContinuousConstSMul G X] in
/-- The overlap set is symmetric. -/
theorem inv_mem_meetSet {V : Set X} {g : G} (h : g ∈ meetSet V) : g⁻¹ ∈ meetSet V := by
  obtain ⟨x, hx1, hx2⟩ := h
  obtain ⟨y, hy, rfl⟩ := hx1
  refine ⟨y, ?_, hy⟩
  have : g⁻¹ • (g • y) ∈ g⁻¹ • V := smul_mem_smul_set hx2
  simpa using this

omit [TopologicalSpace X] [ContinuousConstSMul G X] in
/-- **The defining relation of Macbeath's group**, read in the presented group. -/
theorem macbeathOf_mul (V : Set X) (a b c : meetSet (G := G) V)
    (habc : (a : G) * (b : G) = (c : G))
    (hov : (((a : G) • V) ∩ (((a : G) * (b : G)) • V) ∩ V).Nonempty) :
    macbeathOf V a * macbeathOf V b = macbeathOf V c := by
  have hmem : (FreeGroup.of a * FreeGroup.of b * (FreeGroup.of c)⁻¹) ∈ macbeathRels (G := G) V :=
    ⟨a, b, c, habc, hov, rfl⟩
  have hq : (QuotientGroup.mk (FreeGroup.of a * FreeGroup.of b * (FreeGroup.of c)⁻¹) :
      MacbeathGroup (G := G) V) = 1 :=
    (QuotientGroup.eq_one_iff _).2 (Subgroup.subset_normalClosure hmem)
  rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, mul_inv_eq_one] at hq
  exact hq

omit [TopologicalSpace X] [ContinuousConstSMul G X] in
/-- **The generator at the identity is the identity.** -/
theorem macbeathOf_one {V : Set X} (hVne : V.Nonempty) :
    macbeathOf V ⟨(1 : G), one_mem_meetSet hVne⟩ = 1 := by
  have hov : (((1 : G) • V) ∩ (((1 : G) * (1 : G)) • V) ∩ V).Nonempty := by
    obtain ⟨x, hx⟩ := hVne
    exact ⟨x, ⟨by simpa using hx, by simpa using hx⟩, hx⟩
  have h := macbeathOf_mul V ⟨(1 : G), one_mem_meetSet hVne⟩ ⟨(1 : G), one_mem_meetSet hVne⟩
    ⟨(1 : G), one_mem_meetSet hVne⟩ (by simp) hov
  have h2 : macbeathOf V ⟨(1 : G), one_mem_meetSet hVne⟩
      * macbeathOf V ⟨(1 : G), one_mem_meetSet hVne⟩
      = macbeathOf V ⟨(1 : G), one_mem_meetSet hVne⟩ * 1 := by
    rw [mul_one]; exact h
  exact mul_left_cancel h2

omit [TopologicalSpace X] [ContinuousConstSMul G X] in
/-- **The generator at an inverse is the inverse generator.** -/
theorem macbeathOf_inv {V : Set X} (hVne : V.Nonempty) (g : meetSet (G := G) V) :
    macbeathOf V ⟨((g : G))⁻¹, inv_mem_meetSet g.2⟩ = (macbeathOf V g)⁻¹ := by
  have hov : (((g : G) • V) ∩ (((g : G) * ((g : G))⁻¹) • V) ∩ V).Nonempty := by
    obtain ⟨x, hx1, hx2⟩ := g.2
    exact ⟨x, ⟨hx1, by simpa using hx2⟩, hx2⟩
  have h := macbeathOf_mul V g ⟨((g : G))⁻¹, inv_mem_meetSet g.2⟩
    ⟨(1 : G), one_mem_meetSet hVne⟩ (by simp) hov
  rw [macbeathOf_one hVne] at h
  exact eq_inv_of_mul_eq_one_right h

end GaloisForLFunctions.HTGeometry
