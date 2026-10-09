import DifferentialGeometry.Topology.VanKampen.SimplyConnectedUnion
import Mathlib.GroupTheory.QuotientGroup.Basic
import GaloisForLFunctions.HTGeometry.FundamentalGroupTransport

/-!
# Fundamental group of a simply connected cap attachment

For an open cover by a path-connected body and a simply connected cap with
path-connected overlap, the body inclusion is onto on fundamental groups.
Its kernel is exactly the normal closure of the overlap image. These are
local ingredients for capping peripheral cycles; no global completion is assumed.
-/

open Set CategoryTheory
open DifferentialGeometry.Topology.VanKampen

namespace GaloisForLFunctions.HTGeometry

/-- Adding a simply connected open cap with path-connected overlap creates no loop classes. -/
theorem fundamentalGroup_inclusion_surjective_of_simplyConnected_cap
    {X : Type*} [TopologicalSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ)
    (x₀ : X) (hx₀ : x₀ ∈ U ∩ V)
    [PathConnectedSpace U] [SimplyConnectedSpace V]
    [PathConnectedSpace (↑(U ∩ V))] :
    Function.Surjective (fundamentalGroupLeftToAmbient U x₀ hx₀.1).hom := by
  let e := fundamentalGroupEquivAmalgamatedProduct U V hU hV hcover x₀ hx₀
  have hs : Function.Surjective
      (Monoid.PushoutI.of (φ := fundamentalGroupAmalgamation U V x₀ hx₀) false) := by
    intro z
    induction z using Monoid.PushoutI.induction_on with
    | of i g =>
        cases i with
        | false => exact ⟨g, rfl⟩
        | true =>
            have hg : g = 1 := Subsingleton.elim _ _
            refine ⟨1, ?_⟩
            rw [hg, map_one, map_one]
    | base c =>
        exact ⟨fundamentalGroupAmalgamation U V x₀ hx₀ false c,
          Monoid.PushoutI.of_apply_eq_base _ _ _⟩
    | mul a b ha hb =>
        obtain ⟨a', rfl⟩ := ha
        obtain ⟨b', rfl⟩ := hb
        exact ⟨a' * b', map_mul _ _ _⟩
  intro z
  obtain ⟨a, ha⟩ := hs (e.symm z)
  refine ⟨a, ?_⟩
  have he := DFunLike.congr_fun
    (fundamentalGroupEquivAmalgamatedProduct_comp_left U V hU hV hcover x₀ hx₀) a
  change e (Monoid.PushoutI.of false a) =
    (fundamentalGroupLeftToAmbient U x₀ hx₀.1).hom a at he
  rw [← he, ha, e.apply_symm_apply]

/-- The cap kills exactly the normal closure of the overlap's loop classes. -/
theorem fundamentalGroup_inclusion_ker_of_simplyConnected_cap
    {X : Type*} [TopologicalSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ)
    (x₀ : X) (hx₀ : x₀ ∈ U ∩ V)
    [PathConnectedSpace U] [SimplyConnectedSpace V]
    [PathConnectedSpace (↑(U ∩ V))] :
    (fundamentalGroupLeftToAmbient U x₀ hx₀.1).hom.ker =
      Subgroup.normalClosure (Set.range (fundamentalGroupInterToLeft U V x₀ hx₀).hom) := by
  let f := (fundamentalGroupLeftToAmbient U x₀ hx₀.1).hom
  let k := (fundamentalGroupInterToLeft U V x₀ hx₀).hom
  let N := Subgroup.normalClosure (Set.range k)
  have hk : Set.range k ⊆ f.ker := by
    rintro _ ⟨c, rfl⟩
    change f (k c) = 1
    have hc := DFunLike.congr_fun (congrArg GrpCat.Hom.hom
      (fundamentalGroup_coverSquare_commutes U V x₀ hx₀)) c
    have hr : (fundamentalGroupInterToRight U V x₀ hx₀).hom c = 1 :=
      Subsingleton.elim _ _
    change f (k c) = (fundamentalGroupRightToAmbient V x₀ hx₀.2).hom
      ((fundamentalGroupInterToRight U V x₀ hx₀).hom c) at hc
    simpa only [hr, map_one] using hc
  have hN : N ≤ f.ker := Subgroup.normalClosure_le_normal hk
  apply le_antisymm
  · intro a ha
    let q : FundamentalGroup U (leftBasepoint U x₀ hx₀.1) →*
        (FundamentalGroup U (leftBasepoint U x₀ hx₀.1)) ⧸ N := QuotientGroup.mk' N
    have hq : ∀ c, q (k c) = 1 := by
      intro c
      exact (QuotientGroup.eq_one_iff _).2 (Subgroup.subset_normalClosure ⟨c, rfl⟩)
    have hcompat : fundamentalGroupInterToLeft U V x₀ hx₀ ≫ GrpCat.ofHom q =
        fundamentalGroupInterToRight U V x₀ hx₀ ≫ GrpCat.ofHom 1 := by
      apply GrpCat.ext
      intro c
      exact hq c
    let hp := fundamentalGroup_isPushout U V hU hV hcover x₀ hx₀
    let d := hp.desc (GrpCat.ofHom q) (GrpCat.ofHom 1) hcompat
    have hd := DFunLike.congr_fun (congrArg GrpCat.Hom.hom
      (hp.inl_desc (GrpCat.ofHom q) (GrpCat.ofHom 1) hcompat)) a
    change d.hom (f a) = q a at hd
    have ha' : f a = 1 := ha
    have hqa : q a = 1 := by simpa only [ha', map_one] using hd.symm
    exact (QuotientGroup.eq_one_iff _).1 hqa
  · exact hN

/-- The cap-surjection statement at any basepoint in the body. -/
theorem fundamentalGroup_inclusion_surjective_of_simplyConnected_cap_at
    {X : Type*} [TopologicalSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ)
    (hinter : (U ∩ V).Nonempty)
    [PathConnectedSpace U] [SimplyConnectedSpace V]
    [PathConnectedSpace (↑(U ∩ V))] (a : U) :
    Function.Surjective (FundamentalGroup.map (subsetToAmbient U) a) := by
  obtain ⟨b, hb⟩ := hinter
  have hs := fundamentalGroup_inclusion_surjective_of_simplyConnected_cap
    U V hU hV hcover b hb
  have hs' : Function.Surjective
      (FundamentalGroup.map (subsetToAmbient U) (⟨b, hb.1⟩ : U)) := by
    intro z
    obtain ⟨q, hq⟩ := hs z
    refine ⟨q, ?_⟩
    change FundamentalGroup.mapOfEq (subsetToAmbient U) rfl q = z at hq
    rw [FundamentalGroup.mapOfEq_apply, Path.Homotopic.Quotient.cast_rfl_rfl] at hq
    exact hq
  let p := PathConnectedSpace.somePath (⟨b, hb.1⟩ : U) a
  let e := FundamentalGroup.fundamentalGroupMulEquivOfPath
    (p.map (subsetToAmbient U).continuous)
  intro z
  obtain ⟨q, hq⟩ := hs' (e.symm z)
  refine ⟨FundamentalGroup.fundamentalGroupMulEquivOfPath p q, ?_⟩
  rw [fundamentalGroup_map_transport, hq]
  exact e.apply_symm_apply z


/-- A loop class in a directed open union comes from a single cover member. -/
theorem fundamentalGroup_exists_preimage_of_directed_open_cover
    {X : Type*} [TopologicalSpace X] {ι : Type*} [Nonempty ι]
    (W : ι → Set X) (hWo : ∀ i, IsOpen (W i))
    (hWcover : (⋃ i, W i) = univ) (hWdir : Directed (· ⊆ ·) W)
    (x : X) (p : FundamentalGroup X x) :
    ∃ (i : ι) (hx : x ∈ W i) (q : FundamentalGroup (W i) ⟨x, hx⟩),
      FundamentalGroup.map (subsetToAmbient (W i)) ⟨x, hx⟩ q = p := by
  induction p using Quotient.inductionOn with
  | _ γ =>
      obtain ⟨i, hi⟩ := (isCompact_range γ.continuous).elim_directed_cover W hWo
        (by rw [hWcover]; exact subset_univ _) hWdir
      have hx : x ∈ W i := by
        simpa only [γ.source] using hi (mem_range_self (f := γ) 0)
      let γi : Path (⟨x, hx⟩ : W i) ⟨x, hx⟩ :=
        { toFun := fun t => ⟨γ t, hi (mem_range_self t)⟩
          continuous_toFun := γ.continuous.subtype_mk _
          source' := Subtype.ext γ.source
          target' := Subtype.ext γ.target }
      refine ⟨i, hx, FundamentalGroup.fromPath ⟦γi⟧, ?_⟩
      change ⟦γi.map continuous_subtype_val⟧ = ⟦γ⟧
      congr 1

end GaloisForLFunctions.HTGeometry
