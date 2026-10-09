import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Covering.Quotient

/-!
# A universal covering as a quotient by its full deck group

Unique lifting constructs the homeomorphism between two prescribed sheets.
Covering-preserving homeomorphisms act freely, continuously, and transitively
on each fiber, so a surjective universal cover is a quotient covering by
this intrinsic group. No prior identification of a modular deck group is used.
-/

open Topology

namespace GaloisForLFunctions.HTGeometry

/-- A universal covering has one covering-preserving homeomorphism carrying a prescribed
point to any other point in its fiber. -/
theorem existsUnique_covering_homeomorph_of_same_fiber
    {E B : Type*} [TopologicalSpace E] [TopologicalSpace B]
    [SimplyConnectedSpace E] [LocallyPathConnectedSpace E]
    {p : E → B} (hp : IsCoveringMap p) (e₀ e₁ : E) (he : p e₁ = p e₀) :
    ∃! d : E ≃ₜ E, d e₀ = e₁ ∧ ∀ e, p (d e) = p e := by
  let f : C(E, B) := ⟨p, hp.continuous⟩
  obtain ⟨d, ⟨hd0, hdp⟩, hdunique⟩ := hp.existsUnique_continuousMap_lifts f e₀ e₁ he
  obtain ⟨d', ⟨hd1, hdp'⟩, -⟩ := hp.existsUnique_continuousMap_lifts f e₁ e₀ he.symm
  have hleft : (d' : E → E) ∘ d = id := by
    refine hp.eq_of_comp_eq (d'.continuous.comp d.continuous) continuous_id ?_ e₀ ?_
    · funext e
      change p (d' (d e)) = p e
      exact (congrFun hdp' (d e)).trans (congrFun hdp e)
    · change d' (d e₀) = e₀
      rw [hd0, hd1]
  have hright : (d : E → E) ∘ d' = id := by
    refine hp.eq_of_comp_eq (d.continuous.comp d'.continuous) continuous_id ?_ e₁ ?_
    · funext e
      change p (d (d' e)) = p e
      exact (congrFun hdp (d' e)).trans (congrFun hdp' e)
    · change d (d' e₁) = e₁
      rw [hd1, hd0]
  let D : E ≃ₜ E :=
    { toFun := d
      invFun := d'
      left_inv := fun e => congrFun hleft e
      right_inv := fun e => congrFun hright e
      continuous_toFun := d.continuous
      continuous_invFun := d'.continuous }
  refine ⟨D, ⟨hd0, fun e => congrFun hdp e⟩, ?_⟩
  intro D' hD'
  have hd' : (⟨D', D'.continuous⟩ : C(E, E)) = d :=
    hdunique (⟨D', D'.continuous⟩ : C(E, E)) ⟨hD'.1, funext hD'.2⟩
  ext e
  exact DFunLike.congr_fun hd' e

/-- The homeomorphisms preserving the covering projection. -/
def coveringDeckGroup {E B : Type*} [TopologicalSpace E] [TopologicalSpace B]
    (p : E → B) : Subgroup (E ≃ₜ E) where
  carrier := {d | ∀ e, p (d e) = p e}
  one_mem' := fun _ => rfl
  mul_mem' := by
    intro d d' hd hd' e
    exact (hd (d' e)).trans (hd' e)
  inv_mem' := by
    intro d hd e
    simpa only [Homeomorph.inv_apply, Homeomorph.apply_symm_apply] using (hd (d.symm e)).symm

instance coveringDeckGroupMulAction {E B : Type*} [TopologicalSpace E] [TopologicalSpace B]
    (p : E → B) : MulAction (coveringDeckGroup p) E where
  smul d e := d.1 e
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

instance coveringDeckGroupContinuousConstSMul {E B : Type*}
    [TopologicalSpace E] [TopologicalSpace B] (p : E → B) :
    ContinuousConstSMul (coveringDeckGroup p) E where
  continuous_const_smul d := d.1.continuous

/-- A deck action on a connected covering is free. -/
theorem coveringDeckGroup_isCancelSMul
    {E B : Type*} [TopologicalSpace E] [TopologicalSpace B] [PreconnectedSpace E]
    {p : E → B} (hp : IsCoveringMap p) : IsCancelSMul (coveringDeckGroup p) E where
  right_cancel' d d' e he := by
    have hdd : (d.1 : E → E) = d'.1 := hp.eq_of_comp_eq
      d.1.continuous d'.1.continuous
      (funext fun x => (d.2 x).trans (d'.2 x).symm) e he
    apply Subtype.ext
    ext x
    exact congrFun hdd x

/-- On a universal cover, deck orbits are exactly the fibers. -/
theorem coveringDeckGroup_orbit_iff
    {E B : Type*} [TopologicalSpace E] [TopologicalSpace B]
    [SimplyConnectedSpace E] [LocallyPathConnectedSpace E]
    {p : E → B} (hp : IsCoveringMap p) (e e' : E) :
    p e = p e' ↔ e ∈ MulAction.orbit (coveringDeckGroup p) e' := by
  constructor
  · intro he
    obtain ⟨d, ⟨hd, hdp⟩, -⟩ := existsUnique_covering_homeomorph_of_same_fiber hp e' e he
    exact ⟨⟨d, hdp⟩, hd⟩
  · rintro ⟨d, rfl⟩
    exact d.2 e'

/-- The deck group presents a surjective universal covering as a quotient covering. -/
theorem isQuotientCoveringMap_coveringDeckGroup
    {E B : Type*} [TopologicalSpace E] [TopologicalSpace B]
    [SimplyConnectedSpace E] [LocallyPathConnectedSpace E]
    {p : E → B} (hp : IsCoveringMap p) (hsurj : Function.Surjective p) :
    IsQuotientCoveringMap p (coveringDeckGroup p) := by
  exact (isQuotientCoveringMap_iff_isCoveringMap_and p (coveringDeckGroup p)).mpr
    ⟨hp, hsurj, inferInstance, coveringDeckGroup_isCancelSMul hp,
      fun {e e'} => coveringDeckGroup_orbit_iff hp e e'⟩

end GaloisForLFunctions.HTGeometry
