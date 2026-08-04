import GaloisForLFunctions.HTGeometry.RatFuncScaleFixedField

/-!
# Rational functions with infinitely many scaling symmetries

A nonconstant rational function generates a subfield of finite index in the rational coordinate
field, so its stabilizer inside the automorphism group is finite.  Hence a rational function fixed
by infinitely many scalings `X ↦ uX` is constant, and the fixed field of an infinite group of
scalings is the base field.

Unlike the cyclic statement this needs no element of infinite order: an infinite torsion group of
scalings — for instance all roots of unity of unbounded order — already collapses the fixed field.
-/

open Polynomial IntermediateField

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- **The scaling stabilizer of a nonconstant rational function is finite.**  The function generates
a subfield of finite index, whose fixing subgroup is finite, and distinct scalars act by distinct
automorphisms. -/
theorem finite_setOf_ratFuncUnitScale_fixed {K : Type*} [Field K] {r : RatFunc K}
    (hr : ¬ ∃ c : K, r = RatFunc.C c) :
    {u : Kˣ | ratFuncUnitScaleAction u r = r}.Finite := by
  classical
  let H : IntermediateField K (RatFunc K) := K⟮r⟯
  letI : FiniteDimensional H H⟮(RatFunc.X : RatFunc K)⟯ :=
    IntermediateField.adjoin.finiteDimensional
      ((r.isAlgebraic_adjoin_simple_X hr).isIntegral)
  letI : FiniteDimensional H (RatFunc K) :=
    Module.Finite.equiv (RatFunc.IntermediateField.adjoinXEquiv H).toLinearEquiv
  letI : Finite (RatFunc K ≃ₐ[H] RatFunc K) := by infer_instance
  letI : Finite H.fixingSubgroup :=
    Finite.of_injective (H.fixingSubgroupEquiv : H.fixingSubgroup →
      (RatFunc K ≃ₐ[H] RatFunc K)) H.fixingSubgroupEquiv.injective
  have hmem : ∀ u : Kˣ, ratFuncUnitScaleAction u r = r →
      ratFuncUnitScaleAction u ∈ H.fixingSubgroup := by
    intro u hu
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    change x ∈ IntermediateField.adjoin K ({r} : Set (RatFunc K)) at hx
    apply IntermediateField.adjoin_induction (F := K) (s := ({r} : Set (RatFunc K)))
      (p := fun y _ ↦ ratFuncUnitScaleAction u y = y)
    · intro y hy
      have hyr : y = r := Set.mem_singleton_iff.mp hy
      rw [hyr]
      exact hu
    · intro c
      exact (ratFuncUnitScaleAction u).commutes c
    · intro a b _ _ ha hb
      rw [map_add, ha, hb]
    · intro a _ ha
      rw [map_inv₀, ha]
    · intro a b _ _ ha hb
      rw [map_mul, ha, hb]
    · exact hx
  rw [← Set.finite_coe_iff]
  refine Finite.of_injective
    (fun u : {u : Kˣ // ratFuncUnitScaleAction u r = r} ↦
      (⟨ratFuncUnitScaleAction (u : Kˣ), hmem (u : Kˣ) u.2⟩ : H.fixingSubgroup)) ?_
  intro a b hab
  apply Subtype.ext
  have hact : ratFuncUnitScaleAction (a : Kˣ) = ratFuncUnitScaleAction (b : Kˣ) :=
    congrArg (fun x : H.fixingSubgroup ↦ (x : RatFunc K ≃ₐ[K] RatFunc K)) hab
  exact ratFuncUnitScaleAction_injective hact

/-- **A rational function with infinitely many scaling symmetries is constant.** -/
theorem ratFuncUnitScale_fixed_eq_constant_of_infinite {K : Type*} [Field K]
    {S : Set Kˣ} (hS : S.Infinite) {r : RatFunc K}
    (hr : ∀ u ∈ S, ratFuncUnitScaleAction u r = r) :
    ∃ c : K, r = RatFunc.C c := by
  by_contra hcon
  exact hS ((finite_setOf_ratFuncUnitScale_fixed hcon).subset hr)

/-- **The fixed field of an infinite group of scalings is the base field.** -/
theorem fixedField_map_ratFuncUnitScaleAction_of_infinite {K : Type*} [Field K]
    (S : Subgroup Kˣ) (hS : (S : Set Kˣ).Infinite) :
    IntermediateField.fixedField (S.map (ratFuncUnitScaleAction (K := K))) = ⊥ := by
  apply le_antisymm
  · intro r hr
    rw [IntermediateField.mem_fixedField_iff] at hr
    obtain ⟨c, hc⟩ := ratFuncUnitScale_fixed_eq_constant_of_infinite hS
      (fun u hu ↦ hr _ ⟨u, hu, rfl⟩)
    rw [hc]
    exact (⊥ : IntermediateField K (RatFunc K)).algebraMap_mem c
  · exact bot_le

end

end GaloisForLFunctions.HTGeometry
