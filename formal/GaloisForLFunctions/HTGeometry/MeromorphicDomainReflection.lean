import GaloisForLFunctions.HTGeometry.MeromorphicDomainField
import GaloisForLFunctions.HTGeometry.MeromorphicPlaneReflection

/-!
# Point reflection on the meromorphic field of a symmetric domain

Let `D` be a nonempty connected open subset of `ℂ` and `c ∈ ℂ` such that `z ∈ D` implies
`c - z ∈ D`. The reflection `z ↦ c - z` preserves the codiscrete filter of `D` and induces a ring
endomorphism `f ↦ f(c - ·)` of the field of meromorphic functions on `D`. It is an involution,
hence a ring automorphism, and it is compatible with the restriction map from the meromorphic field
of the plane and the plane reflection.

## Main results

- `reflectHom`: the ring endomorphism `f ↦ f(c - ·)` of `D.Field`.
- `reflectHom_involutive`, `reflectEquiv`: it is an involution, packaged as a ring automorphism.
- `reflectEquiv_restrictPlane`: reflecting the restriction of a plane meromorphic function equals
  restricting its plane reflection.

## Hypotheses

All results are unconditional apart from the symmetry hypothesis `hc : ∀ z ∈ D.carrier,
c - z ∈ D.carrier`, which is needed for `f(c - ·)` to be defined on `D`.
-/

open Filter Topology
namespace GaloisForLFunctions.HTGeometry.MeromorphicDomainData
noncomputable section
variable (D : MeromorphicDomainData) (c : ℂ)
variable (hc : ∀ z ∈ D.carrier, c - z ∈ D.carrier)

include hc in
/-- For `D` symmetric about `c / 2`, the reflection `z ↦ c - z` maps the codiscrete filter of `D`
to itself. -/
theorem tendsto_const_sub_codiscrete :
    Tendsto (fun z : ℂ => c - z) D.codiscrete D.codiscrete := by
  refine Filter.tendsto_def.mpr fun S hS => ?_
  refine D.mem_codiscrete.mpr fun x hx => ?_
  have ht : Tendsto (fun w : ℂ => c - w) (𝓝[≠] x) (𝓝[≠] (c - x)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · exact ((by fun_prop : Continuous fun w : ℂ => c - w).tendsto x).mono_left
        nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with w hw
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro he
      exact hw (sub_right_injective he)
  exact ht ((D.mem_codiscrete.mp hS) (c - x) (hc x hx))

private def reflectGerm : Germ D.codiscrete ℂ →+* Germ D.codiscrete ℂ where
  toFun a := a.compTendsto (fun z => c - z) (D.tendsto_const_sub_codiscrete c hc)
  map_one' := by rw [← Germ.coe_one, Germ.coe_compTendsto]; rfl
  map_zero' := by rw [← Germ.coe_zero, Germ.coe_compTendsto]; rfl
  map_mul' a b := by
    induction a using Germ.inductionOn with
    | _ f => induction b using Germ.inductionOn with
      | _ g => simp only [← Germ.coe_mul, Germ.coe_compTendsto]; rfl
  map_add' a b := by
    induction a using Germ.inductionOn with
    | _ f => induction b using Germ.inductionOn with
      | _ g => simp only [← Germ.coe_add, Germ.coe_compTendsto]; rfl

/-- The ring endomorphism `f ↦ f(c - ·)` of the meromorphic field of a domain symmetric under
`z ↦ c - z`. -/
def reflectHom : D.Field →+* D.Field where
  toFun a := ⟨D.reflectGerm c hc (D.germ a), by
    obtain ⟨f, hf, rfl⟩ := D.exists_rep a
    exact ⟨fun z => f (c - z), fun z hz =>
      (hf (c - z) (hc z hz)).comp_analyticAt (by fun_prop), rfl⟩⟩
  map_one' := Subtype.ext (D.reflectGerm c hc).map_one
  map_zero' := Subtype.ext (D.reflectGerm c hc).map_zero
  map_add' a b := Subtype.ext ((D.reflectGerm c hc).map_add (D.germ a) (D.germ b))
  map_mul' a b := Subtype.ext ((D.reflectGerm c hc).map_mul (D.germ a) (D.germ b))

/-- On the class of a meromorphic representative `f`, reflection is the class of `z ↦ f(c - z)`. -/
theorem reflectHom_ofMeromorphic (f : ℂ → ℂ) (hf : MeromorphicOn f D.carrier) :
    D.reflectHom c hc (D.ofMeromorphic f hf) =
      D.ofMeromorphic (fun z => f (c - z))
        (fun z hz => (hf (c - z) (hc z hz)).comp_analyticAt (by fun_prop)) := rfl

/-- Reflection `f ↦ f(c - ·)` is an involution of the meromorphic field. -/
theorem reflectHom_involutive : Function.Involutive (D.reflectHom c hc) := by
  intro a
  obtain ⟨f, hf, rfl⟩ := D.exists_rep a
  rw [D.reflectHom_ofMeromorphic, D.reflectHom_ofMeromorphic]
  apply (D.ofMeromorphic_eq_iff _ _).mpr
  intro z _
  exact Filter.Eventually.of_forall fun w => by simp only [sub_sub_cancel]

/-- Reflection as a ring automorphism of the meromorphic field, its own inverse. -/
def reflectEquiv : D.Field ≃+* D.Field where
  __ := D.reflectHom c hc
  invFun := D.reflectHom c hc
  left_inv := D.reflectHom_involutive c hc
  right_inv := D.reflectHom_involutive c hc

theorem reflectEquiv_involutive : Function.Involutive (D.reflectEquiv c hc) :=
  D.reflectHom_involutive c hc

/-- Reflection commutes with restriction from the plane: reflecting the restriction of a plane
meromorphic function equals restricting its plane reflection about `c`. -/
theorem reflectEquiv_restrictPlane (a : MeromorphicPlane) :
    D.reflectEquiv c hc (D.restrictPlane a) = D.restrictPlane (planeReflectEquiv c a) := by
  obtain ⟨f, hf, rfl⟩ := a.exists_rep
  rfl

end
end GaloisForLFunctions.HTGeometry.MeromorphicDomainData
