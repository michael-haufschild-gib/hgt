import GaloisForLFunctions.HTGeometry.MeromorphicDomainField
import GaloisForLFunctions.HTGeometry.MeromorphicPlaneReflection

open Filter Topology
namespace GaloisForLFunctions.HTGeometry.MeromorphicDomainData
noncomputable section
variable (D : MeromorphicDomainData) (c : ℂ)
variable (hc : ∀ z ∈ D.carrier, c - z ∈ D.carrier)

include hc in
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

def reflectHom : D.Field →+* D.Field where
  toFun a := ⟨D.reflectGerm c hc (D.germ a), by
    obtain ⟨f, hf, rfl⟩ := D.exists_rep a
    exact ⟨fun z => f (c - z), fun z hz =>
      (hf (c - z) (hc z hz)).comp_analyticAt (by fun_prop), rfl⟩⟩
  map_one' := Subtype.ext (D.reflectGerm c hc).map_one
  map_zero' := Subtype.ext (D.reflectGerm c hc).map_zero
  map_add' a b := Subtype.ext ((D.reflectGerm c hc).map_add (D.germ a) (D.germ b))
  map_mul' a b := Subtype.ext ((D.reflectGerm c hc).map_mul (D.germ a) (D.germ b))

theorem reflectHom_ofMeromorphic (f : ℂ → ℂ) (hf : MeromorphicOn f D.carrier) :
    D.reflectHom c hc (D.ofMeromorphic f hf) =
      D.ofMeromorphic (fun z => f (c - z))
        (fun z hz => (hf (c - z) (hc z hz)).comp_analyticAt (by fun_prop)) := rfl

theorem reflectHom_involutive : Function.Involutive (D.reflectHom c hc) := by
  intro a
  obtain ⟨f, hf, rfl⟩ := D.exists_rep a
  rw [D.reflectHom_ofMeromorphic, D.reflectHom_ofMeromorphic]
  apply (D.ofMeromorphic_eq_iff _ _).mpr
  intro z _
  exact Filter.Eventually.of_forall fun w => by simp only [sub_sub_cancel]

def reflectEquiv : D.Field ≃+* D.Field where
  __ := D.reflectHom c hc
  invFun := D.reflectHom c hc
  left_inv := D.reflectHom_involutive c hc
  right_inv := D.reflectHom_involutive c hc

theorem reflectEquiv_involutive : Function.Involutive (D.reflectEquiv c hc) :=
  D.reflectHom_involutive c hc

theorem reflectEquiv_restrictPlane (a : MeromorphicPlane) :
    D.reflectEquiv c hc (D.restrictPlane a) = D.restrictPlane (planeReflectEquiv c a) := by
  obtain ⟨f, hf, rfl⟩ := a.exists_rep
  rfl

end
end GaloisForLFunctions.HTGeometry.MeromorphicDomainData
