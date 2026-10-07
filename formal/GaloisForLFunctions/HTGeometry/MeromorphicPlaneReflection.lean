import GaloisForLFunctions.HTGeometry.MeromorphicPlaneAlgebra

/-!
# Affine reflection on the actual meromorphic plane field

Pullback by `z ↦ c-z` preserves codiscrete equality and meromorphicity. It gives
an involutive automorphism of the all-meromorphic carrier and fixes constants.
This is the actual global base used by the marked Xi towers.
-/

open Filter Topology
namespace GaloisForLFunctions.HTGeometry
noncomputable section

theorem tendsto_const_sub_planeCodiscrete (c : ℂ) :
    Tendsto (fun z : ℂ => c - z) planeCodiscrete planeCodiscrete := by
  refine Filter.tendsto_def.mpr fun S hS => ?_
  refine mem_planeCodiscrete.mpr fun x => ?_
  have ht : Tendsto (fun w : ℂ => c - w) (𝓝[≠] x) (𝓝[≠] (c - x)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · exact ((by fun_prop : Continuous fun w : ℂ => c - w).tendsto x).mono_left
        nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with w hw
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro he
      exact hw (sub_right_injective he)
  exact ht ((mem_planeCodiscrete.mp hS) (c - x))

private def planeGermReflect (c : ℂ) : Germ planeCodiscrete ℂ →+* Germ planeCodiscrete ℂ where
  toFun a := a.compTendsto (fun z => c - z) (tendsto_const_sub_planeCodiscrete c)
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

/-- Pullback by an affine reflection on the actual all-meromorphic carrier. -/
def planeReflectHom (c : ℂ) : MeromorphicPlane →+* MeromorphicPlane where
  toFun a := ⟨planeGermReflect c a.germ, by
    obtain ⟨f, hf, rfl⟩ := a.exists_rep
    exact ⟨fun z => f (c - z), fun z =>
      (hf (c - z)).comp_analyticAt (by fun_prop), rfl⟩⟩
  map_one' := Subtype.ext (planeGermReflect c).map_one
  map_zero' := Subtype.ext (planeGermReflect c).map_zero
  map_add' a b := Subtype.ext ((planeGermReflect c).map_add a.germ b.germ)
  map_mul' a b := Subtype.ext ((planeGermReflect c).map_mul a.germ b.germ)

theorem planeReflectHom_ofMeromorphic (c : ℂ) (f : ℂ → ℂ)
    (hf : ∀ z, MeromorphicAt f z) :
    planeReflectHom c (ofMeromorphic f hf) =
      ofMeromorphic (fun z => f (c - z))
        (fun z => (hf (c - z)).comp_analyticAt (by fun_prop)) := rfl

theorem planeReflectHom_involutive (c : ℂ) : Function.Involutive (planeReflectHom c) := by
  intro a
  obtain ⟨f, hf, rfl⟩ := a.exists_rep
  rw [planeReflectHom_ofMeromorphic, planeReflectHom_ofMeromorphic]
  apply MeromorphicPlane.germ_injective
  rw [germ_ofMeromorphic, germ_ofMeromorphic]
  apply Germ.coe_eq.mpr
  exact Filter.Eventually.of_forall fun z => by
    simp only [sub_sub_cancel]

/-- Reflection is an involutive automorphism of the actual global field. -/
def planeReflectEquiv (c : ℂ) : MeromorphicPlane ≃+* MeromorphicPlane where
  __ := planeReflectHom c
  invFun := planeReflectHom c
  left_inv := planeReflectHom_involutive c
  right_inv := planeReflectHom_involutive c

theorem planeReflectEquiv_ofMeromorphic (c : ℂ) (f : ℂ → ℂ)
    (hf : ∀ z, MeromorphicAt f z) :
    planeReflectEquiv c (ofMeromorphic f hf) =
      ofMeromorphic (fun z => f (c - z))
        (fun z => (hf (c - z)).comp_analyticAt (by fun_prop)) := rfl

theorem planeReflectEquiv_const (c a : ℂ) : planeReflectEquiv c (constPlane a) = constPlane a := rfl

theorem planeReflectEquiv_involutive (c : ℂ) : Function.Involutive (planeReflectEquiv c) :=
  planeReflectHom_involutive c

end
end GaloisForLFunctions.HTGeometry
