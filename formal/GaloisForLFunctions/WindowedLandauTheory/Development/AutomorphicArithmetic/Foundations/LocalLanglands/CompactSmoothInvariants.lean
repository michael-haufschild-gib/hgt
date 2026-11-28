import Mathlib.Analysis.Complex.Basic
import Mathlib.GroupTheory.IndexNormal
import Mathlib.RepresentationTheory.Coinvariants
import Mathlib.RepresentationTheory.Invariants
import Mathlib.Topology.Algebra.OpenSubgroup

/-! For a smooth complex representation of a compact group, fixed
vectors split off from the relations defining coinvariants. Each
finite set of vectors is fixed by an open subgroup of finite index. -/

noncomputable section

namespace Representation

variable {G V : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
  (hρ : ∀ v : V, IsOpen {g : G | ρ g v = v})

include hρ in
private theorem exists_finiteIndex_fix (v : V) :
    ∃ U : Subgroup G, U.FiniteIndex ∧ ∀ u ∈ U, ρ u v = v := by
  let U : Subgroup G :=
    { carrier := {g | ρ g v = v}
      one_mem' := by simp
      mul_mem' := fun {x y} hx hy => by
        change ρ (x * y) v = v
        rw [map_mul, Module.End.mul_apply, show ρ y v = v from hy]
        exact hx
      inv_mem' := fun {x} hx => by
        change ρ x⁻¹ v = v
        nth_rw 1 [← show ρ x v = v from hx]
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
          Module.End.one_apply] }
  haveI : Finite (G ⧸ U) := U.quotient_finite_of_isOpen (hρ v)
  exact ⟨U, U.finiteIndex_of_finite_quotient, fun _ hu => hu⟩

private def cosetSum (U : Subgroup G) [Fintype (G ⧸ U)] : V →ₗ[ℂ] V :=
  ∑ q : G ⧸ U, ρ q.out

private theorem apply_out_of_fixed {U : Subgroup G} {v : V}
    (hv : ∀ u ∈ U, ρ u v = v) (g : G) : ρ ((g : G ⧸ U).out) v = ρ g v := by
  obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul U g
  rw [hu, map_mul, Module.End.mul_apply, hv u u.2]

include hρ in
private theorem exists_cosetSum_zero_of_mem_coinvariantKer {v : V} (hv : v ∈ Coinvariants.ker ρ) :
    ∃ U₀ : Subgroup G, U₀.FiniteIndex ∧
      ∀ (U : Subgroup G) [U.Normal] [Fintype (G ⧸ U)], U ≤ U₀ → cosetSum ρ U v = 0 := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨g, u⟩, rfl⟩ := hx
    obtain ⟨U₀, hfin, hfix⟩ := exists_finiteIndex_fix ρ hρ u
    refine ⟨U₀, hfin, fun U _ _ hU => ?_⟩
    simp only [map_sub, sub_eq_zero, cosetSum, LinearMap.sum_apply]
    refine Fintype.sum_equiv (Equiv.mulRight (g : G ⧸ U)) _ _ fun q => ?_
    have he : Equiv.mulRight (g : G ⧸ U) q = ((q.out * g : G) : G ⧸ U) := by
      rw [QuotientGroup.mk_mul, QuotientGroup.out_eq']
      rfl
    rw [he, apply_out_of_fixed ρ (fun x hx => hfix x (hU hx)), map_mul, Module.End.mul_apply]
  | zero => exact ⟨⊤, inferInstance, fun U _ _ _ => map_zero _⟩
  | add x y _ _ hx hy =>
    obtain ⟨A, _, hA⟩ := hx
    obtain ⟨B, _, hB⟩ := hy
    refine ⟨A ⊓ B, inferInstance, fun U _ _ hU => ?_⟩
    rw [map_add, hA U (hU.trans inf_le_left), hB U (hU.trans inf_le_right), add_zero]
  | smul c x _ hx =>
    obtain ⟨A, hA, he⟩ := hx
    exact ⟨A, hA, fun U _ _ hU => by rw [map_smul, he U hU, smul_zero]⟩

include hρ in
theorem invariants_isCompl_coinvariantKer_of_compact :
    IsCompl ρ.invariants (Coinvariants.ker ρ) := by
  constructor
  · refine Submodule.disjoint_def.mpr fun v hv hv' => ?_
    obtain ⟨U, _, hU⟩ := exists_cosetSum_zero_of_mem_coinvariantKer ρ hρ hv'
    letI := Fintype.ofFinite (G ⧸ U.normalCore)
    have he := hU U.normalCore U.normalCore_le
    rw [cosetSum, LinearMap.sum_apply, Finset.sum_congr rfl fun q _ => hv q.out,
      Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ] at he
    exact (smul_eq_zero.mp he).resolve_left (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  · refine codisjoint_iff.mpr (eq_top_iff.mpr fun v _ => ?_)
    obtain ⟨U, _, hU⟩ := exists_finiteIndex_fix ρ hρ v
    letI := Fintype.ofFinite (G ⧸ U)
    let c : ℂ := Fintype.card (G ⧸ U)
    have hc : c ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    have hfixed : cosetSum ρ U v ∈ ρ.invariants := by
      intro g
      simp only [cosetSum, LinearMap.sum_apply, map_sum]
      refine Fintype.sum_equiv (MulAction.toPerm g) _ _ fun q => ?_
      conv_rhs => rw [MulAction.toPerm_apply, ← q.out_eq, MulAction.Quotient.smul_mk]
      rw [apply_out_of_fixed ρ hU, smul_eq_mul, map_mul, Module.End.mul_apply]
    have hrel : cosetSum ρ U v - c • v ∈ Coinvariants.ker ρ := by
      rw [cosetSum, LinearMap.sum_apply, show c = (Fintype.card (G ⧸ U) : ℂ) from rfl,
        Nat.cast_smul_eq_nsmul, ← Finset.card_univ, ← Finset.sum_const, ← Finset.sum_sub_distrib]
      exact Submodule.sum_mem _ fun q _ => Coinvariants.sub_mem_ker q.out v
    have hsum := Submodule.smul_mem _ c⁻¹
      (sub_mem (Submodule.mem_sup_left hfixed) (Submodule.mem_sup_right hrel))
    simpa only [sub_sub_cancel, smul_smul, inv_mul_cancel₀ hc, one_smul] using hsum

end Representation

#print axioms Representation.invariants_isCompl_coinvariantKer_of_compact
