import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.IdeleGroups.CompactIdelicClassQuotient

/-! Finitely many finite places suffice to represent the ordinary ideal
classes. Every idelic class has a representative integral outside them. -/

noncomputable section

open NumberField IsDedekindDomain FractionalIdeal
open scoped nonZeroDivisors

namespace GlobalTheory.Reciprocity.IdeleGroup

variable {K : Type*} [Field K] [NumberField K]

/-- Ideles with integral finite components outside the prescribed set. -/
def supportedIdeles (S : Set (HeightOneSpectrum (𝓞 K))) : Subgroup (IdeleGroup K) where
  carrier := {x | ∀ v ∉ S, ord v x = 0}
  one_mem' v _ := ord_one v
  mul_mem' {x y} hx hy v hv := by rw [ord_mul, hx v hv, hy v hv, add_zero]
  inv_mem' {x} hx v hv := by rw [ord_inv, hx v hv, neg_zero]

theorem supportedIdeles_mono : Monotone (supportedIdeles (K := K)) :=
  fun _ _ h _ hx v hv => hx v (fun hm => hv (h hm))

theorem exists_sup_supportedIdeles_eq_top :
    ∃ S : Finset (HeightOneSpectrum (𝓞 K)),
      (diagonal K).range ⊔ supportedIdeles (S : Set _) = ⊤ := by
  classical
  let r := Function.surjInv (toOrdinaryClassGroup_surjective K)
  have hr (c : ClassGroup (𝓞 K)) : toOrdinaryClassGroup K (r c) = c :=
    Function.rightInverse_surjInv (toOrdinaryClassGroup_surjective K) c
  have hfin (c : ClassGroup (𝓞 K)) : {v | ord v (r c) ≠ 0}.Finite :=
    Filter.eventually_cofinite.mp (eventually_ord_eq_zero (r c))
  let S : Finset (HeightOneSpectrum (𝓞 K)) := Finset.univ.biUnion fun c => (hfin c).toFinset
  have hS (c : ClassGroup (𝓞 K)) : r c ∈ supportedIdeles (S : Set _) := by
    intro v hv
    by_contra h
    exact hv (Finset.mem_biUnion.mpr ⟨c, Finset.mem_univ _, (hfin c).mem_toFinset.mpr h⟩)
  refine ⟨S, eq_top_iff.mpr fun x _ => ?_⟩
  let c := toOrdinaryClassGroup K x
  have hx : toOrdinaryClassGroup K (x * (r c)⁻¹) = 1 := by
    rw [map_mul, map_inv, hr, mul_inv_cancel]
  obtain ⟨a, ha⟩ := (toOrdinaryClassGroup_eq_one_iff K).mp hx
  set u := (diagonal K a)⁻¹ * (x * (r c)⁻¹) with hudef
  have hu : toFractionalIdeal u = 1 := by
    rw [hudef, map_mul, map_inv, toFractionalIdeal_diagonal, ha, inv_mul_cancel]
  have huS : u ∈ supportedIdeles (S : Set _) := fun v _ => by
    simpa only [Units.val_one, count_one] using (toFractionalIdeal_eq_iff.mp hu v)
  refine Subgroup.mem_sup.mpr ⟨diagonal K a, ⟨a, rfl⟩, u * r c, mul_mem huS (hS c), ?_⟩
  rw [hudef, mul_assoc ((diagonal K a)⁻¹), inv_mul_cancel_right, mul_inv_cancel_left]

end GlobalTheory.Reciprocity.IdeleGroup
