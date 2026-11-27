import Mathlib.GroupTheory.Index

/-! The index of a homomorphism's image from its effect on a
finite-index subgroup disjoint from its kernel. -/

namespace GlobalTheory.Reciprocity

variable {G H : Type*} [CommGroup G] [Group H]

theorem index_range_of_index_map (f : G →* H) (U : Subgroup G)
    (hU : 0 < U.index) (hker : Disjoint U f.ker) (m : ℕ)
    (hindex : (U.map f).index = U.index * m) :
    f.range.index = Nat.card f.ker * m := by
  have hrel : U.relIndex f.ker = Nat.card f.ker := by
    rw [Subgroup.relIndex, Subgroup.subgroupOf_eq_bot.2 hker, Subgroup.index_bot]
  have hmul : Nat.card f.ker * (U ⊔ f.ker).index = U.index := by
    rw [← hrel, ← Subgroup.relIndex_sup_left f.ker U]
    exact Subgroup.relIndex_mul_index le_sup_left
  apply Nat.eq_of_mul_eq_mul_left hU
  calc U.index * f.range.index = Nat.card f.ker * ((U ⊔ f.ker).index * f.range.index) := by
        rw [← hmul, mul_assoc]
    _ = U.index * (Nat.card f.ker * m) := by
        rw [← U.index_map f, hindex, mul_left_comm]

end GlobalTheory.Reciprocity
