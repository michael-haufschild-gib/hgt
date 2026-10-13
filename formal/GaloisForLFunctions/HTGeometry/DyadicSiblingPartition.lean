import Mathlib.Data.Nat.Find
import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Logic.Equiv.Fin.Basic

/-! # The unique dyadic sibling rectangle of an ordered pair

Every pair `n < j` belongs to exactly one left/right sibling rectangle.
The level is the last binary scale at which their quotient labels differ.
-/

namespace GaloisForLFunctions.HTGeometry

def DyadicSibling (k n j : ℕ) : Prop :=
  n / 2 ^ k / 2 = j / 2 ^ k / 2 ∧ n / 2 ^ k % 2 = 0 ∧ j / 2 ^ k % 2 = 1

instance (k n j : ℕ) : Decidable (DyadicSibling k n j) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

theorem dyadic_quotient_eq_mono {n j k l : ℕ} (hkl : k ≤ l)
    (h : n / 2 ^ k = j / 2 ^ k) : n / 2 ^ l = j / 2 ^ l := by
  rw [show l = k + (l - k) by omega, pow_add, ← Nat.div_div_eq_div_mul,
    ← Nat.div_div_eq_div_mul, h]

theorem DyadicSibling.quotient_lt {k n j : ℕ} (h : DyadicSibling k n j) :
    n / 2 ^ k < j / 2 ^ k := by
  rcases h with ⟨he, hn, hj⟩
  omega

theorem DyadicSibling.lt {k n j : ℕ} (h : DyadicSibling k n j) : n < j := by
  by_contra hn
  exact (not_lt_of_ge (Nat.div_le_div_right (by omega : j ≤ n))) h.quotient_lt

theorem DyadicSibling.parent_eq {k n j : ℕ} (h : DyadicSibling k n j) :
    n / 2 ^ (k + 1) = j / 2 ^ (k + 1) := by
  simpa only [pow_succ, ← Nat.div_div_eq_div_mul] using h.1

theorem DyadicSibling.level_unique {k l n j : ℕ}
    (hk : DyadicSibling k n j) (hl : DyadicSibling l n j) : k = l := by
  have hnot (k l : ℕ) (hk : DyadicSibling k n j) (hl : DyadicSibling l n j) : ¬ k < l := by
    intro hkl
    have he := dyadic_quotient_eq_mono (Nat.succ_le_iff.mpr hkl) hk.parent_eq
    exact hl.quotient_lt.ne he
  have h₁ := hnot k l hk hl
  have h₂ := hnot l k hl hk
  omega

/-- An exact partition of the entire strict upper triangle, with no finite cutoff. -/
theorem existsUnique_dyadicSibling {n j : ℕ} (hnj : n < j) : ∃! k, DyadicSibling k n j := by
  have hex : ∃ l : ℕ, n / 2 ^ l = j / 2 ^ l :=
    ⟨j, by rw [Nat.div_eq_of_lt (hnj.trans j.lt_two_pow_self), Nat.div_eq_of_lt j.lt_two_pow_self]⟩
  let l := Nat.find hex
  have he : n / 2 ^ l = j / 2 ^ l := Nat.find_spec hex
  have hl : 0 < l := by
    by_contra h
    have hz : l = 0 := by omega
    simp only [hz, pow_zero, Nat.div_one] at he
    omega
  have hn : n / 2 ^ (l - 1) ≠ j / 2 ^ (l - 1) := Nat.find_min hex (by omega)
  have hp : n / 2 ^ (l - 1) / 2 = j / 2 ^ (l - 1) / 2 := by
    simpa only [Nat.div_div_eq_div_mul, ← pow_succ, Nat.sub_add_cancel hl] using he
  have hmono := Nat.div_le_div_right (c := 2 ^ (l - 1)) hnj.le
  have hs : DyadicSibling (l - 1) n j := by
    unfold DyadicSibling
    omega
  exact ⟨l - 1, hs, fun k hk => hk.level_unique hs⟩

noncomputable def dyadicSiblingLevel (n j : ℕ) : ℕ :=
  if h : n < j then (existsUnique_dyadicSibling h).exists.choose else 0

theorem dyadicSibling_level {n j : ℕ} (h : n < j) : DyadicSibling (dyadicSiblingLevel n j) n j := by
  rw [dyadicSiblingLevel, dif_pos h]
  exact (existsUnique_dyadicSibling h).exists.choose_spec

theorem dyadicSibling_iff_level {k n j : ℕ} (h : n < j) :
    DyadicSibling k n j ↔ k = dyadicSiblingLevel n j :=
  ⟨fun hk => hk.level_unique (dyadicSibling_level h), fun hk => hk ▸ dyadicSibling_level h⟩

/-- A coordinate in the left (`b = 0`) or right (`b = 1`) half of a dyadic block. -/
def dyadicChild (k : ℕ) (b : Fin 2) (p : ℕ × Fin (2 ^ k)) : ℕ :=
  (2 * p.1 + b) * 2 ^ k + p.2

@[simp] theorem dyadicChild_div (k : ℕ) (b : Fin 2) (p : ℕ × Fin (2 ^ k)) :
    dyadicChild k b p / 2 ^ k = 2 * p.1 + b := by
  rw [dyadicChild, Nat.add_comm,
    Nat.add_mul_div_right _ _ ((Nat.zero_le k).trans_lt k.lt_two_pow_self),
    Nat.div_eq_of_lt p.2.isLt, Nat.zero_add]

@[simp] theorem dyadicChild_mod (k : ℕ) (b : Fin 2) (p : ℕ × Fin (2 ^ k)) :
    dyadicChild k b p % 2 ^ k = p.2 := by
  simp [dyadicChild, Nat.add_mod, Nat.mod_eq_of_lt p.2.isLt]

theorem dyadicChild_injective (k : ℕ) (b : Fin 2) : Function.Injective (dyadicChild k b) := by
  intro p q h
  have hd := congrArg (fun n => n / 2 ^ k) h
  have hm := congrArg (fun n => n % 2 ^ k) h
  simp only [dyadicChild_div] at hd
  simp only [dyadicChild_mod] at hm
  apply Prod.ext
  · omega
  · exact Fin.ext hm

theorem dyadicChild_sibling (k m : ℕ) (r s : Fin (2 ^ k)) :
    DyadicSibling k (dyadicChild k 0 (m, r)) (dyadicChild k 1 (m, s)) := by
  unfold DyadicSibling
  simp only [dyadicChild_div, Fin.val_zero, Fin.val_one]
  omega

theorem dyadicChild_right_lower (k : ℕ) (p : ℕ × Fin (2 ^ k)) :
    2 ^ k ≤ dyadicChild k 1 p := by
  unfold dyadicChild
  simp only [Fin.val_one]
  have := Nat.mul_le_mul_right (2 ^ k) (show 1 ≤ 2 * p.1 + 1 by omega)
  omega

theorem dyadicChild_eq_of_div {k n : ℕ} {b : Fin 2} (h : n / 2 ^ k % 2 = b) :
    dyadicChild k b (n / 2 ^ k / 2,
      ⟨n % 2 ^ k, Nat.mod_lt _ ((Nat.zero_le k).trans_lt k.lt_two_pow_self)⟩) = n := by
  unfold dyadicChild
  have he := Nat.mod_add_div (n / 2 ^ k) 2
  have hn := Nat.div_add_mod' n (2 ^ k)
  rw [h] at he
  have hq : 2 * (n / 2 ^ k / 2) + b = n / 2 ^ k := by omega
  simpa only [hq] using hn

theorem DyadicSibling.coordinates {k n j : ℕ} (h : DyadicSibling k n j) :
    ∃ (m : ℕ) (r s : Fin (2 ^ k)), n = dyadicChild k 0 (m, r) ∧ j = dyadicChild k 1 (m, s) := by
  refine ⟨n / 2 ^ k / 2,
    ⟨n % 2 ^ k, Nat.mod_lt _ ((Nat.zero_le k).trans_lt k.lt_two_pow_self)⟩,
    ⟨j % 2 ^ k, Nat.mod_lt _ ((Nat.zero_le k).trans_lt k.lt_two_pow_self)⟩, ?_, ?_⟩
  · exact (dyadicChild_eq_of_div h.2.1).symm
  · rw [h.1]
    exact (dyadicChild_eq_of_div h.2.2).symm

end GaloisForLFunctions.HTGeometry
