import GaloisForLFunctions.HTGeometry.DyadicSiblingPartition
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # The common positive scale of a dyadic sibling block -/

namespace GaloisForLFunctions.HTGeometry

def dyadicParentBase (k n : ℕ) : ℕ := (n / 2 ^ k / 2 + 1) * 2 ^ k

theorem dyadicParentBase_lower (k n : ℕ) : 2 ^ k ≤ dyadicParentBase k n := by
  simpa only [dyadicParentBase, Nat.succ_eq_add_one, Nat.zero_add, one_mul] using Nat.mul_le_mul_right (2 ^ k)
    (Nat.succ_le_succ (Nat.zero_le (n / 2 ^ k / 2)))

theorem dyadicParentBase_pos (k n : ℕ) : 0 < dyadicParentBase k n :=
  ((Nat.zero_le k).trans_lt k.lt_two_pow_self).trans_le (dyadicParentBase_lower k n)

theorem succ_le_twice_dyadicParentBase (k n : ℕ) : n + 1 ≤ 2 * dyadicParentBase k n := by
  have h : n / 2 ^ k < 2 * (n / 2 ^ k / 2 + 1) := by omega
  have he := (Nat.div_lt_iff_lt_mul ((Nat.zero_le k).trans_lt k.lt_two_pow_self)).mp h
  simpa only [dyadicParentBase, Nat.mul_assoc] using Nat.succ_le_of_lt he

theorem dyadicParentBase_le_of_right {k n : ℕ} (h : n / 2 ^ k % 2 = 1) :
    dyadicParentBase k n ≤ n := by
  have hzero := Nat.zero_le (n / 2 ^ k / 2)
  have he := Nat.mod_add_div (n / 2 ^ k) 2
  have hq : n / 2 ^ k / 2 + 1 ≤ n / 2 ^ k := by omega
  exact (Nat.mul_le_mul_right (2 ^ k) hq).trans (Nat.div_mul_le_self n (2 ^ k))

@[simp] theorem dyadicParentBase_child (k : ℕ) (b : Fin 2) (p : ℕ × Fin (2 ^ k)) :
    dyadicParentBase k (dyadicChild k b p) = (p.1 + 1) * 2 ^ k := by
  unfold dyadicParentBase
  rw [dyadicChild_div]
  have hb := b.isLt
  have he : (2 * p.1 + b.val) / 2 = p.1 := by omega
  rw [he]

theorem DyadicSibling.parentBase_eq {k n j : ℕ} (h : DyadicSibling k n j) :
    dyadicParentBase k n = dyadicParentBase k j := by
  simp only [dyadicParentBase, h.1]

theorem dyadicParentBase_real_lower (k n : ℕ) :
    ((n : ℝ) + 1) / 2 ≤ (dyadicParentBase k n : ℝ) := by
  have h : (n : ℝ) + 1 ≤ 2 * (dyadicParentBase k n : ℝ) := by
    exact_mod_cast succ_le_twice_dyadicParentBase k n
  linarith

end GaloisForLFunctions.HTGeometry
