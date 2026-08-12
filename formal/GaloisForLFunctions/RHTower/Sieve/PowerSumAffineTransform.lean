import GaloisForLFunctions.RHTower.Sieve.FiniteFiberInjectiveTransform
import Mathlib.Algebra.Field.ZMod

namespace RHTower.Sieve

open scoped BigOperators

noncomputable section

def powerSumAffineLinearTransform (q k : ℕ) [NeZero q]
    (p r : ZMod q) : (Fin k → ZMod q) →+ (Fin k → ZMod q) where
  toFun s j := ∑ m : Fin (j.val + 1),
    p ^ (m.val + 1) * r ^ (j.val - m.val) *
      (j.val + 1).choose (m.val + 1) *
        s (Fin.castLE (Nat.succ_le_of_lt j.isLt) m)
  map_zero' := by
    funext j
    simp
  map_add' x y := by
    funext j
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem powerSumAffineLinearTransform_apply
    (q k : ℕ) [NeZero q] (p r : ZMod q) (s : Fin k → ZMod q) (j : Fin k) :
    powerSumAffineLinearTransform q k p r s j =
      ∑ m : Fin (j.val + 1),
        p ^ (m.val + 1) * r ^ (j.val - m.val) *
          (j.val + 1).choose (m.val + 1) *
            s (Fin.castLE (Nat.succ_le_of_lt j.isLt) m) := rfl

theorem powerSumAffineLinearTransform_injective
    {q k : ℕ} [NeZero q] {p : ZMod q} (hp : IsUnit p) (r : ZMod q) :
    Function.Injective (powerSumAffineLinearTransform q k p r) := by
  intro x y hxy
  funext j
  have hcoord : ∀ n : ℕ, (hn : n < k) → x ⟨n, hn⟩ = y ⟨n, hn⟩ := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro hn
        let jn : Fin k := ⟨n, hn⟩
        have h := congrFun hxy jn
        rw [powerSumAffineLinearTransform_apply,
          powerSumAffineLinearTransform_apply] at h
        rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc] at h
        dsimp [jn] at h
        simp only [Nat.sub_self, pow_zero, Nat.choose_self, mul_one,
          Nat.cast_one] at h
        have hlower :
            (∑ m : Fin n,
                p ^ (m.val + 1) * r ^ (n - m.val) *
                  (n + 1).choose (m.val + 1) *
                  x (Fin.castLE (Nat.le_of_lt hn) m)) =
              ∑ m : Fin n,
                p ^ (m.val + 1) * r ^ (n - m.val) *
                  (n + 1).choose (m.val + 1) *
                    y (Fin.castLE (Nat.le_of_lt hn) m) := by
          apply Finset.sum_congr rfl
          intro m _
          have hindex : Fin.castLE (Nat.le_of_lt hn) m =
              ⟨m.val, m.isLt.trans hn⟩ := Fin.ext rfl
          rw [hindex, ih m.val m.isLt (m.isLt.trans hn)]
        rw [hlower] at h
        have hlast : Fin.castLE (Nat.succ_le_of_lt hn) (Fin.last n) =
            ⟨n, hn⟩ := Fin.ext rfl
        rw [hlast] at h
        have htop : p ^ (n + 1) * x ⟨n, hn⟩ =
            p ^ (n + 1) * y ⟨n, hn⟩ := by
          have := add_left_cancel h
          simpa using this
        exact (hp.pow (n + 1)).mul_left_cancel htop
  exact hcoord j.val j.isLt

def powerSumAffineConstant (q k b : ℕ) [NeZero q]
    (r : ZMod q) : Fin k → ZMod q :=
  fun j => b * r ^ (j.val + 1)

theorem powerSumAffine_signature
    {q k b : ℕ} [NeZero q] (p r : ZMod q)
    (u : Fin b → ZMod q) :
    (fun j : Fin k => ∑ i : Fin b, (p * u i + r) ^ (j.val + 1)) =
      powerSumAffineConstant q k b r +
        powerSumAffineLinearTransform q k p r
          (fun j : Fin k => ∑ i : Fin b, u i ^ (j.val + 1)) := by
  funext j
  change (∑ i : Fin b, (p * u i + r) ^ (j.val + 1)) =
    powerSumAffineConstant q k b r j +
      powerSumAffineLinearTransform q k p r
        (fun j : Fin k => ∑ i : Fin b, u i ^ (j.val + 1)) j
  rw [powerSumAffineLinearTransform_apply]
  simp_rw [add_pow]
  conv_lhs => rw [Finset.sum_comm]
  rw [show j.val + 2 = (j.val + 1) + 1 by omega,
    ← Fin.sum_univ_eq_sum_range]
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, Nat.sub_zero, Nat.choose_zero_right,
    powerSumAffineConstant]
  congr 1
  · simp
  · apply Finset.sum_congr rfl
    intro m hm
    simp only [Fin.val_succ, Fin.val_castLE]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    push_cast
    rw [mul_pow]
    ring

end

end RHTower.Sieve

