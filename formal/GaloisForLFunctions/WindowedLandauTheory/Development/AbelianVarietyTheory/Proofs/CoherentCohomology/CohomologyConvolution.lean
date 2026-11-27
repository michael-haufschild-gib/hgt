import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! The nonnegative convolution identities used in the cohomology of
translation differences and principal polarizations. -/

open Finset.HasAntidiagonal

namespace GlobalTheory.PrincipalSections

/-- If the self-convolution of a cohomology dimension sequence equals its
convolution with a sequence positive in degree zero, its first nonzero entry
must already occur in degree zero. -/
theorem eq_zero_of_selfConvolution (a b : ℕ → ℕ) (ha : a 0 = 0) (hb : 0 < b 0)
    (h : ∀ n, (∑ x ∈ antidiagonal n, a x.1 * a x.2) =
      ∑ x ∈ antidiagonal n, a x.1 * b x.2) (n : ℕ) : a n = 0 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have hzero : (∑ x ∈ antidiagonal n, a x.1 * a x.2) = 0 := by
      refine Finset.sum_eq_zero fun x hx => ?_
      have e : x.1 + x.2 = n := by simpa using hx
      rcases Nat.eq_zero_or_pos x.2 with h₂ | h₂
      · rw [h₂, ha, Nat.mul_zero]
      · rw [ih x.1 (by omega), Nat.zero_mul]
    have hle : a n * b 0 ≤ ∑ x ∈ antidiagonal n, a x.1 * b x.2 :=
      Finset.single_le_sum (f := fun x : ℕ × ℕ => a x.1 * b x.2)
        (fun _ _ => Nat.zero_le _) (show (n, 0) ∈ antidiagonal n by simp)
    rw [← h n, hzero] at hle
    exact (Nat.mul_eq_zero.mp (Nat.eq_zero_of_le_zero hle)).resolve_right hb.ne'

/-- A convolution supported with value one in a single degree bounds the
degree-zero dimension of the first factor by one. -/
theorem le_one_of_convolution (a b : ℕ → ℕ) (g : ℕ)
    (h : ∀ n, ∑ x ∈ antidiagonal n, a x.1 * b x.2 = if n = g then 1 else 0) :
    a 0 ≤ 1 := by
  have hg := h g
  rw [if_pos rfl] at hg
  obtain ⟨x, -, hx⟩ := Finset.exists_ne_zero_of_sum_ne_zero (hg.trans_ne one_ne_zero)
  have hb : 0 < b x.2 := Nat.pos_of_ne_zero fun e => hx (by rw [e, Nat.mul_zero])
  have hle : a 0 * b x.2 ≤ ∑ y ∈ antidiagonal x.2, a y.1 * b y.2 :=
    Finset.single_le_sum (f := fun y : ℕ × ℕ => a y.1 * b y.2)
      (fun _ _ => Nat.zero_le _) (show (0, x.2) ∈ antidiagonal x.2 by simp)
  have h₁ : (if x.2 = g then 1 else 0) ≤ 1 := by split_ifs <;> omega
  exact (Nat.le_mul_of_pos_right _ hb).trans (hle.trans ((h x.2).le.trans h₁))

end GlobalTheory.PrincipalSections
