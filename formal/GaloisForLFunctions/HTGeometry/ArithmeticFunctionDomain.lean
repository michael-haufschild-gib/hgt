import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.Data.Complex.Basic

/-!
# The Dirichlet-convolution domain of complex arithmetic functions

Mathlib equips `ArithmeticFunction ℂ` with Dirichlet convolution but does not currently provide its
domain structure.  The least nonzero coefficient proves the missing fact: if `m` and `n` are the
least nonzero indices of `f` and `g`, then the coefficient of `f * g` at `m*n` is exactly
`f m * g n`.  Every other factorization has a first index below `m` or a second index below `n`.
-/

namespace GaloisForLFunctions.HTGeometry

open ArithmeticFunction

noncomputable section

/-- Complex arithmetic functions are nontrivial: zero and the Dirichlet-convolution unit differ at
coefficient one. -/
instance arithmeticFunctionComplex_nontrivial : Nontrivial (ArithmeticFunction ℂ) := by
  refine ⟨⟨0, 1, ?_⟩⟩
  intro h
  have h1 := congrArg (fun f : ArithmeticFunction ℂ => f 1) h
  simp at h1

/-- The coefficient at the product of two first nonzero indices has only the distinguished
factorization as a nonzero summand. -/
theorem arithmeticFunction_mul_apply_of_first_nonzero
    (f g : ArithmeticFunction ℂ) (m n : ℕ)
    (hmpos : 0 < m) (hnpos : 0 < n)
    (hfbelow : ∀ k, k < m → f k = 0)
    (hgbelow : ∀ k, k < n → g k = 0) :
    (f * g) (m * n) = f m * g n := by
  rw [ArithmeticFunction.mul_apply]
  apply Finset.sum_eq_single (m, n)
  · intro x hx hxne
    rw [Nat.mem_divisorsAntidiagonal] at hx
    by_cases hxm : x.1 < m
    · rw [hfbelow x.1 hxm, zero_mul]
    by_cases hmx : m < x.1
    · have hxnpos : 0 < x.2 := by
        exact Nat.pos_of_ne_zero (fun hx0 => hx.2 (by rw [← hx.1, hx0, mul_zero]))
      have hx2lt : x.2 < n := by
        by_contra hnot
        have hnle : n ≤ x.2 := Nat.le_of_not_gt hnot
        have hstrict : m * n < x.1 * x.2 :=
          (Nat.mul_lt_mul_of_pos_right hmx hnpos).trans_le
            (Nat.mul_le_mul_left x.1 hnle)
        rw [hx.1] at hstrict
        exact (Nat.lt_irrefl (m * n)) hstrict
      rw [hgbelow x.2 hx2lt, mul_zero]
    · have hxeq : x.1 = m := Nat.le_antisymm (Nat.le_of_not_gt hmx) (Nat.le_of_not_gt hxm)
      have hx2eq : x.2 = n := by
        rw [hxeq] at hx
        exact Nat.eq_of_mul_eq_mul_left hmpos hx.1
      exact (hxne (Prod.ext hxeq hx2eq)).elim
  · intro hnot
    exfalso
    apply hnot
    rw [Nat.mem_divisorsAntidiagonal]
    exact ⟨rfl, Nat.mul_ne_zero hmpos.ne' hnpos.ne'⟩

/-- Dirichlet convolution of two nonzero complex arithmetic functions is nonzero. -/
theorem arithmeticFunction_mul_ne_zero
    {f g : ArithmeticFunction ℂ} (hf : f ≠ 0) (hg : g ≠ 0) :
    f * g ≠ 0 := by
  classical
  let hfex : ∃ k, f k ≠ 0 := by
    by_contra h
    apply hf
    ext k
    by_contra hk
    exact h ⟨k, hk⟩
  let hgex : ∃ k, g k ≠ 0 := by
    by_contra h
    apply hg
    ext k
    by_contra hk
    exact h ⟨k, hk⟩
  let m := Nat.find hfex
  let n := Nat.find hgex
  have hm : f m ≠ 0 := Nat.find_spec hfex
  have hn : g n ≠ 0 := Nat.find_spec hgex
  have hmpos : 0 < m := by
    exact Nat.pos_of_ne_zero (fun hm0 => hm (by simp [m, hm0]))
  have hnpos : 0 < n := by
    exact Nat.pos_of_ne_zero (fun hn0 => hn (by simp [n, hn0]))
  have hfbelow : ∀ k, k < m → f k = 0 := by
    intro k hk
    by_contra hfk
    exact Nat.find_min hfex hk hfk
  have hgbelow : ∀ k, k < n → g k = 0 := by
    intro k hk
    by_contra hgk
    exact Nat.find_min hgex hk hgk
  intro hzero
  have hcoeff : (f * g) (m * n) = 0 := by rw [hzero]; rfl
  rw [arithmeticFunction_mul_apply_of_first_nonzero f g m n hmpos hnpos hfbelow hgbelow]
    at hcoeff
  exact mul_ne_zero hm hn hcoeff

/-- Complex arithmetic functions form an integral domain under Dirichlet convolution. -/
instance arithmeticFunctionComplex_isDomain : IsDomain (ArithmeticFunction ℂ) := by
  letI : NoZeroDivisors (ArithmeticFunction ℂ) :=
    ⟨fun {f g} hfg => by
      by_cases hf : f = 0
      · exact Or.inl hf
      by_cases hg : g = 0
      · exact Or.inr hg
      exact (arithmeticFunction_mul_ne_zero hf hg hfg).elim⟩
  exact NoZeroDivisors.to_isDomain _

end

end GaloisForLFunctions.HTGeometry
