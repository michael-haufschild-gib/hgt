import GaloisForLFunctions.HTGeometry.EllipticLatticeOrder

/-!
# Clearing the poles of the monomials and of their combinations

The principal-jet machinery consumes hypotheses of the form
`0 ≤ meromorphicOrderAt ((· − p)^d · g) p`.  This file discharges them for the differential monomials
`fⁱ (f')ʲ` with `i, j ≤ N` and for their finite combinations, from a single order bound `−m` shared
by `f` and `f'` at `p`, with the uniform clearing exponent `d = 2mN`.

* `eq_zero_of_meromorphicOrderAt_neg` — a normal-form function takes the value `0` at a pole;
* `nonneg_order_const_mul`;
* **`nonneg_order_poleFactor_monomial`** and **`nonneg_order_poleFactor_combination`**.
-/

namespace GaloisForLFunctions.HTGeometry

/-- **A normal-form function vanishes at a pole.**  This is the normal-form convention, read off
from `MeromorphicNFAt.meromorphicOrderAt_eq_zero_iff`. -/
theorem eq_zero_of_meromorphicOrderAt_neg {f : ℂ → ℂ} {x : ℂ} (hNF : MeromorphicNFAt f x)
    (h : meromorphicOrderAt f x < 0) : f x = 0 := by
  by_contra hne
  exact absurd (hNF.meromorphicOrderAt_eq_zero_iff.mpr hne) (ne_of_lt h)

/-- Multiplying by a constant cannot lower the order below zero. -/
theorem nonneg_order_const_mul {g : ℂ → ℂ} {p : ℂ} (a : ℂ) (hg : MeromorphicAt g p)
    (h : 0 ≤ meromorphicOrderAt g p) :
    0 ≤ meromorphicOrderAt (fun z => a * g z) p := by
  classical
  have hfun : (fun z => a * g z) = (fun _ : ℂ => a) * g := rfl
  rw [hfun, meromorphicOrderAt_mul analyticAt_const.meromorphicAt hg]
  have hconst : 0 ≤ meromorphicOrderAt (fun _ : ℂ => a) p := by
    rw [meromorphicOrderAt_const]
    split
    · exact le_top
    · exact le_rfl
  exact add_nonneg hconst h

/-- **The clearing exponent `2mN` clears every monomial of bidegree at most `(N, N)`.** -/
theorem nonneg_order_poleFactor_monomial {f : ℂ → ℂ} {p : ℂ} {m N : ℕ}
    (hf : MeromorphicAt f p)
    (ho₁ : (-(m : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt f p)
    (ho₂ : (-(m : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (deriv f) p)
    {i j : ℕ} (hi : i ≤ N) (hj : j ≤ N) :
    0 ≤ meromorphicOrderAt (fun z => (z - p) ^ (2 * m * N) * diffMonomial f i j z) p := by
  have hij : i + j ≤ 2 * N := by omega
  have hbound := order_monomial_ge_of_le hf hf.deriv ho₁ ho₂ hij
  have hrw : m * (2 * N) = 2 * m * N := by ring
  rw [hrw] at hbound
  exact nonneg_order_poleFactor (meromorphicAt_diffMonomial hf i j) hbound

/-- **The same exponent clears every finite combination of those monomials.** -/
theorem nonneg_order_poleFactor_combination {f : ℂ → ℂ} {p : ℂ} {m N : ℕ}
    (hf : MeromorphicAt f p)
    (ho₁ : (-(m : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt f p)
    (ho₂ : (-(m : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (deriv f) p)
    (c : (Fin (N + 1) × Fin (N + 1)) → ℂ) :
    0 ≤ meromorphicOrderAt (fun z => (z - p) ^ (2 * m * N) *
      ∑ q : Fin (N + 1) × Fin (N + 1), c q * diffMonomial f (q.1 : ℕ) (q.2 : ℕ) z) p := by
  classical
  have hpow : MeromorphicAt (fun z : ℂ => (z - p) ^ (2 * m * N)) p := by fun_prop
  have hfun : (fun z : ℂ => (z - p) ^ (2 * m * N) *
      ∑ q : Fin (N + 1) × Fin (N + 1), c q * diffMonomial f (q.1 : ℕ) (q.2 : ℕ) z)
      = fun z : ℂ => ∑ q : Fin (N + 1) × Fin (N + 1),
        c q * ((z - p) ^ (2 * m * N) * diffMonomial f (q.1 : ℕ) (q.2 : ℕ) z) := by
    funext z
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun q _ => by ring)
  rw [hfun]
  refine nonneg_order_finset_sum _ _ (fun q _ => ?_) (fun q _ => ?_)
  · exact analyticAt_const.meromorphicAt.mul
      (hpow.mul (meromorphicAt_diffMonomial hf (q.1 : ℕ) (q.2 : ℕ)))
  · refine nonneg_order_const_mul _ (hpow.mul (meromorphicAt_diffMonomial hf _ _)) ?_
    exact nonneg_order_poleFactor_monomial hf ho₁ ho₂
      (Nat.lt_succ_iff.mp q.1.isLt) (Nat.lt_succ_iff.mp q.2.isLt)

end GaloisForLFunctions.HTGeometry
