import Mathlib

/-!
# Matching of commensurable power frequencies

Two exponential families with frequency sets `{n^{1/a}}` and `{m^{1/b}}` overlap exactly at the
pairs `(n, m)` with `n^b = m^a`.  When `a/b = p/q` in lowest terms this forces `n = t^p` and
`m = t^q` for a single integer `t`, so the overlap is carried by the perfect `p`-th and `q`-th
powers — a set of density zero unless `p = q = 1`.

The algebraic core is stated without any construction: given a Bézout relation `p·u = q·v + 1` and
a witness `t` for the exact division `n^u = m^v · t`, the conclusion `n = t^p`, `m = t^q` follows by
cancellation alone.  This is the mechanism by which the Bohr mean of a product of two exponential
twists of different degrees is supported on perfect powers.
-/

namespace HTGeometry

/-- **Commensurable frequency matching.**  If `p·u = q·v + 1`, `n^q = m^p`, and `t` witnesses the
division `n^u = m^v · t`, then `n = t^p` and `m = t^q`. -/
theorem pow_eq_pow_of_bezout {p q u v n m t : ℕ} (hm : m ≠ 0)
    (hb : p * u = q * v + 1) (h : n ^ q = m ^ p) (ht : n ^ u = m ^ v * t) :
    n = t ^ p ∧ m = t ^ q := by
  have hmp : m ^ (v * p) ≠ 0 := pow_ne_zero _ hm
  have hmq : m ^ (v * q) ≠ 0 := pow_ne_zero _ hm
  constructor
  · have e1 : n ^ (u * p) = m ^ (v * p) * t ^ p := by
      rw [pow_mul, ht, mul_pow, ← pow_mul]
    have e2 : n ^ (u * p) = m ^ (v * p) * n := by
      have huv : u * p = q * v + 1 := by rw [mul_comm]; exact hb
      rw [huv, pow_succ, pow_mul, h, ← pow_mul]
      ring
    have := e1.symm.trans e2
    exact (Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hmp) this).symm
  · have e1 : n ^ (u * q) = m ^ (v * q) * t ^ q := by
      rw [pow_mul, ht, mul_pow, ← pow_mul]
    have e2 : n ^ (u * q) = m ^ (v * q) * m := by
      have h1 : n ^ (u * q) = m ^ (p * u) := by
        rw [mul_comm u q, pow_mul, h, ← pow_mul, mul_comm p u]
      rw [h1, hb]
      ring
    have := e1.symm.trans e2
    exact (Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hmq) this).symm

/-- In the equal-degree case `p = q = 1` the matching is the identity: the overlap is the full
diagonal. -/
theorem pow_eq_pow_of_bezout_diag {n m : ℕ} (h : n ^ 1 = m ^ 1) : n = m := by
  simpa using h

end HTGeometry
