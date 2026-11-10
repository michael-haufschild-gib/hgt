import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheArithmeticSquareIsCofree

/-!
# The arithmetic square is a δ-ring

The `p`-derivation `δ_p x = (F_p x − x^p)/p` of the arithmetic square satisfies the identities of a
δ-ring. The square has no `p`-torsion, so each identity follows from the fact that `F_p` is a ring
homomorphism (`natCast_mul_left_cancel_ghost`).

* **Sum rule, with the carry** (`natCast_mul_delta_add`):
  `p (δ_p(x + y) − δ_p x − δ_p y) = x^p + y^p − (x + y)^p`. The defect of additivity of `δ_p` is the
  first Witt carry polynomial.
* **Product rule** (`delta_mul`): `δ_p(xy) = x^p δ_p y + y^p δ_p x + p δ_p x δ_p y`.
* **Constants** (`delta_one`, `delta_teichmuller`): `δ_p 1 = 0` and `δ_p [a] = 0`.
* **`δ_p` commutes with every Frobenius** (`delta_frobenius`): `δ_p F_k = F_k δ_p`.
-/

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

/-- The arithmetic square has no `p`-torsion. -/
theorem natCast_mul_left_cancel_ghost {p : ℕ} (hp : p ≠ 0) {a b : ghostRing}
    (h : (p : ghostRing) * a = (p : ghostRing) * b) : a = b := by
  refine ghostRing_ext fun n => ?_
  have hn := congrArg (ghostComponent n) h
  rw [map_mul, map_mul, map_natCast] at hn
  exact mul_left_cancel₀ (by exact_mod_cast hp) hn

variable (p : ℕ+) (hp : p.Prime)

/-- **The sum rule**: the defect of additivity of `δ_p` is the Witt carry polynomial. -/
theorem natCast_mul_delta_add (x y : ghostRing) :
    ((p : ℕ) : ghostRing) * (delta p hp (x + y) - delta p hp x - delta p hp y) =
      x ^ (p : ℕ) + y ^ (p : ℕ) - (x + y) ^ (p : ℕ) := by
  have h1 := frobenius_eq_pow_add_delta p hp (x + y)
  have h2 := frobenius_eq_pow_add_delta p hp x
  have h3 := frobenius_eq_pow_add_delta p hp y
  rw [map_add] at h1
  linear_combination -h1 + h2 + h3

/-- **The product rule**: `δ_p(xy) = x^p δ_p y + y^p δ_p x + p δ_p x δ_p y`. -/
theorem delta_mul (x y : ghostRing) :
    delta p hp (x * y) = x ^ (p : ℕ) * delta p hp y + y ^ (p : ℕ) * delta p hp x +
      ((p : ℕ) : ghostRing) * delta p hp x * delta p hp y := by
  have hp' : (p : ℕ).Prime := hp
  refine natCast_mul_left_cancel_ghost hp'.ne_zero ?_
  have h1 := frobenius_eq_pow_add_delta p hp (x * y)
  have h2 := frobenius_eq_pow_add_delta p hp x
  have h3 := frobenius_eq_pow_add_delta p hp y
  rw [map_mul, h2, h3] at h1
  linear_combination -h1

/-- `δ_p 1 = 0`. -/
theorem delta_one : delta p hp 1 = 0 := by
  have hp' : (p : ℕ).Prime := hp
  refine natCast_mul_left_cancel_ghost hp'.ne_zero ?_
  have h1 := frobenius_eq_pow_add_delta p hp 1
  rw [map_one, one_pow] at h1
  linear_combination -h1

/-- **The Teichmüller points are constants**: `δ_p [a] = 0`. -/
theorem delta_teichmuller (a : ℤ) : delta p hp (teichmuller a) = 0 := by
  have hp' : (p : ℕ).Prime := hp
  refine natCast_mul_left_cancel_ghost hp'.ne_zero ?_
  have h1 := frobenius_eq_pow_add_delta p hp (teichmuller a)
  rw [frobenius_teichmuller_eq_pow] at h1
  linear_combination -h1

/-- **`δ_p` commutes with every Frobenius.** -/
theorem delta_frobenius (k : ℕ+) (x : ghostRing) :
    delta p hp (frobenius k x) = frobenius k (delta p hp x) := by
  have hp' : (p : ℕ).Prime := hp
  refine natCast_mul_left_cancel_ghost hp'.ne_zero ?_
  have h1 := frobenius_eq_pow_add_delta p hp (frobenius k x)
  have h2 := congrArg (frobenius k) (frobenius_eq_pow_add_delta p hp x)
  rw [map_add, map_pow, map_mul, map_natCast, frobenius_frobenius] at h2
  rw [frobenius_frobenius, mul_comm k p] at h1
  linear_combination h2 - h1

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
