import Mathlib

/-!
# The root-of-unity packet filter

Two elementary identities for a primitive `q`-th root of unity `ω` in `ℂ`.

* `prod_one_add_primitiveRoot_pow_mul` — the multiplicative filter
  `∏_{j<q} (1 + ω^j u) = 1 - (-u)^q`, obtained by evaluating the splitting of `X^q - (-u)^q` at
  `X = 1`.
* `sum_primitiveRoot_pow_mul` — the additive filter (character orthogonality)
  `∑_{j<q} ω^{jr} = q · [q ∣ r]`.

Together they collapse a finite root-of-unity packet of Weierstrass primary factors, and they
isolate a single residue class of exponents in any finite expansion whose coefficients are
invariant under `z ↦ ω z`.
-/

namespace HTGeometry

open Finset Polynomial

variable {q : ℕ} {ω : ℂ}

/-- **Multiplicative filter.**  For a primitive `q`-th root of unity `ω`, the finite root-of-unity
packet of linear factors collapses: `∏_{j<q} (1 + ω^j u) = 1 - (-u)^q`.

Obtained by evaluating the splitting `X^q - C ((-u)^q) = ∏_{j<q} (X - C (ω^j · (-u)))` at
`X = 1`. -/
theorem prod_one_add_primitiveRoot_pow_mul (hq : 0 < q) (hω : IsPrimitiveRoot ω q) (u : ℂ) :
    ∏ j ∈ Finset.range q, (1 + ω ^ j * u) = 1 - (-u) ^ q := by
  have h := X_pow_sub_C_eq_prod (R := ℂ) hω hq (α := -u) (a := (-u) ^ q) rfl
  have h1 := congrArg (Polynomial.eval (1 : ℂ)) h
  simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
    Polynomial.eval_prod, one_pow] at h1
  rw [h1]
  exact Finset.prod_congr rfl fun j _ => by ring

/-- **Additive filter.**  Summing the `r`-th powers of all `q`-th roots of unity gives `q` when
`q ∣ r` and `0` otherwise. -/
theorem sum_primitiveRoot_pow_mul (hω : IsPrimitiveRoot ω q) (r : ℕ) :
    ∑ j ∈ Finset.range q, ω ^ (j * r) = if q ∣ r then (q : ℂ) else 0 := by
  have hpow : ∀ j : ℕ, ω ^ (j * r) = (ω ^ r) ^ j := by
    intro j; rw [← pow_mul, mul_comm]
  simp only [hpow]
  by_cases hdvd : q ∣ r
  · have h1 : ω ^ r = 1 := (hω.pow_eq_one_iff_dvd r).mpr hdvd
    simp [h1, hdvd]
  · have h1 : ω ^ r ≠ 1 := fun h => hdvd ((hω.pow_eq_one_iff_dvd r).mp h)
    have hqpow : (ω ^ r) ^ q = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, hω.pow_eq_one, one_pow]
    rw [geom_sum_eq h1, hqpow]
    simp [hdvd]

end HTGeometry
