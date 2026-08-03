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

/-- **Root-of-unity partial fractions.**  For a primitive `p`-th root of unity `ω`,

`∑_{j<p} (x - ω^j y)⁻¹ = p x^{p-1} / (x^p - y^p)`,

whenever no factor vanishes.  This is the logarithmic derivative of the factorisation
`x^p - y^p = ∏_{j<p} (x - ω^j y)` in the first variable. -/
theorem sum_inv_sub_primitiveRoot_mul {p : ℕ} (hp : 0 < p) {ω : ℂ} (hω : IsPrimitiveRoot ω p)
    (x y : ℂ) (h : ∀ j ∈ Finset.range p, x - ω ^ j * y ≠ 0) :
    ∑ j ∈ Finset.range p, (x - ω ^ j * y)⁻¹ = (p : ℂ) * x ^ (p - 1) / (x ^ p - y ^ p) := by
  classical
  have hfac : ∏ j ∈ Finset.range p, (x - ω ^ j * y) = x ^ p - y ^ p := by
    have hpoly := X_pow_sub_C_eq_prod (R := ℂ) hω hp (α := y) (a := y ^ p) rfl
    have hval := congrArg (Polynomial.eval x) hpoly
    simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
      Polynomial.eval_prod] at hval
    exact hval.symm
  have hne : (x ^ p - y ^ p) ≠ 0 := by
    rw [← hfac]
    exact Finset.prod_ne_zero_iff.mpr h
  -- the derivative of the factorisation, evaluated at `x`
  have hderiv : (p : ℂ) * x ^ (p - 1)
      = ∑ j ∈ Finset.range p, ∏ k ∈ (Finset.range p).erase j, (x - ω ^ k * y) := by
    have hP : (∏ j ∈ Finset.range p, (Polynomial.X - Polynomial.C (ω ^ j * y)) :
        Polynomial ℂ) = Polynomial.X ^ p - Polynomial.C (y ^ p) :=
      (X_pow_sub_C_eq_prod (R := ℂ) hω hp (α := y) (a := y ^ p) rfl).symm
    have hd := congrArg Polynomial.derivative hP
    rw [Polynomial.derivative_prod_finset] at hd
    have hdRHS : Polynomial.derivative
        (Polynomial.X ^ p - Polynomial.C (y ^ p) : Polynomial ℂ)
        = Polynomial.C (p : ℂ) * Polynomial.X ^ (p - 1) := by
      simp [Polynomial.derivative_X_pow]
    rw [hdRHS] at hd
    have hval := congrArg (Polynomial.eval x) hd
    simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_prod,
      Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.derivative_sub, Polynomial.derivative_X, Polynomial.derivative_C,
      sub_zero, mul_one] at hval
    exact hval.symm
  rw [eq_div_iff hne, hderiv, ← hfac, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hsplit : ∏ k ∈ Finset.range p, (x - ω ^ k * y)
      = (x - ω ^ j * y) * ∏ k ∈ (Finset.range p).erase j, (x - ω ^ k * y) :=
    (Finset.mul_prod_erase _ _ hj).symm
  have hj0 : x - ω ^ j * y ≠ 0 := h j hj
  rw [hsplit, ← mul_assoc, inv_mul_cancel₀ hj0, one_mul]

/-- **Residue decomposition of `1/(m^p - n^p)`.**  Each simple factor `ω^j m - n` carries the
weight `1/(p n^{p-1})`.  Summing the weights over `j` is exactly the cancellation
`∑_{j<p} ω^j = 0` that makes the regularised sum over `m` converge. -/
theorem inv_pow_sub_pow_eq_weighted_sum {p : ℕ} (hp : 0 < p) {ω : ℂ} (hω : IsPrimitiveRoot ω p)
    (m n : ℂ) (hn : n ≠ 0) (h : ∀ j ∈ Finset.range p, n - ω ^ j * m ≠ 0) :
    (m ^ p - n ^ p)⁻¹
      = ((p : ℂ) * n ^ (p - 1))⁻¹ * ∑ j ∈ Finset.range p, (ω ^ j * m - n)⁻¹ := by
  have hpC : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne'
  have hden : ((p : ℂ) * n ^ (p - 1)) ≠ 0 := mul_ne_zero hpC (pow_ne_zero _ hn)
  have hsum := sum_inv_sub_primitiveRoot_mul hp hω n m h
  have hne : (n ^ p - m ^ p) ≠ 0 := by
    have hfac : ∏ j ∈ Finset.range p, (n - ω ^ j * m) = n ^ p - m ^ p := by
      have hpoly := X_pow_sub_C_eq_prod (R := ℂ) hω hp (α := m) (a := m ^ p) rfl
      have hval := congrArg (Polynomial.eval n) hpoly
      simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
        Polynomial.eval_prod] at hval
      exact hval.symm
    rw [← hfac]
    exact Finset.prod_ne_zero_iff.mpr h
  have hflip : ∑ j ∈ Finset.range p, (ω ^ j * m - n)⁻¹
      = -∑ j ∈ Finset.range p, (n - ω ^ j * m)⁻¹ := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show (ω ^ j * m - n) = -(n - ω ^ j * m) from by ring, inv_neg]
  rw [hflip, hsum]
  have hmn : (m ^ p - n ^ p) = -(n ^ p - m ^ p) := by ring
  rw [hmn]
  field_simp

end HTGeometry

