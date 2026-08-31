import Mathlib

/-!
# Single monomials with nonzero coefficient

The predicate `IsScalarMonomial p` says `p = monomial s c` for some `c ≠ 0`, together with its
closure under products, powers and the generators `1`, `C c`, `X i`, `(−1)^n`.

This is the vocabulary the exponential-cascade cards need.  Their determinant reductions produce a
value of the shape `±(power of X)·(smaller determinant)`, so an induction carrying
`IsScalarMonomial` instead of `≠ 0` yields the *valuation* of the determinant, not merely its
nonvanishing — and the valuation is exactly what a Newton degeneration from the perturbed cascade to
the model cascade requires, since it certifies that the corrections stay strictly above the leading
term.
-/

namespace GaloisForLFunctions.HTGeometry

/-- A polynomial that is a single monomial with a nonzero coefficient. -/
def IsScalarMonomial (p : MvPolynomial ℕ ℂ) : Prop :=
  ∃ (c : ℂ) (s : ℕ →₀ ℕ), c ≠ 0 ∧ p = MvPolynomial.monomial s c

theorem IsScalarMonomial.ne_zero {p : MvPolynomial ℕ ℂ} (h : IsScalarMonomial p) : p ≠ 0 := by
  obtain ⟨c, s, hc, rfl⟩ := h
  simpa using hc

theorem IsScalarMonomial.mul {p q : MvPolynomial ℕ ℂ}
    (hp : IsScalarMonomial p) (hq : IsScalarMonomial q) : IsScalarMonomial (p * q) := by
  obtain ⟨c, s, hc, rfl⟩ := hp
  obtain ⟨d, t, hd, rfl⟩ := hq
  exact ⟨c * d, s + t, mul_ne_zero hc hd, by rw [MvPolynomial.monomial_mul]⟩

theorem isScalarMonomial_one : IsScalarMonomial (1 : MvPolynomial ℕ ℂ) :=
  ⟨1, 0, one_ne_zero, by simp⟩

theorem isScalarMonomial_C {c : ℂ} (hc : c ≠ 0) : IsScalarMonomial (MvPolynomial.C c) :=
  ⟨c, 0, hc, by rw [MvPolynomial.C_apply]⟩

theorem isScalarMonomial_X (i : ℕ) : IsScalarMonomial (MvPolynomial.X i : MvPolynomial ℕ ℂ) :=
  ⟨1, Finsupp.single i 1, one_ne_zero, by rw [MvPolynomial.X]⟩

theorem IsScalarMonomial.pow {p : MvPolynomial ℕ ℂ} (hp : IsScalarMonomial p) (n : ℕ) :
    IsScalarMonomial (p ^ n) := by
  induction n with
  | zero => simpa using isScalarMonomial_one
  | succ n ih => rw [pow_succ]; exact ih.mul hp

theorem isScalarMonomial_neg_one_pow (n : ℕ) :
    IsScalarMonomial ((-1 : MvPolynomial ℕ ℂ) ^ n) := by
  refine IsScalarMonomial.pow ?_ n
  refine ⟨-1, 0, by norm_num, ?_⟩
  rw [← MvPolynomial.C_1, ← map_neg, MvPolynomial.C_apply]

end GaloisForLFunctions.HTGeometry
