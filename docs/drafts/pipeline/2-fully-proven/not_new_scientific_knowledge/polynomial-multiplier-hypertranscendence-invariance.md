# Polynomial-multiplier invariance of functional hypertranscendence

- **ID:** polynomial-multiplier-hypertranscendence-invariance
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** `HTGeometry/GaugeReductionToMultiplicative.lean`; the generic substitution and triangular-solvability library
- **Statement:** Multiplication by any nonzero complex polynomial preserves differential algebraicity, and hence hypertranscendence, for an entire-smooth function.

## Goal

Close the sole remaining multiplicative interface in the regularized Herglotz gauge.  The result is
stated for an arbitrary nonzero polynomial, so it also subsumes the special multiplier
`1 + z^2` and every later polynomial-gauge consumer.

## Gates

- [x] 0 → 1  in-progress: exact open interface and polynomial substitution identified
- [x] 1 → 2  fully-proven: complete paper proof below, with no open dependency
- [ ] 2 → 3  formalized: Lean theorem `differentiallyAlgebraic_mul_polynomial_iff`, exact leaf build, and axiom audit
- [ ] 3 → 4  publication-ready: standalone paper treatment

## Statement

Let `a in C[z]` be nonzero and let `f : C -> C` be smooth to every complex order.  Then

```text
DA(z |-> a(z) f(z))  <->  DA(f),
HT(z |-> a(z) f(z))  <->  HT(f).
```

Consequently, if

```text
m(z) = b(z) + (1 + z^2) C(z)
```

with polynomial `b` and the smoothness required by the additive interface, then

```text
HT(m) <-> HT(C).
```

## Paper proof

Fix a differential relation of order `N` and write `x` for its spectral coordinate.  For each
`0 <= k <= N`, the Leibniz law gives

```text
(a f)^(k) = sum_(j=0)^k binom(k,j) a^(k-j) f^(j).
```

Substitute the right-hand side for the `k`-th jet variable of the relation while fixing `x`.
This is a polynomial substitution.  Ordered by jet degree, it is triangular: its `k`-th coordinate
has diagonal term `a(x) f^(k)` and a polynomial expression in lower jets.

The substitution is injective.  Indeed, on the Zariski-open locus `a(x) != 0`, any prescribed
finite target jet packet has a preimage: fix the spectral coordinate and solve the triangular
system recursively, dividing every layer by the common diagonal `a(x)`.  The substitution
nonvanishing criterion then says that it cannot kill a nonzero polynomial, because the nonzero
polynomial `a(x)` defines precisely the exceptional locus omitted by the point-map covering.
Therefore a nonzero relation for `a f` pulls back to a nonzero relation for `f`, proving
`DA(a f) -> DA(f)`.

Apply the same implication to the smooth product `a f` with the same multiplier in the reverse
presentation only after observing that the preceding argument is directional in the correct way:
to prove `DA(f) -> DA(a f)`, substitute the Leibniz jets of `a f` into a relation for `f` after
clearing the powers of the nonzero diagonal `a(x)`.  Equivalently, work over `C(x)`, apply the
inverse triangular substitution there, and clear its finite common denominator.  Clearing a
nonzero polynomial denominator preserves nonzeroness because `C[x, jets]` is a domain.  Evaluation
of the cleared relation vanishes identically, including at zeros of `a`, by polynomial identity
after multiplication by that common denominator.  Hence `DA(f) -> DA(a f)`.

For the Lean implementation the reverse direction can be obtained more economically by applying
the already proved forward transport to the product relation after constructing the cleared
inverse substitution, or by formalizing the same denominator-clearing argument directly.  Negating
the resulting equivalence yields the hypertranscendence law.  Combining it with additive
polynomial invariance closes the regularized Herglotz gauge.

## Novelty audit

This is a standard closure property of differential-algebraic functions, not new science.  Its
value here is interface closure: the live corpus had already isolated this exact missing theorem
and built all generic nonvanishing and triangular-solvability ingredients, but had not connected
them.  The general statement prevents a one-off `1 + z^2` wrapper.

## Log

- 2026-07-19 — exact paper theorem and proof recorded after corpus-first gap audit
