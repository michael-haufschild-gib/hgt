# Prime--archimedean exact finite positive-atomic block law for RH

- **ID:** `prime-arch-exact-finite-positive-atomic-block-rh`
- **Stage:** 2-fully-proven
- **Type:** PROVED REDUCTION (not new scientific knowledge)
- **Formal status:** the approximate local-closure law is formalized; the exact cubature upgrade
  below is not yet formalized

## Theorem

Let

```text
m_n = normalizedPrimeArchMoment n.
```

The following are equivalent.

1. RH.
2. For every `N : ℕ`, there exist `d ≤ N + 1`, masses `w_i ≥ 0`, and nodes `x_i ≥ 0`
   (`i < d`) such that

   ```text
   m_n = sum_{i<d} w_i x_i^n                 for every n < N.
   ```

Consequently, for every admissible rectangular prime--polar source, the critical negative-source
abscissa bound is equivalent to exact finite positive-atomic representability of every finite
prime--Gamma moment block.

## Proof

### RH gives exact finite atomic blocks

Assume RH and write

```text
lambda_j = xiThermalNode (xiThermalEnumeration j).
```

The formal Xi thermal laws give `lambda_j > 0` and, for every `n`,

```text
sum_j lambda_j^(n+1) = m_n.
```

In particular, with `M = m_0`,

```text
M > 0,                 sum_j lambda_j = M.
```

Every `lambda_j` lies in `[0,M]`: all terms are nonnegative and no term exceeds their sum.
Fix `N` and define the compact moment curve

```text
v : [0,M] -> R^N,
v(x)_n = x^n.
```

For `J : ℕ`, put the unspent mass at the zero node and form

```text
b_J = sum_{j<J} (lambda_j/M) v(lambda_j)
      + (1 - sum_{j<J} lambda_j/M) v(0).
```

The coefficients are nonnegative and sum to one, so `b_J` belongs to
`conv(v([0,M]))`.  Coordinatewise power-sum convergence gives

```text
b_J -> (m_n/M)_{n<N}.
```

The convex hull `conv(v([0,M]))` is compact.  Indeed, Caratheodory's theorem represents every
point of this convex hull using at most `N+1` points.  After padding with zero coefficients, the
convex hull is the image of

```text
Delta_N x [0,M]^(N+1)
```

under the continuous map

```text
((a_i),(x_i)) |-> sum_i a_i v(x_i),
```

where `Delta_N` is the compact standard simplex.  Hence the convex hull is closed.  The limit of
the `b_J` therefore remains in the convex hull.  Thus there are `d ≤ N+1`, coefficients
`a_i ≥ 0` summing to one, and nodes `x_i in [0,M]` with

```text
(m_n/M)_{n<N} = sum_{i<d} a_i v(x_i).
```

Taking `w_i = M a_i` gives the required exact moment identities.

### Exact finite atomic blocks give RH

Assume the exact finite-block property.  For every cutoff `N` and tolerance `epsilon > 0`, use
the exact witness for that `N` and let

```text
m'_n = sum_{i<d} w_i x_i^n.
```

Then `m'_n = m_n` for `n<N`, so the coordinatewise error is zero and hence is less than
`epsilon`.  Therefore the normalized prime--Gamma source satisfies
`PrimeArchFinitePositiveAtomicLocalMomentClosure`.  The formal theorem

```text
primeArchFinitePositiveAtomicLocalMomentClosure_iff_riemannHypothesis
```

implies RH.

This also proves the prime--polar abscissa formulation by the formal theorem

```text
rectangularPrimePolarSource_negativeAbscissa_le_one_iff_primeArchFinitePositiveAtomicLocalClosure.
```

## Impact on the proof burden

The approximation tolerance can be removed on paper.  It is enough to solve one exact finite
nonnegative algebraic moment problem at every cutoff, and at most `N+1` atoms are required for an
`N`-coordinate block.  No thermodynamic limit, compatibility between cutoffs, infinite-dimensional
observable, or global representing measure is part of the hypothesis.

The remaining formal task is a finite-dimensional compact-convex cubature lemma specialized to
the moment curve, followed by its application to the Xi thermal power sums.  Until that lemma is
formalized, publication text must describe this card as paper-proven rather than Lean-proven.

## Gates

- [x] 0 -> 1 candidate isolated
- [x] 1 -> 2 complete paper proof
- [ ] 2 -> 3 Lean formalization and axiom audit
- [ ] 3 -> 4 publication-ready integration
