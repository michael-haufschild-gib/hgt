# Monomial Tail Gate Height-Linear No-Go

- **ID:** monomial-tail-gate-height-linear-no-go
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / route guardrail
- **Source:** `../../3-formalized/not_new_scientific_knowledge/finite-degree-shifted-hankel-tail-stability.md`;
  `gamma-tail-law-shifted-square-tests.md`
- **Statement:** The coefficient-norm finite-degree tail gate cannot prove a
  height-linear determinant range. In the monomial basis, the verified bulk
  eigenvalue margin decays exponentially in degree, while the first hard-edge
  tail moment decays only at the reciprocal height scale.

## Setup

Let a positive real bulk have shifted moments

`L_k = sum_{x in B} M_x x^k`,

with `0<x<=R<1`, and let

`B_d=[L_{i+j+1}]_{i,j=0}^d`.

Let a remaining tail have absolute moment bound `eta_1`, so any Frobenius or
row-sum tail bound in `../../3-formalized/not_new_scientific_knowledge/finite-degree-shifted-hankel-tail-stability.md` satisfies

`F_d(eta)>=eta_1` and `G_d(eta)>=eta_1`.

## Theorem

The monomial coefficient-norm gate

`lambda_min(B_d)>F_d(eta)` or `lambda_min(B_d)>G_d(eta)`

can hold only if

`eta_1 < L_{2d+1} <= L_1 R^(2d)`.

Consequently, if a height cutoff `H` gives a first absolute tail moment

`eta_1(H) >> log H / H`,

then this gate can hold only in the logarithmic degree range

```text
d <= (log H + O(log log H))/(2 log(1/R)).
```

It cannot prove a height-linear range `d ~ cH`.

## Proof

The last standard basis vector `e_d` has Euclidean norm `1`. Its Rayleigh
quotient for `B_d` is the last diagonal entry:

```text
e_d^T B_d e_d = L_{2d+1}.
```

Hence

```text
lambda_min(B_d) <= L_{2d+1}.
```

Since every bulk atom lies in `(0,R]`,

```text
L_{2d+1} = sum_x M_x x^(2d+1)
        <= R^(2d) sum_x M_x x
        = R^(2d) L_1.
```

Also `F_d(eta)>=eta_1` and `G_d(eta)>=eta_1`, because the `(0,0)` tail entry is
bounded by `eta_1`. Therefore either sufficient condition from
`../../3-formalized/not_new_scientific_knowledge/finite-degree-shifted-hankel-tail-stability.md` implies

`eta_1 < lambda_min(B_d) <= L_1 R^(2d)`.

For the zeta reciprocal hard-edge tail beyond height `H`,
`gamma-tail-law-shifted-square-tests.md` gives the first absolute shifted
tail scale `eta_1(H) >> log H / H` at the sharp exponent level. Substitution
gives

```text
log H - O(log log H) <= 2d log(1/R) + O(1),
```

which is the stated logarithmic restriction on `d`.

## Consequence For The RH Route

This theorem kills a false repair of the finite-range discriminant claim. The
matrix gate in `../../3-formalized/not_new_scientific_knowledge/finite-degree-shifted-hankel-tail-stability.md` is a valid
sufficient condition, but in the monomial coefficient norm it is much too crude
to prove a range comparable to the RH verification height.

Therefore a real finite-height or all-order proof must use one of:

1. a relative Loewner estimate such as `||B_d^(-1/2) R_d B_d^(-1/2)||<1`;
2. an orthogonal-polynomial or Christoffel coordinate where the hard-edge
   small eigenvalue is not confused with source negativity;
3. a completed source identity proving the sign directly.

The old phrase "the verified bulk dominates the tail up to `d~H`" is not
salvaged by absolute moment bounds in the monomial basis.

## Gates

- [x] 0 -> 1 in-progress: monomial finite-tail gate audited.
- [x] 1 -> 2 fully-proven: Rayleigh quotient and hard-edge tail comparison
  written.
- [ ] 2 -> 3 formalized: finite matrix eigenvalue inequality; asymptotic tail
  bound kept as paper input.

## Log

- 2026-06-24 -- Codex: created after checking whether the finite-degree tail
  gate could justify a height-linear determinant range. It cannot; the useful
  target is the relative/source-Weyl gate, not monomial absolute tails.
