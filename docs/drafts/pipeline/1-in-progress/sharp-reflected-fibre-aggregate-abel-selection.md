# Sharp reflected-fibre and aggregate Abel selection

- **ID:** `sharp-reflected-fibre-aggregate-abel-selection`
- **Stage:** 1-in-progress
- **Type:** MASTER THEOREM STRENGTHENING / COLLISION CLASSIFICATION / SOURCE QUOTIENT
- **Statement:** The scale-covariant Bernstein--Abel selector descends to nonzero aggregate source fibres and its quadratic half-order and Abel laws hold at the sharp uniform scale threshold `R > M`.
- **Scientific status:** `[CONJECTURE] [PAPER PROOF IN PROGRESS] [LEAN IN PROGRESS] [NOVELTY UNVERIFIED] [NOT AN RH PROOF]`

## Goal

Remove two artificial hypotheses from the current tomography theorem:

1. replace the half-disk condition `R > 2M` by the sharp radial condition `R > M`;
2. replace injective, pointwise-nonzero indexing by the intrinsic quotient of the source by its
   nonzero aggregate fibres.

The survivor is positive: a successful scale-covariant selector is forced to live on the
aggregate support, and the complete reflected fibre geometry still supplies a strict quadratic
mixed-mode gap.

## Exact reflected-fibre claim

For nonreal equal-amplitude nodes with the same Bernstein ellipse phase, the existing rigidity
theorem gives

```text
v = u  or  v = 1 - conj(u).
```

In the second case the normalized reflected cross moment is exactly

```text
cross_n(u, 1-conj(u)) = choose(2n,n) * (u(1-u))^n.
```

Therefore

```text
|cross_n| <= (4|u||1-u|)^n,

(|u|+|1-u|)^2 - 4|u||1-u|
  = (|u|-|1-u|)^2.
```

If `u != 1-conj(u)`, then `|u| != |1-u|`, so the reflected cross base is strictly below the
diagonal base.  Distinct equal-amplitude nodes thus always possess a strict quadratic mixed gap:
different ellipse phases by compactness, and equal phases by the exact reflected formula.

For a source in `|z| <= M`, the condition `R > M` puts every real nonnegative normalized node
`z/R` in `[0,1)`.  Hence any superunit maximal-amplitude node is nonreal, and the complete collision
classification applies.  The threshold is sharp uniformly over the class: when `R <= M`, the
allowed positive real node `z=M` can itself have amplitude `2M/R-1 > 1`.

## Aggregate quotient claim

For an arbitrary absolutely summable indexed source `(c_i,z_i)`, define

```text
cHat(u) = sum_{i : z_i=u} c_i,
J = {u : C | cHat(u) != 0}.
```

Fibrewise absolute convergence gives

```text
sum_u |cHat(u)| <= sum_i |c_i|,
sum_i c_i F(z_i) = sum_u cHat(u) F(u)
```

for every bounded multiplier `F` occurring in a fixed moment or Bernstein row.  The subtype map
`J -> C` is injective, every weight is nonzero by definition, all support bounds and real
orientation statements descend, and cofinite convergence to zero descends because every occupied
aggregate fibre contains an original node.  Thus moments, finite scale polynomials, Bernstein
packets, confocal envelopes, and the transverse defect depend only on the nonzero aggregate
support.

## Gates

- [x] exact reflected-fibre formula identified
- [x] sharp strict-gap identity identified
- [x] sharp uniform threshold `R > M` identified
- [ ] dependency-closed paper proof of the complete collision theorem
- [ ] unconditional Lean theorem for the complete collision theorem
- [ ] dependency-closed aggregate quotient proof
- [ ] unconditional Lean aggregate quotient API and selector
- [ ] quantitative joint stability layer
- [ ] external novelty audit

## Open core

The Xi arithmetic radical remains separate.  No endpoint equivalence is to be presented as an
estimate toward `Delta_Xi = 0`; only a genuinely unconditional transverse-defect bound may alter
that status.

## Log

- 2026-07-18 — Exact reflected collision formula and the sharp `R > M` scale threshold isolated;
  aggregate quotient formulation fixed as the intrinsic replacement for injective indexing.
