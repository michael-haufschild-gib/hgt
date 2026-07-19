# Normed sublevel splitting and transfer

- **ID:** `normed-sublevel-splitting-transfer`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `RHTower/SelbergTransfer.lean`

## Statement

Let `E` be a real normed vector space and let `Z,g,tau,zeta : alpha -> E`. Suppose `A > 0`,

```text
Z(x) = A g(x) + tau(x),
||g(x)-zeta(x)|| <= eps on B.
```

For arbitrary thresholds `lam,kappa`,

```text
{||Z|| <= A lam} intersect B
  subset {||zeta|| <= lam+kappa+eps} union ({A kappa <= ||tau||} intersect B).
```

Consequently, a countable family of these covers has total measure at most the measure of the one
global reference sublevel set plus the sum of the local exceptional-set measures.

## Paper proof

At a point with `||Z|| <= A lam`, either `A kappa <= ||tau||`, which is the exceptional branch,
or `||tau|| < A kappa`. In the second branch,

```text
A ||g|| = ||A g|| = ||Z-tau|| <= ||Z||+||tau||
          <= A lam + A kappa = A(lam+kappa).
```

Cancelling the positive scalar gives `||g|| <= lam+kappa`. On `B`, reverse triangle inequality
and `||g-zeta|| <= eps` then give

```text
||zeta|| <= ||g|| + ||zeta-g|| <= lam+kappa+eps.
```

For countably many blocks, take the union of the pointwise covers, use monotonicity of measure,
subadditivity for the union with the one global reference set, and countable subadditivity for the
exceptional sets. No measurability hypothesis on the sets is needed.

## Novelty audit

This is standard normed-space and measure algebra, not new scientific knowledge. Its structural
role is to separate the reusable two-threshold transfer law from the Riemann--Siegel/Selberg
specialization, eliminate the forced equal thresholds, and expose the exact abstract interface
consumed by any later value-relation approximation argument.

## Lean certificate

Module: `formal/GaloisForLFunctions/RHTower/SelbergTransfer.lean`.

Principal declarations:

- `norm_sublevel_split_subset`;
- `norm_sublevel_transfer_subset`;
- `norm_sublevel_split_transfer_subset`;
- `blockwise_norm_sublevel_transfer_measure_le`.

The previous `sublevel_split_subset`, `sublevel_transfer_subset`,
`sublevel_split_transfer_subset`, and `blockwise_sublevel_transfer_measure_le` declarations are
now compatibility wrappers at `E = C` and `kappa = lam`.

Validation on 2026-07-19:

- exact source check: `lake env lean GaloisForLFunctions/RHTower/SelbergTransfer.lean` — PASS;
- exact leaf build: `lake build GaloisForLFunctions.RHTower.SelbergTransfer` — PASS;
- axiom audit of the four general laws and representative wrappers — only
  `[propext, Classical.choice, Quot.sound]`.

## Gates

- [x] exact corpus and generated API searched; no generic two-threshold normed-space law found
- [x] dependency-closed paper proof
- [x] Lean formalization
- [x] exact leaf build and axiom audit
