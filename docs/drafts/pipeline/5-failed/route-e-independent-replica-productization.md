# Route E independent replica productization

- **ID:** `ROUTE-E-INDEPENDENT-REPLICA-PRODUCTIZATION-001`
- **Stage:** 5-failed
- **Type:** FALSIFIED
- **Source:** Route E replica-shuffle conditional-parity ANOVA
- **Statement:** Independent Bernoulli replication cannot reduce histogram parity ANOVA below the
  original one-copy product parity mean squared.

## Goal

Test whether averaging exact component-histogram biases over independent replicas supplies the
strict-half parity-energy estimate missing from the physical Route E replica shuffle.

## Gates

- [x] 0 → 1 in-progress: exact finite product law stated
- [x] 1 → 2 fully-proven: dependency-closed bias-variance proof
- [x] 2 → 3 formalized: Lean module
- [ ] 3 → 4 publication-ready: not pursued as a standalone preprint

## Approach

For one binary component with activation probability `q` and `M` replicas, let `K` be its replica
occupancy. The exact histogram bias is `1-2K/M`. Product-Bernoulli moments give

```text
E[(1-2K/M)^2] = (1-2q)^2 + 4q(1-q)/M.
```

Independent components multiply these local second moments.

## No-go closure

- **Exact killing theorem/mechanism:** Every local variance correction is nonnegative, so the
  independent-replica ANOVA is at least
  `(prod_c (1-2q_c))^2`, exactly the original one-copy product parity mean squared. Increasing
  replica order removes only the positive `1/M` correction and cannot improve the scalar rate.
- **Strongest positive survivor:** Exact finite bias-variance identity above, valid at every
  replica order. It isolates the only possible gain: non-product correlations created by physical
  aperture conditioning or another source-specific constraint.
- **New insight:** Replica count and independent Euler productization cannot be the cancellation
  producer. The live replica route must estimate aperture-conditioned prime-histogram parity ANOVA;
  unbounded component density remains necessary but is not sufficient.
- **Status:** Paper proof dependency-closed. Lean theorems
  `routeE_replica_degree_bias_second_moment`, `routeE_independent_replica_localANOVA_eq`, and
  `routeE_independent_replica_productANOVA_floor` in
  `formal/GaloisForLFunctions/RHTower/RouteEIndependentReplicaANOVAFloor.lean`.

## Log

- 2026-09-12 — independent productization falsified; exact ANOVA floor formalized.
