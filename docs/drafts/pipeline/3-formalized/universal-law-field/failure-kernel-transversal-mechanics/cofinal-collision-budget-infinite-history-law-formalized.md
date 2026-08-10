# Cofinal collision budget and infinite-history law — formalized

- **ID:** ULF-FKT-CCD-1-CORE
- **Stage:** 3-formalized
- **Type:** ROUTE-INDEPENDENT MECHANISM THEOREM (Lean-certified)
- **Lean module:** `GaloisForLFunctions.HTGeometry.ConstitutiveCofinalCollisionHistory`
- **Umbrella:** `GaloisForLFunctions.HTGeometry.UniversalLawField`

## Certified laws

For the exact collision weights `d_n = 1 / ((n+1)(n+2))`, Lean certifies:

1. telescoping finite capacity `A_N = 1 - 1/(N+1)`;
2. strict capacity growth and convergence to one;
3. exact tail `1/(N+1)` and convergence of the tail to zero;
4. depth-weighted term `(n+1)d_n = 1/(n+2)`;
5. nonsummability and divergence of weighted partial history;
6. bounded total collision budget, vanishing unseen tail, and infinite costed history coexist.

No `sorry`, `admit`, added axiom, `opaque`, `unsafe`, or computational proof is used.

## Audit

- direct foreground elaboration: pass, no warnings;
- `scripts/formal_tools.py lint`: pass;
- axiom print on nonsummability and the combined capstone:
  `[propext, Classical.choice, Quot.sound]`;
- final foreground umbrella build: pass, 11,514 jobs.

## Certification boundary

The countable source profiles, observer partitions, and unique simultaneous coupling realizing these
weights remain paper-only.  This Stage-3 card certifies the analytic mechanism, not that realization.

## Field meaning

Normalization bounds collision mass but does not bound lifted history.  A field theory must carry an
independent cost or uniform-integrability law; it cannot infer one from observer-loss alone.
