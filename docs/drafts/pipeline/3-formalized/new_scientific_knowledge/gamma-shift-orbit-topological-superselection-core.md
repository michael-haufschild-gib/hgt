# Gamma shift-orbit topological superselection core

- **ID:** `gamma-shift-orbit-topological-superselection-core`
- **Stage:** 3-formalized
- **Type:** FORMALIZATION
- **Scientific status:** `[FORMALIZATION]` of a `[NOVELTY UNVERIFIED]` paper theorem
- **Paper theorem:** `gamma-shift-orbit-topological-superselection-law`
- **Lean module:** `GaloisForLFunctions.HTGeometry.OrbitChargeExactSequence`

## Formalized surface

The module proves without placeholders, for every additive commutative coefficient group `A`:

- `intOrbitCellularBoundary_single`;
- `intOrbitCellularBoundary_pathPrimitive`;
- `intOrbitCellularBoundary_orbitPrimitive`;
- `additiveOrbitSum_embDomain`;
- `additiveIntShiftCoboundary_eq_intOrbitCellularBoundary`;
- `additiveOrbitSum_eq_zero_iff_exists_intOrbitCellularBoundary`;
- `intOrbitData_charge_normalForm`;
- `intOrbitData_sameCharge_iff_boundary`.

The central exact sequence is

```text
(Z ->_0 A) --boundary--> (Z ->_0 A) --total charge--> A -> 0.
```

An explicit finite path contraction proves that every orbit datum equals its total charge at one
site plus a finite boundary.  Consequently the total charge is a complete invariant of finite
shift-gauge equivalence, not merely a necessary obstruction.

## Deliberate paper boundary

The Lean theorem is coefficient-generic cellular algebra.  The paper theorem applies it to signed
Gamma exponent divisors and combines it with the separate analytic theorem that a nonzero
shift-orbit charge forces hypertranscendence.  Analytic Gamma products are not hidden behind any
axiom in this module.

## Physical/topological meaning

The formal object is literally the cellular chain complex of an integer translation orbit.  Its
zeroth homology is the coefficient group `A`; local edge gauges move charge but cannot change the
total component charge.  For integer Gamma exponents this is the superselection lattice whose
nonzero sectors are hypertranscendental by the paper-level analytic input.

## RH impact audit

The exact sequence proves that rational recurrence gauges cannot erase a nonzero archimedean
Gamma charge.  It contains no zeta zero, prime, positivity, or critical-line statement, so it is an
RH architecture check rather than an RH proof step.

## Verification

The previously missing exact-module object was built once with
`+GaloisForLFunctions.HTGeometry.OrbitChargeExactSequence`.  The touched source then passed direct
leaf compilation.  No umbrella, theorem-area, full, or self-concurrent build was run.

## Gates

- [x] explicit path contraction
- [x] exactness and canonical charge normal form
- [x] complete same-charge/gauge-equivalence law
- [ ] formal analytic Gamma quotient group
