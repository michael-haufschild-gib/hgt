# Gibbs batch entropy-production nullspace lift

- **ID:** `gibbs-batch-entropy-production-nullspace-lift`
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Conjecture label:** C15
- **Inputs:** `GibbsAntiscaleFirstTraceFrame`, `ThermodynamicAffinityHolonomy`

## Conjecture

The order-free Route E batch dispersion admits a canonical off-diagonal thermodynamic lift. For a
finite batch with positive weights `w_i` and signed leaf values `v_i`, use energy `E_i = v_i`,
inverse temperature `1`, and Hermitian amplitude

```text
A_ij = sqrt(w_i w_j).
```

Then every KMS entropy-production edge is nonnegative and is strictly positive exactly when
`v_i != v_j`. Consequently total entropy production vanishes exactly when the Route E pairwise
dispersion vanishes.

## Why this matters

C14 proved diagonal first-trace data give zero response. C15 supplies the forced replacement: a
canonical Hermitian cross-leaf amplitude. It does not assume RH and does not identify the limiting
prime--archimedean trace; it converts the existing Gibbs escape mode into genuine KMS transition
mass without changing its exact nullspace.

## Proof plan

At `beta = 1`, equality of finite Gibbs state weights is equivalent to equality of energies because
the real exponential is injective and the common partition is positive. The amplitude is Hermitian
and has positive squared norm under positive weights. The entropy-production factor is positive
iff endpoint Gibbs populations differ, hence iff `v_i != v_j`. Finite nonnegative-sum rigidity then
identifies the zero set of total entropy production with constancy of all `v_i`, which is already
the zero-set classification of Route E pairwise dispersion.

## Gates

- [x] Exact conjecture frozen
- [x] Hostile proof audit
- [x] Dependency-closed paper proof
- [x] Lean formalization and axiom audit

## Hostile audit result

The construction does not yet give the prime--archimedean response limit: its transition
frequencies are differences of chosen batch values. What it proves is exact and weaker: diagonal
inertness is repaired canonically, positivity is unconditional, and no batch-escape information is
lost at the nullspace level.

## Novelty audit

Lehmann/KMS response and weighted pairwise dispersion are individually standard. Targeted searches
found no theorem identifying the nullspace of this canonical square-root-weight KMS lift with the
Route E batch residual. Provisional novelty passes as a new cross-corpus synthesis; no claim is made
that the abstract physical mechanism is literature-new.

## Formalization

`GaloisForLFunctions.RHTower.GibbsBatchEntropyProductionLift` proves the Hermitian amplitude,
edge positivity classification, total-production zero classification, and exact equivalence with
Route E pairwise-dispersion vanishing. Exact `lake env lean` verification passes; axiom audit
reports only `propext`, `Classical.choice`, and `Quot.sound`. Module is wired into `RHTower.lean`.
Final module build audit passed 2026-08-13
(`lake build GaloisForLFunctions.RHTower.GibbsBatchEntropyProductionLift`), axiom audit re-verified
clean on the intensity classification and both total-production zero classifications.
