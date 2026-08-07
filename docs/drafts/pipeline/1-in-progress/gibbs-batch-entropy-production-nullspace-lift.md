# Gibbs batch entropy-production nullspace lift

- **ID:** `gibbs-batch-entropy-production-nullspace-lift`
- **Stage:** 1-in-progress
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
- [ ] Hostile proof audit
- [ ] Dependency-closed paper proof
- [ ] Lean formalization and axiom audit

