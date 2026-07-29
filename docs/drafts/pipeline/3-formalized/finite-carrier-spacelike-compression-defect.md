# Finite-carrier spacelike compression defect

- **ID:** `finite-carrier-spacelike-compression-defect`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / SHARP CAPACITY BOUND / MONOIDAL NO-GO
- **Paper proof:** `../2-fully-proven/not_new_scientific_knowledge/finite-carrier-spacelike-compression-defect.md`
- **Lean module:** `GaloisForLFunctions.HTGeometry.FiniteCarrierSpacelikeCompression`
- **Scientific status:** `[FORMALIZED] [REDISCOVERED] [NOT NEW SCIENTIFIC KNOWLEDGE]`

## Formalized statements

For a finite-dimensional vector space \(V\) over a field \(K\) and every linear map

\[
\mu:V\otimes_KV\longrightarrow V,
\]

the module

`formal/GaloisForLFunctions/HTGeometry/FiniteCarrierSpacelikeCompression.lean`

proves unconditionally:

1. `finiteCarrierTensorCompression_kernel_lower_bound`:

   \[
   (\dim V)^2-\dim V\leq\dim\ker\mu;
   \]

2. `finiteCarrierTensorCompression_not_injective` — if \(\dim V\geq2\), then \(\mu\) is not
   injective;
3. `finiteCarrierTensorCompression_injective_finrank_le_one` — injectivity forces
   \(\dim V\leq1\);
4. `finiteCarrierTensorCompression_kernel_eq_of_surjective` — surjectivity gives exact equality in
   the kernel bound; and
5. `finiteCarrierTensorSelfEquiv_finrank_le_one` — a linear equivalence
   \(V\otimes V\simeq V\) forces \(\dim V\leq1\).

## Audit

Direct source check:

```text
lake env lean GaloisForLFunctions/HTGeometry/FiniteCarrierSpacelikeCompression.lean
PASS
```

Focused final build:

```text
lake build GaloisForLFunctions.HTGeometry.FiniteCarrierSpacelikeCompression
✔ [1558/1558] Built GaloisForLFunctions.HTGeometry.FiniteCarrierSpacelikeCompression
Build completed successfully (1558 jobs).
```

`#print axioms` was run from `/tmp/FiniteCarrierSpacelikeCompressionAxioms.lean` for all five
theorems. Dependencies are limited to:

```text
propext
Classical.choice
Quot.sound
```

Repository formal lint completed successfully. There is no `sorry`, `admit`, project `axiom`,
`opaque`, or `unsafe` declaration in the module.

## Exact scope

Lean proves a theorem of finite-dimensional linear algebra. It does not prove:

1. that any physical region has an exactly finite-dimensional carrier;
2. that spacelike physical composition is the full tensor product;
3. that gauge or gravitational constraints preserve the theorem's hypotheses;
4. that kernel dimension is entropy, area, gravity, or a force;
5. that event actualization creates a new carrier; or
6. any part of Einstein or Standard Model dynamics.

The theorem is the sharp finite-capacity structure missing from the universal sequential
fixed-carrier dilation:

> finite typed sequential networks fit in one direct sum, but two independent copies cannot be
> faithfully compressed into the same finite nonclassical carrier.

## Physical boundary

The formal theorem supplies a finite resource certificate, not a theory of gravity. Infinite
Hilbert spaces can be isomorphic to their tensor square; a composite may use a larger carrier; and
gauge constraints may replace a full tensor product by a matched physical subspace.

The next physical question is exact:

`BOUNDARY STORAGE OF FINITE COMPRESSION DEBT`

Derive a finite carrier and spacelike composition operationally for a bounded region, then determine
whether the unavoidable kernel debt is stored as gauge edge data, gravitational boundary data, or
genuine loss of independent possibilities.

## Gates

- [x] 0 → 1: exact finite-capacity tensor-compression claim
- [x] 1 → 2: sharp dependency-closed paper proof and physical audit
- [x] 2 → 3: unconditional Lean module, direct check, focused build, axiom audit, lint
- [ ] 3 → 4: intentionally blocked; physical carrier and boundary interpretation are absent

## Log

- 2026-07-29 — formalized the optimal kernel debt for every finite tensor-square compression and
  the resulting noninjectivity, dimension classification, equality, and equivalence corollaries.
