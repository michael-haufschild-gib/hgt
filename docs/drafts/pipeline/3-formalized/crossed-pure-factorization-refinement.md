# Crossed pure factorizations force fourfold refinement

- **ID:** `crossed-pure-factorization-refinement`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / PURE-TENSOR REFINEMENT
- **Paper proof:** `../2-fully-proven/not_new_scientific_knowledge/crossed-pure-factorization-refinement.md`
- **Lean module:** `GaloisForLFunctions.HTGeometry.CrossedPureFactorizationRefinement`
- **Scientific status:** `[FORMALIZED] [REDISCOVERED] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE]`

## Formalized theorem

For arbitrary index types \(I,J,K,L\), an arbitrary field \(\Bbbk\), functions

\[
x:I\times J\to\Bbbk,\quad y:K\times L\to\Bbbk,
\]
\[
u:I\times K\to\Bbbk,\quad v:J\times L\to\Bbbk,
\]

and the crossed equality

\[
x_{ij}y_{k\ell}=u_{ik}v_{j\ell},
\]

the module

`formal/GaloisForLFunctions/HTGeometry/CrossedPureFactorizationRefinement.lean`

proves unconditionally:

1. `crossedBlockFactorization_refines` — if \(x\neq0\) and \(y\neq0\), there are one-index
   functions \(a,b,c,d\) with

   \[
   x_{ij}=a_ib_j,\qquad y_{k\ell}=c_kd_\ell;
   \]

2. `crossedPureFactorization_refines_to_four` — the common four-index tensor therefore satisfies

   \[
   x_{ij}y_{k\ell}=a_ib_jc_kd_\ell.
   \]

No finite-dimensional, Fintype, nonempty-index, ordered-index, Hilbert-space, positivity, or
computational hypothesis is used.

## Verification

Direct source check:

```text
lake env lean GaloisForLFunctions/HTGeometry/CrossedPureFactorizationRefinement.lean
PASS
```

Focused final build:

```text
lake build GaloisForLFunctions.HTGeometry.CrossedPureFactorizationRefinement
✔ [3007/3007] Built GaloisForLFunctions.HTGeometry.CrossedPureFactorizationRefinement (2.3s)
Build completed successfully (3007 jobs).
```

`#print axioms` was run from `/tmp/CrossedPureFactorizationRefinementAxioms.lean`. Both theorems
depend only on:

```text
propext
Classical.choice
Quot.sound
```

There is no `sorry`, `admit`, project `axiom`, `opaque`, or `unsafe` declaration in the module.
The module is reachable from `GaloisForLFunctions.HTGeometry`.

## Exact scope

The formal theorem is coordinate Segre rigidity. It proves neither a preferred tensor-product
structure nor a physical subsystem decomposition.

Its exact research use is:

> Once a pure nonzero history and a port alphabet are supplied, crossed exact bipartite
> factorizations refine to a common four-party product.

It does not:

1. generate the port alphabet;
2. define operational independence;
3. handle mixed process tensors or convex decomposition ambiguity;
4. descend under gauge or quantum-reference-frame changes;
5. treat gravitational dressing; or
6. derive spacetime, matter, forces, or dynamics.

## Physical survivor

The theorem removes “choosing between crossed pure cuts” from the fundamental open core. The
remaining ambiguity lives one level earlier:

```text
which interventions or distinctions count as ports at all?
```

A source-generated separability law must construct a relational intervention groupoid and retain
the complete record required when operational histories are mixed. Pure tensor factorization
alone cannot be the spacetime primitive.

## Gates

- [x] exact paper proof
- [x] external rediscovery audit
- [x] unconditional Lean theorem
- [x] direct check, focused build, axiom audit, umbrella reachability
- [ ] source-generated relational ports
- [ ] mixed/extremal factorization descent
- [ ] physical spacetime or force theorem

## Log

- 2026-07-30 — formalized the four-block crossed-factorization refinement over an arbitrary field
  and arbitrary index types.
