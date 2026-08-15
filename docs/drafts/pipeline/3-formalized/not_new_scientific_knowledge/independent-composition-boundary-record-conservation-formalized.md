# Independent-composition boundary-record conservation

- **ID:** `independent-composition-boundary-record-conservation`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / MINIMAL RECORD COMPLETION
- **Paper proof:** `independent-composition-boundary-record-conservation.md`
- **Lean module:** `GaloisForLFunctions.HTGeometry.IndependentCompositionBoundaryRecord`
- **Scientific status:** `[FORMALIZED] [REDISCOVERED] [NOT NEW SCIENTIFIC KNOWLEDGE]`

## Formalized statements

For finite-dimensional vector spaces \(V,E\) over a field \(K\), a public compression

\[
\mu:V\otimes_KV\to V
\]

and a complementary record

\[
R:V\otimes_KV\to E,
\]

the module

`formal/GaloisForLFunctions/HTGeometry/IndependentCompositionBoundaryRecord.lean`

proves unconditionally:

1. `independentCompositionBoundaryRecord_finrank_lower_bound` — injectivity of
   \((\mu,R)\) implies

   \[
   (\dim V)^2-\dim V\leq\dim E;
   \]

2. `minimalIndependentCompositionBoundary_finrank` — at the minimal record dimension,
   source and public-plus-record target have equal dimension;
3. `independentCompositionBoundary_bijective_of_minimal_record` — minimal faithful recording
   makes \((\mu,R)\) bijective;
4. `independentCompositionCompression_surjective_of_minimal_record` — the public compression is
   then surjective;
5. `independentCompositionKernelRecord_bijective_of_minimal_record` — the restricted record
   \(\ker\mu\to E\) is bijective;
6. `independentCompositionKernelRecordEquiv` — the resulting linear equivalence
   \(\ker\mu\simeq E\); and
7. `independentCompositionBoundaryEquiv` — the full linear equivalence

   \[
   V\otimes_KV\simeq V\oplus E.
   \]

## Verification

Direct source check:

```text
lake env lean GaloisForLFunctions/HTGeometry/IndependentCompositionBoundaryRecord.lean
PASS
```

Focused final build:

```text
lake build GaloisForLFunctions.HTGeometry.IndependentCompositionBoundaryRecord
✔ [3003/3003] Built GaloisForLFunctions.HTGeometry.IndependentCompositionBoundaryRecord (3.7s)
Build completed successfully (3003 jobs).
```

`#print axioms` was run from
`/tmp/IndependentCompositionBoundaryRecordAxioms.lean` for all seven declarations. Every
declaration depends only on:

```text
propext
Classical.choice
Quot.sound
```

There is no `sorry`, `admit`, project `axiom`, `opaque`, or `unsafe` declaration in the module.

Repository lint was executed and reached the independent global umbrella check. It is currently
blocked by a pre-existing/unrelated reachability error:

```text
error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower:
GaloisForLFunctions.RHTower.FinitePrimePolarizedIrregularTriple
```

The new HTGeometry module is imported by `GaloisForLFunctions/HTGeometry.lean`; direct check,
focused build, axiom audit, forbidden-declaration scan, and `git diff --check` all pass.

## Exact scope

Lean proves finite-dimensional linear algebra. It does not prove:

1. physical finiteness of a bounded region;
2. exact tensor factorization of gravitational or gauge subsystems;
3. source-generation or canonical selection of \(R\);
4. localization of \(E\) on a boundary;
5. an entropy or area law;
6. spacetime, holography, gravity, gauge forces, or matter; or
7. the Dynamic Separability Conjecture.

The exact bridge is:

> If full independent tensor capacity is compressed into a finite public carrier but conserved by
> a minimal complementary record, erased joint directions and record directions are linearly
> equivalent, and public output plus record reconstructs the full joint input.

## Gates

- [x] 0 → 1: exact capacity-and-record claim isolated
- [x] 1 → 2: complete proof and hostile standardness audit
- [x] 2 → 3: unconditional Lean module, direct check, focused build, axiom audit
- [ ] global repository lint: blocked by unrelated RHTower umbrella reachability
- [ ] 3 → 4: intentionally blocked; physical derivation and novelty absent

## Log

- 2026-07-30 — formalized exact minimal boundary-record conservation for finite independent
  composition and audited all declarations.
