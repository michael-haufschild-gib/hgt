# Every identity partition admits a perfect source-test presentation

- **ID:** `source-test-partition-universality`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / NO-GO DISCRIMINATOR
- **Paper proof:**
  `../2-fully-proven/not_new_scientific_knowledge/source-test-partition-universality.md`
- **Lean module:**
  `GaloisForLFunctions.HTGeometry.SourceTestPartitionUniversality`
- **Scientific status:**
  `[FORMALIZED] [REDISCOVERED] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE]`

## Formalized theorem

For a source type \(\alpha\), the module defines:

```text
SourceTestPresentation α
SourceTestPresentation.ObservationallyEquivalent
SourceTestPresentation.observationalSetoid
```

A presentation consists of a test type and a propositional response relation. Two sources are
observationally equivalent when every test gives logically equivalent responses.

For every setoid \(s\) on \(\alpha\), define its quotient recognizer by
\[
T=\alpha/s,
\qquad
\rho(a,q)\Longleftrightarrow [a]=q.
\]
Lean proves unconditionally:

1. `quotientRecognizer_deterministic` — every source responds to exactly one quotient test;
2. `quotientRecognizer_exhaustive` — every quotient test is reached by some source;
3. `quotientRecognizer_observationallyEquivalent_iff` — two sources have the same response
   profile exactly when \(s\) relates them;
4. `quotientRecognizer_observationalSetoid_eq` — the induced observational setoid equals \(s\);
5. `everySetoid_has_perfect_sourceTestPresentation` — every identity partition admits one
   presentation satisfying all three properties simultaneously.

No finiteness, decidable equality, choice of representatives, probability model, topology,
algebra, tensor product, or computation is used.

## Verification

Direct source check:

```text
lake env lean GaloisForLFunctions/HTGeometry/SourceTestPartitionUniversality.lean
PASS
```

Focused final build:

```text
lake build GaloisForLFunctions.HTGeometry.SourceTestPartitionUniversality
✔ [115/115] Built GaloisForLFunctions.HTGeometry.SourceTestPartitionUniversality (457ms)
Build completed successfully (115 jobs).
```

`#print axioms` was run from `/tmp/SourceTestPartitionUniversalityAxioms.lean`.
The two existence lemmas are axiom-free. The exact observational-equivalence and packaged
universality theorems depend only on:

```text
propext
Quot.sound
```

There is no `sorry`, `admit`, project `axiom`, `opaque`, or `unsafe` declaration. The module is
imported by `GaloisForLFunctions.HTGeometry`.

## Exact scope

The result is elementary quotient effectiveness in `Set`. It proves that observational
exactness is universally programmable:

> choose an identity partition first, use its equivalence classes as tests, and the tests recover
> that partition perfectly.

It does not prove that physical tests are arbitrary, that a chosen equivalence is physical, or
that events generate their own recognizers.

## Physical no-go

The theorem rules out local recognizer completeness as a physical selector. Determinism,
exhaustivity, future separation, no unused tests, and exact agreement between responses and
identity can all be manufactured for any desired partition.

Consequently, the recognizer form
\[
\mathsf{LostJoint}_e\simeq\mathsf{BornRecognizer}_e
\]
is nontrivial only if both sides are constructed independently. Defining successor recognizers
from the lost-joint quotient makes the law true by construction.

## Positive survivor

The open object is no longer one source-test functor. It is a family of independently generated
local recognizer laws together with their cross-history comparison. Candidate interaction can
live only in an invariant obstruction to one composition-preserving globalization of all those
local laws.

This does not establish that such an obstruction is gravity or gauge curvature. It removes a
programmable local substitute from the open core.

## Gates

- [x] complete paper proof
- [x] parent and priority audit
- [x] exact unconditional Lean theorem
- [x] direct check
- [x] focused final build
- [x] axiom audit
- [x] umbrella import
- [ ] independently generated local recognizers
- [ ] cross-history obstruction theorem
- [ ] physical gravity, gauge, or prediction theorem

## Log

- 2026-07-30 — formalized quotient-test partition universality and preserved its exact
  `REDISCOVERED / BRIDGE` status.
