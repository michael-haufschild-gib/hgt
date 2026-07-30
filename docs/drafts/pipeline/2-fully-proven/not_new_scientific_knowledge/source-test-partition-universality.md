# Every identity partition admits a perfect source-test presentation

- **ID:** `source-test-partition-universality`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / NO-GO DISCRIMINATOR
- **Scientific status:** `[PAPER-PROVED] [REDISCOVERED] [BRIDGE]`
  `[NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Source:** `../../1-in-progress/actuality-creates-future-law.md`
- **Statement:** Every equivalence relation is exactly the observational equivalence of a
  deterministic, exhaustive family of tests.
- **Lean target:**
  `GaloisForLFunctions.HTGeometry.SourceTestPartitionUniversality`

## Goal

Test whether a complete family of source-generated recognizers can select what counts as the same
physical thing. The theorem proves that existence, perfect discrimination, deterministic response,
and absence of unused tests do not select an identity law: all identity partitions admit such a
presentation.

## Definitions

Let \(A\) be a type of source alternatives. A **source-test presentation** is a type \(T\) and a
response relation
\[
\rho:A\times T\longrightarrow\mathsf{Prop}.
\]
Two sources are observationally equivalent when they have identical response profiles:
\[
a\equiv_\rho b
\quad\Longleftrightarrow\quad
\forall t\in T,\ \rho(a,t)\Longleftrightarrow\rho(b,t).
\tag{1}
\]

Call the presentation:

1. **deterministic** when every \(a\in A\) responds to exactly one test;
2. **exhaustive** when every test receives a response from at least one source; and
3. **exact for \(\sim\)** when \(a\equiv_\rho b\) if and only if \(a\sim b\).

## Exact theorem

`[PAPER-PROVED] [REDISCOVERED]`

For every set \(A\) equipped with an equivalence relation \(\sim\), there exists a deterministic,
exhaustive source-test presentation exact for \(\sim\).

More precisely, take
\[
T=A/{\sim}
\]
and define
\[
\rho(a,q)
\quad\Longleftrightarrow\quad
[a]=q.
\tag{2}
\]
Then:
\[
\forall a\in A,\ \exists!q\in T,\ \rho(a,q),
\tag{3}
\]
\[
\forall q\in T,\ \exists a\in A,\ \rho(a,q),
\tag{4}
\]
and
\[
\boxed{
\forall a,b\in A,\qquad
a\equiv_\rho b\Longleftrightarrow a\sim b.
}
\tag{5}
\]

## Paper proof

Fix \(a\in A\). Equation `(2)` holds for \(q=[a]\). If it also holds for \(q'\), then
\([a]=q'\), hence \(q'=q\). This proves `(3)`.

Every \(q\in A/{\sim}\) is an equivalence class \([a]\) for some \(a\in A\). Equation `(2)` then
gives \(\rho(a,q)\), proving `(4)`.

If \(a\sim b\), quotient soundness gives \([a]=[b]\). Therefore, for every \(q\),
\[
[a]=q\Longleftrightarrow[b]=q,
\]
so \(a\equiv_\rho b\).

Conversely, suppose \(a\equiv_\rho b\). Test with \(q=[a]\). Since
\(\rho(a,[a])\), observational equivalence gives \(\rho(b,[a])\), hence
\([b]=[a]\). Exactness of the quotient relation gives \(b\sim a\), and symmetry gives
\(a\sim b\). This proves `(5)`. Every dependency is closed.

## Parent and priority audit

The theorem is the elementary effectiveness of equivalence relations in `Set`: an equivalence
relation is the kernel pair of its quotient map. It is not new mathematics.

The physical framing also has strong parents:

1. [Foulis--Randall test-space approaches](https://arxiv.org/abs/2603.05682) begin with a
   catalogue of tests and define states through consistent response probabilities.
2. [State-and-effect triangles](https://arxiv.org/abs/1703.09034) organize states, predicates,
   and transformations after an adjunction or monad is supplied.
3. [Operational probabilistic theories](https://arxiv.org/abs/0910.1527) admit a range of
   non-signalling composite products; tests on individual systems do not select one physical
   tensor product.
4. [Conjugate-system reconstructions](https://arxiv.org/abs/1206.2897) derive Jordan structure
   from strong correlational, filter, and symmetry hypotheses after systems and basic
   measurements are supplied.

The theorem adds no reconstruction result. It supplies an exact hostile discriminator for the
local corpus.

## Physical no-go

`[LOCAL-RESEARCH INTERPRETATION; NOT A PHYSICS THEOREM]`

Any proposed identity partition can be made to look operationally exact by choosing its quotient
classes as tests. Therefore none of the following can select physical objects by itself:

- existence of recognizers;
- separation of every claimed distinction;
- one response per source;
- no unused recognizer;
- minimal quotient cardinality; or
- the equation “same responses if and only if same thing.”

Applied to the Dynamic Separability Conjecture, the result says that
\[
\mathsf{LostJoint}_e\simeq\mathsf{BornRecognizer}_e
\]
is tautologically realizable if the successor tests may be chosen after the lost-joint equivalence
is known. The two sides must be produced independently before their equivalence is asserted.

## Strongest positive survivor

The missing physical invariant cannot live inside one source-test presentation. Local recognition
is programmable. Candidate novelty can begin only with **cross-history compatibility of
independently generated recognizers**:

1. each event record generates successor tests without access to a desired identity quotient;
2. different histories generate recognizers independently;
3. their comparison preserves complete source consequences and independent composition; and
4. failure of joint globalization is invariant under changing either local presentation.

This sharpens the open core from “construct a source-test functor” to:

> construct independently generated local recognizer laws and classify the obstruction to one
> composition-preserving global recognizer.

That obstruction, not local test completeness, is the only remaining candidate carrier for
interaction, gauge curvature, gravity, and Hypertranscendental nonclosure.

## Gates

- [x] exact statement frozen
- [x] internal corpus audit
- [x] external parent audit
- [x] complete dependency-closed paper proof
- [x] novelty downgraded to `REDISCOVERED / BRIDGE`
- [x] exact Lean formalization
- [x] axiom audit; only `propext` and `Quot.sound`
- [x] targeted final module build:
  `lake build GaloisForLFunctions.HTGeometry.SourceTestPartitionUniversality`

## Log

- 2026-07-30 — extracted from hostile attack on regenerating recognizers.
- 2026-07-30 — paper-proved quotient-test universality and identified cross-history compatibility
  as strongest positive survivor.
- 2026-07-30 — formalized the exact theorem unconditionally in Lean and recorded the certificate
  in `../../3-formalized/source-test-partition-universality.md`.
