# Irreversible event coupling is square-zero and vanishes in the symmetry quotient

- **ID:** `event-square-zero-unification-boundary`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / NONSEMISIMPLE UNIFICATION BOUNDARY
- **Parent:** `../2-fully-proven/not_new_scientific_knowledge/event-square-zero-unification-boundary.md`
- **Scientific status:** `[LEAN-PROVED] [REDISCOVERED] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Lean module:** `GaloisForLFunctions.HTGeometry.EventSquareZeroUnificationBoundary`

## Exact formal result

For modules \(K,I\) over an arbitrary commutative ring, `EventUpperBlock` records

\[
(a,b,d)\in
\operatorname{End}(K)\times\operatorname{Hom}(I,K)\times\operatorname{End}(I)
\]

with upper-block multiplication

\[
(a,b,d)(a',b',d')=(aa',ab'+bd',dd').
\]

The Lean module proves unconditionally:

1. `EventUpperBlock.toEnd_injective` — block parameters are faithfully represented as
   endomorphisms of \(K\times I\);
2. `EventUpperBlock.toEnd_mul` — block multiplication is ordinary endomorphism composition;
3. `EventUpperBlock.radical_mul_radical` — every product of two pure off-diagonal channels is
   zero;
4. `EventUpperBlock.diagonal_mul_radical` and
   `EventUpperBlock.radical_mul_diagonal` — endpoint algebras act on the event direction from the
   left and right;
5. `EventUpperBlock.diagonalReporter_surjective` and
   `EventUpperBlock.diagonalReporter_eq_zero_iff` — the endpoint reporter is onto and erases
   exactly the pure event channels;
6. `EventUpperBlock.symmetryQuotientEquiv` — quotienting equality by the erased event direction is
   exactly equivalent to
   \(\operatorname{End}(K)\times\operatorname{End}(I)\);
7. `EventUpperBlock.symmetryQuotientEquiv_add` and
   `EventUpperBlock.symmetryQuotientEquiv_mul` — this equivalence transports addition and
   multiplication to componentwise endpoint operations; and
8. `EventUpperBlock.commutator_eq`, `EventUpperBlock.radical_commutator`, and
   `EventUpperBlock.commutator_radical` — the pure event direction is commutative under its own
   bracket and transforms by the exact endpoint bimodule commutator \(ac-cd\).

No dimension, field, finite-rank, semisimplicity, Lie-group, spacetime, gauge-force, or physical
event hypothesis is used.

## Scientific boundary

This is standard triangular block algebra. It does not derive a physical nilpotent symmetry or
evade Coleman--Mandula by itself.

Its research consequence is exact:

```text
retain noninvertible off-diagonal event data
  -> non-product square-zero endpoint coupling remains

quotient to diagonal invertible symmetry data
  -> exact product of endpoint algebras.
```

Thus any proposed unification through this interface must derive the irreversible event channel
physically and use its bimodule or typed quadratic soldering data. Merely identifying the diagonal
quotient with Lorentz and Standard Model symmetries gives no unification.

## Verification

- [x] source checked with
  `lake env lean GaloisForLFunctions/HTGeometry/EventSquareZeroUnificationBoundary.lean`
- [x] final module build with
  `lake build GaloisForLFunctions.HTGeometry.EventSquareZeroUnificationBoundary`
- [x] axiom audit: strongest declarations use only Lean's standard `propext` and `Quot.sound`
- [x] formal lint

## Gates

- [x] 0 → 1: exact nonsemisimple discriminator stated
- [x] 1 → 2: dependency-closed paper proof and parent-theory audit
- [x] 2 → 3: final build, axiom audit, and lint
- [ ] 3 → 4: not a publication target; parent-theory bridge only

## Log

- 2026-07-29 — formalized the faithful upper-block algebra, square-zero event direction, exact
  quotient equivalence, transported operations, and bimodule commutator without physical
  assumptions.
- 2026-07-29 — direct source check, repository lint, single final module build, and axiom audit
  passed.
