# Infinite orbit quotients have no equivariant finite-support or Hilbert lift

- **ID:** `orbit-quotient-equivariant-lift-no-go`
- **Stage:** 3-formalized
- **Type:** NO-GO / REPRESENTATION-THEORETIC BRIDGE
- **Scientific status:** `[BRIDGE / NOT NEW SCIENTIFIC KNOWLEDGE]` The invariant-vector mechanism is
  standard. Its role here is to close a specific HGT/RH bridge without conditional formalization.
- **Source:** `../../5-failed/polarized-infinite-pair-face-rh-bridge.md`
- **Lean endpoint:** `formal/GaloisForLFunctions/OrbitQuotientLiftNoGo.lean`

## Theorem

Let `G` be a commutative group, `H` an infinite subgroup, and `R` a nontrivial commutative
semiring. The orbit pushforward

```text
R[G] -> R[G/H]
```

has no `G`-equivariant linear section. Moreover, any square-summable vector in the regular module
which is invariant under `H` is zero.

## Proof mechanism

The identity-orbit basis vector in `R[G/H]` is fixed by `H`. Equivariance would lift it to an
`H`-fixed vector. A nonzero finite-support coefficient propagates to the entire infinite orbit,
contradicting finite support. For a square-summable vector, the same propagation produces a
positive constant summable over the infinite subgroup, which is impossible.

## Lean surface

- `leftTranslateFinsupp`
- `eq_zero_of_infinite_subgroup_leftInvariant`
- `orbitPushforward`
- `leftTranslateOrbitFinsupp`
- `no_equivariant_orbitPushforward_section`
- `eq_zero_of_infinite_subgroup_leftInvariant_summable_normSq`
- `pairDifference_const`

The exact module builds. `#print axioms` for the capstones reports only `propext`,
`Classical.choice`, and `Quot.sound`.

## Application boundary

The theorem rules out a canonical regular-module or Hilbert-vector lift of scalar orbit-quotient
charges while the infinite stabilizer acts nontrivially. It does not prohibit distributional
orbit averages or groupoid objects carrying extra fiber data. Such objects are not Hilbert
potentials functorially determined by the original scalar pair-face invariant, so the existing
two-particle Sonin coherence theorem does not apply to them.

## Gates

- [x] finite-support invariant-vector theorem formalized
- [x] equivariant-section no-go formalized
- [x] square-summable invariant-vector theorem formalized
- [x] pair-difference common-mode kernel formalized
- [x] exact module build passed
- [x] standard-axiom audit passed
