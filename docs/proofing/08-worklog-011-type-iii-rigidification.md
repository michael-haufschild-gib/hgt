# C-2026-06-18-011 Proof Attempt: Type-III Rigidification

Source: `docs/consolidated/08-conjectures-required.md` §4.

Claim status: `[CONJECTURE]`.

## Target Claim

One master object has a Z-discrete faithful index `kappa_-` at the
`q -> 1`/archimedean point, while type-II/III measured limits wash out to a
real-valued no-margin object; the crossing preserves the integer index.

## Attempt

The natural theorem is index stability. If `F_q` is a norm-continuous family of
Fredholm operators for `q in (q0,1]`, then the Fredholm index is constant:

```text
index(F_q) = index(F_1).
```

Thus a discrete `kappa_-` can survive a deformation only if the carrier remains
in a Fredholm/finite-negative-square class up to `q=1`.

## Weakened Theorem

For a norm-continuous Fredholm path, the integer index is locally constant.
Therefore type-III rigidification reduces to proving the archimedean
deformation remains Fredholm in the faithful carrier topology.

## Obstruction

The RH carrier is no-margin. If the path loses Fredholmness, develops essential
spectrum at zero, or passes to a measured trace, the integer can wash out. The
conjecture needs exactly the continuity theorem that no-margin makes fragile.

## Missing

An explicit `q -> 1` operator family, a topology, and proof of Fredholm
stability/finite negative-square stability at the limit.
