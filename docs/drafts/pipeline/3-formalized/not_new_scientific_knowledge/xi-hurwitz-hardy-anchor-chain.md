# A finite Hardy moment packet supplies the Hurwitz orientation anchor

- **ID:** `xi-hurwitz-hardy-anchor-chain`
- **Stage:** 3-formalized
- **Type:** THEOREM / CROSS-ROUTE RH CHAIN
- **Scientific status:** `[PROVED] [FORMALIZED] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Parent:** `xi-hurwitz-anchored-vandermonde-reality-rh.md`

## Statement

Let `F(t)=Re xi(1/2+it)` on one finite interval `[alpha,beta]`.  Suppose there are scalars
`S>0` and `M` such that

```text
S <= integral F(t)^2 dt,
|F(t)| <= M on [alpha,beta],
M * |integral F(t) dt| < S.                               (1)
```

Then the actual Xi divisor contains a point `tau` with `Re tau=1/2`.

If, in addition, every critical-line Xi anchor has real two-node Hurwitz Vandermonde separators,
then RH follows.

## Proof

The existing Hardy moment-gap theorem converts `(1)` into points `t1<=t2` with

```text
F(t1)F(t2)<=0.                                           (2)
```

Continuity and reality of Xi on the critical line give a zero between them.  Divisor positivity
turns that zero into an actual `XiDivisorSupport` anchor.  The anchored Hurwitz theorem then gives

```text
real two-node separators from tau
  -> every monodromy character is real
  -> every Xi zero lies on the critical line
  -> RH.                                                  (3)
```

## Positive chain

```text
one finite Hardy second-moment supply
  + one finite line sup
  + one finite first-moment cancellation
  -> Xi sign bracket
  -> one actual critical-line Xi-divisor anchor
  -> reality of anchored Hurwitz independence separators
  -> RH.                                                  (4)
```

This discharges the anchor face without assuming a zero location.  The remaining RH-sized face is
the orientation reality of the Hurwitz separators.  The formal scalar orientation energy now
compresses that face to the equality `xiHurwitzOrientationEnergy = 0`; its construction and
faithfulness are unconditional, but vanishing remains exactly equivalent to RH.

## Lean certificate

Module:

- `formal/GaloisForLFunctions/RHTower/XiHurwitzHardyAnchor.lean`

Principal declarations:

- `exists_xiHurwitzCriticalLineAnchor_of_sign_bracket`
- `exists_xiHurwitzCriticalLineAnchor_of_hardy_moment_gap`
- `XiHurwitzEveryCriticalAnchorPairVandermondeReal`
- `riemannHypothesis_of_xi_sign_bracket_and_allCriticalAnchorPairVandermondeReal`
- `riemannHypothesis_of_xi_hardy_moment_gap_and_allCriticalAnchorPairVandermondeReal`

## Gates

- [x] Xi sign bracket converted to an actual divisor anchor
- [x] Hardy moment gap converted to an actual divisor anchor
- [x] anchor producer composed with the Hurwitz orientation criterion
- [x] exact build and axiom check (standard axioms only: `propext`, `Classical.choice`, `Quot.sound`)
- [ ] source proof of the finite Hardy moment packet
- [ ] source proof of anchored separator reality
- [ ] RH
