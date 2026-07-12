# One anchored two-node Hurwitz Vandermonde reality chamber proves RH

- **ID:** `xi-hurwitz-anchored-vandermonde-reality-rh`
- **Stage:** 3-formalized
- **Type:** THEOREM / CONSTRAINT--ORIENTATION RH PREDECESSOR
- **Scientific status:** `[PROVED] [FORMALIZED] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Parent:** `../xi-hurwitz-constraint-orientation-product-law.md`

## Statement

Fix one actual Xi-divisor point `tau` on the critical line.  For any other divisor point `rho`,
form the same two-node Vandermonde separator used by the Hurwitz differential-independence proof:

```text
D(rho,tau) = det Vandermonde(-q(rho), -q(tau)).           (1)
```

Then

```text
RH <-> Im D(rho,tau)=0 for every actual Xi zero rho.      (2)
```

No determinant positivity, height ordering, or higher-rank minor is required.

## Proof

The two-node determinant is exactly

```text
D(rho,tau)=q(rho)-q(tau).                                 (3)
```

Because `tau` is on the critical line, `q(tau)` is real.  Hence reality of `(3)` forces `q(rho)`
real for every `rho`.  Functional-equation reflection sends `q(rho)` to its complex conjugate, so
every character is reflection-fixed.  Inside the open critical strip, character reality is
equivalent to `Re rho=1/2`.  This proves RH.  The converse follows from the exact negative-ray value
law.

For distinct divisor points the determinant is unconditionally nonzero, because the complete
Hurwitz differential-freeness theorem makes the monodromy character injective on the Xi divisor.

## Positive top-down chain

```text
unconditional Xi-indexed Hurwitz differential freeness
  -> distinct zeros have nonzero two-node Vandermonde separators
  -> choose one actual critical-line zero as a real character anchor
  -> require only reality of every anchored separator
  -> every Xi character is real
  -> functional-equation reflection fixes every Xi zero
  -> RH.                                                   (4)
```

This strictly simplifies the positive Vandermonde chamber theorem:

```text
all finite positive determinants
  is replaced by
one anchored family of real 2 x 2 determinants.           (5)
```

## Source obligation

The existence of critical-line Xi zeros is classical Hardy theory, but the current formal theorem
accepts one actual anchor explicitly.  The live orientation problem is to derive the reality of
the anchored HGT separators from a source symmetry, Hermitian form, monodromy pairing, or real
differential constraint without assuming the character is already reflection-fixed.

## Lean certificate

Module:

- `formal/GaloisForLFunctions/RHTower/XiHurwitzAnchoredVandermondeOrientation.lean`

Principal declarations:

- `xiHurwitzPairVandermondeDet`
- `xiHurwitzPairVandermondeDet_eq_sub`
- `xiHurwitzPairVandermondeDet_ne_zero_of_ne`
- `XiHurwitzAnchoredPairVandermondeReal`
- `riemannHypothesis_iff_xiHurwitzAnchoredPairVandermondeReal`
- `riemannHypothesis_of_exists_xiHurwitzAnchor_pairVandermondeReal`
- `xiHurwitzPairVandermondeDet_pos_real_of_rh`

The exact module build passes.  The nonvanishing and RH capstones use only `propext`,
`Classical.choice`, and `Quot.sound`.

## Gates

- [x] two-node determinant normal form proved
- [x] unconditional nonvanishing for distinct Xi points proved
- [x] positive chamber weakened to anchored reality
- [x] anchored reality composed to RH
- [x] exact build and axiom check
- [ ] direct Lean construction of one actual critical-line Xi anchor
- [ ] source theorem forcing anchored separator reality
- [ ] RH
