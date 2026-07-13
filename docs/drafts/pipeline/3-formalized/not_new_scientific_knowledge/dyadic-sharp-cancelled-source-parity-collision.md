# Dyadic sharp cancelled-source parity collision

- **ID:** `dyadic-sharp-cancelled-source-parity-collision`
- **Stage:** 3-formalized
- **Type:** TOP-DOWN RH CHAIN / ADJACENT SOURCE PARITIES
- **Scientific status:** `[FORMALIZED] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Lean parents:** `CCMSharpPrimeWindowCancellation`, `RHLadderTheory`
- **Lean capstone:** `CCMSharpPrimeWindowParityCollision`

## Statement

Let `C_sharp` be the pole-cancelled dyadic sharp prime source already formalized in Lean.  The
existing local order theorem says that at the shifted point belonging to a right-half Xi zero of
multiplicity `m`,

\[
\operatorname{ord} C_{\mathrm{sharp}}=m-1.
\]

Every shifted right-half Xi pole lies in the narrow continuation band

\[
1<\operatorname{Re}s<\frac32.
\]

Consequently the following two constraints are incompatible with any right-half Xi zero:

1. every zero of `C_sharp` in this band has even order;
2. `RHLadder 1` holds, so every right-half Xi multiplicity is even.

The preferred chain is

```text
analytic square factorization of the cancelled source on 1 < Re s < 3/2
  -> every cancelled-source order in the band is even
RHLadder 1
  -> every right-half Xi zero has even multiplicity
ord(C_sharp) = ord(Xi) - 1
  -> two consecutive orders would both be even
  -> no right-half Xi zero
  -> RH.
```

Zero-freeness on `Re s > 1` remains a stronger sufficient condition: it forces source order zero,
which is even.  It is no longer the minimal source obligation.

## Non-circularity audit

Neither premise alone is RH.  `RHLadder 1` is only the first parity rung, equivalent to an analytic
square root of Xi on the right half-plane.  The cancelled-source parity condition concerns the
complete zero divisor of an explicit entire prime-window expression inside a fixed source-defined
band; RH does not presently imply it in the corpus.  It permits even-multiplicity source zeros and
therefore is strictly weaker than source zero-freeness.  The proof uses the one-order mismatch
between the two parities, not a renamed zero-location condition.

This route is disjoint from sampled rectangular lower bounds and from the Taylor anisotropic-flux
route.  It consumes the sharp-source cancellation identity only as a local multiplicity reader.

## Formal theorem

Lean proves

```text
DyadicSharpPrimeCancelledSourceSquareOnCollisionBand
  -> DyadicSharpPrimeCancelledSourceEvenOrderOnCollisionBand
  -> RHLadder 1
  -> RiemannHypothesis.
```

It also proves the stronger zero-free version and the version with any rung `RHLadder k`,
`1 <= k`, by monotonicity down to the first rung.  The adapter theorem identifies the shifted
regularized-zeta order with the underlying Xi order before the parity collision is applied.

The formal declarations are:

- `analyticOrderAt_shiftedRegularizedZeta_eq_xi_order`;
- `xiRightShiftedPole_mem_dyadicSharpPrimeCollisionBand`;
- `not_three_halves_lt_re_xiRightShiftedPole`;
- `dyadicSharpPrimeCancelledSourceEvenOrderOnCollisionBand_of_square`;
- `riemannHypothesis_of_rhLadder_one_of_dyadicSharpPrimeCancelledSource_evenOrder`;
- `riemannHypothesis_of_rhLadder_of_dyadicSharpPrimeCancelledSource_evenOrder`;
- `riemannHypothesis_of_rhLadder_one_of_dyadicSharpPrimeCancelledSource_square`;
- `riemannHypothesis_of_rhLadder_one_of_dyadicSharpPrimeCancelledSource_rightZeroFree`;
- `riemannHypothesis_of_rhLadder_of_dyadicSharpPrimeCancelledSource_rightZeroFree`.

## Positive continuation-seam law

Lean proves every shifted right-half Xi pole lies strictly in `1 < Re s < 3/2`.  The proposed
ordinary Dirichlet-series interface for the continued sharp source is formulated only on
`Re s > 3/2` and is not a dependency of this theorem.  Therefore, even after that separate module
is repaired, a coefficient-sign or leading-term argument confined to absolute convergence cannot
discharge the parity collision.  A successful proof must control the analytically continued source
across the `Re s = 3/2` seam.

## Open core

`[OPEN CORE A]` Prove `RHLadder 1` from a source construction that does not inspect Xi zero
multiplicities.  Existing symplectic, square-root, and Weyl interfaces may feed this premise, but an
RH-equivalent all-rung construction is unnecessary.

`[OPEN CORE B]` Construct an analytic square root of the explicit cancelled source on
`1 < Re s < 3/2`, or directly prove that every one of its zeros there has even order.  The function
is already holomorphic on the larger half-plane `Re s > 1/2`.  A valid proof must use its
prime-window formula, not the identity at Xi zeros or an assumed divisor classification.

The first attack on B is to seek a square-times-unit factorization or a mod-two divisor law after
the logarithmic derivative cancellation.  A single odd-order zero of `C_sharp` in the collision
band kills this source-parity route.  Even-order zeros do not.

## Gates

- [x] exact order-loss reader available
- [x] first parity rung available as an independent formal interface
- [x] formalize the collision implication
- [ ] discharge `RHLadder 1`
- [ ] prove cancelled-source even-order law or analytic square factorization on the collision band
- [ ] RH

## Verification

The capstone module and its cancellation parent build successfully in the repository toolchain.
Formal lint passes.  The collision-band, square-to-even-divisor, and RH capstones use only
`propext`, `Classical.choice`, and `Quot.sound`.
