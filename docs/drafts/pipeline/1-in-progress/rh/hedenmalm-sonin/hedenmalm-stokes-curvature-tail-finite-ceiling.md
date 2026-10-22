# Hedenmalm Stokes curvature-tail finite ceiling

- **ID:** `hedenmalm-stokes-curvature-tail-finite-ceiling`
- **Label:** `P-G147`
- **Stage:** `1-in-progress`
- **Type:** HIGH-FREQUENCY FAILURE LAW / CURVATURE-TAIL REDUCTION
- **Parent:** `hedenmalm-stokes-fourth-trace-curvature-budget-band.md`
- **Scientific status:** `[PAPER-PROVED] [LEAN-PROVED] [CORPUS-NEW SYNTHESIS] [NOT RH]`

## Result

Let `N(s)` be P-G144 curvature-normalized seam flux.  On positive frequencies beyond the
fourth-trace band, ask only for some finite real ceiling:

```text
exists C, forall s,
  1/2 < Re(s) < 1,
  233/20 < Im(s),
  zeta(s) != 0
    -> Re N(s) <= C.                                  (1)
```

Lean proves:

```text
(1) <-> RH.                                           (2)
```

This is strictly weaker pointwise than P-G144 budget: no sign and no aperture-dependent sharp
allowance are required.

It also proves the explicit contrapositive: if RH is false, then for every `C` there is a
zero-free right-strip point above `233/20` at which `Re N(s)>C`.

## Proof

For centered upper-strip `z`, put

```text
sL = 1/2 + z*i,
sR = conjugate(1-sL) = 1/2 + conjugate(z)*i.
```

Functional equation plus Schwarz reality give

```text
Re F(sR) = Im Tr_source(z).                            (3)
```

Central slope is real and negative, hence `Re F(sR) <= Re N(sR)`.  A finite ceiling in `(1)`
therefore gives a finite ceiling on positive-frequency source trace.  P-G146 supplies
`RHVerifiedThrough(243/20)` and the verified-height bounded-tail theorem then proves RH.

Conversely RH gives P-G144 sharp curvature budget.  Since aperture lies in `(0,1/2)`, its fixed
negative central slope yields a uniform finite ceiling.

## Anti-theatre audit

If RH is false, `Re N(s)` exceeds every prescribed finite level in the stated positive tail. This
is formally proved, not inferred from a missing sign. It identifies remaining obstruction as
pole-driven unbounded growth, not loss of one preferred sign convention.

- Exact source/curvature transport `(3)` is proved from FE, Schwarz, and prime--Gamma continuation.
- No zero computation, RH premise, new axiom, or residual-annulus emptiness is used in the forward
  criterion.
- This does not establish the finite ceiling; doing so would prove RH.
- Scientific gain is sharp failure classification: every finite-ceiling estimate is already
  enough, while mere pointwise finiteness is not.

## Formal artifact

```text
formal/GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmStokesCurvatureTailFiniteCeiling.lean
```

Principal declarations:

```text
seamFluxCochain_rightSchwarz_re_eq_continuedPrimeArchSourceRelativeTrace_im
hedenmalmCurvatureNormalizedRightPositiveTailBoundedAbove_iff_rh_of_verifiedHeight
hedenmalmCurvatureNormalizedRightPositiveTailBoundedAbove_twoHundredThirtyThree_twentieths_iff_rh
exists_hedenmalmCurvatureNormalizedSeamFlux_re_gt_above_twoHundredThirtyThree_twentieths_of_not_rh
```

## Remaining target

Prove any source-side finite upper ceiling on this positive tail. Sign is unnecessary. A valid
producer must remain uniform as frequency tends to infinity and survive arbitrarily close
approach to every hypothetical off-line pole; fixed-order sector positivity and finite annular
exclusions cannot do this.

## Gates

- [x] paper proof dependency closed
- [x] Lean proof
- [x] exact module build (`[12820/12820]`)
- [x] axiom audit (`propext`, `Classical.choice`, `Quot.sound` only)
- [ ] umbrella build
- [ ] RH

## Log

- 2026-08-13 — Opened after exhaustive higher-order source audit: strongest unconditional full
  height prefix remains fourth-trace `2365/16`; orders 20/21 and power 32 leave RH-equivalent
  residual annuli rather than a larger closed prefix.
- 2026-08-13 — Proved exact source/curvature transport, finite-ceiling/RH equivalence, and
  unbounded positive-spike failure law in Lean; wired module into `RHTower.lean`.
