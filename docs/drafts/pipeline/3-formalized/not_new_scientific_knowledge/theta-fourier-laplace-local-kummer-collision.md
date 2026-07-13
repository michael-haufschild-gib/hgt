# Theta Fourier--Laplace local Kummer collision

- **ID:** `theta-fourier-laplace-local-kummer-collision`
- **Stage:** 3-formalized
- **Type:** THEOREM / TOP-DOWN RH CHAIN
- **Scientific status:** `[PROVED] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Lean:** `formal/GaloisForLFunctions/RHTower/ThetaFourierLaplaceLocalKummerCollision.lean`
- **Statement:** Common Kummer covers of the theta-cusp Fourier--Laplace transform and its
  derivative on the fixed band `-1/2 < Im(w) < 0` already force RH; no cover outside this band is
  needed.

## Goal

Let

```text
B- = {w in C : -1/2 < Im(w) < 0}.
```

The theta-cusp source has an analytic Fourier--Laplace transform `F` on `|Im(w)|<1`, and Lean
already proves `F=XiC` there. Lean proves the local chain

```text
d-th analytic roots of F and F' on B-, d>1
  -> d divides ord_w(F) and ord_w(F') at every zero in B-
  -> d divides two consecutive natural numbers
  -> no Xi zero with Re(rho)>1/2
  -> RH.
```

This strictly weakens the existing common-Kummer theorem, which requests roots on the entire
right half-plane. Every possible right-half Xi zero lies in `1/2<Re(rho)<1` and maps under
`w=(rho-1/2)(-i)` into `-1/2<Im(w)<0`. Even the rest of the natural Fourier--Laplace strip is
unused.

## Gates

- [x] 0 -> 1 in-progress: source-pure right-zero-band condition isolated
- [x] 1 -> 2 fully-proven: paper proof and non-circularity audit complete
- [x] 2 -> 3 formalized: Lean theorem, narrow build, axiom audit, lint
- [ ] 3 -> 4 publication-ready: standalone exposition and Lean certificate

## Non-circularity

Neither root condition is a zero-free assertion. A root of `F` only forces zero orders to be
divisible by `d`; a root of `F'` separately permits derivative zeros of orders divisible by `d`.
The contradiction uses the exact one-order loss at a zero of `F`. The premise is stated entirely
in terms of the fixed theta source transform and its differentiated source transform, with no zero
enumeration, sign condition, limiting divisor measure, or rectangular subpower hypothesis.

## Open core

`[OPEN CORE]` Construct either the common right-zero-band cover directly from theta-source
factorization, or, in degree two, construct an analytic square root of the differentiated
theta-cusp Fourier--Laplace transform on `B-` and combine it with the first Xi ladder rung.

## Principal declarations

- `thetaCuspFourierLaplaceRightZeroBand`
- `analyticOrderAt_thetaCuspFourierLaplace_and_deriv_of_zero`
- `riemannHypothesis_of_thetaCuspDerivativeCommonKummerRootRightZeroBand`
- `riemannHypothesis_of_rhLadder_one_of_thetaCuspDerivativeSquareRootRightZeroBand`

## Formal verification

The exact module and named target compile in the repository toolchain. The three principal
theorems depend only on `propext`, `Classical.choice`, and `Quot.sound`; the formal lint gate passes.
