# Short-window endpoint payment

- **ID:** twin-prime-short-fourier-endpoint
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / BRIDGE
- **Source:** [actual Liouville short Fourier sums](../1-in-progress/twin-prime-short-fourier-formalization.md).
- **Statement:** The small-window part of the major-arc partial-summation integral is paid by the exact support-length first moment, without cancellation.

## Exact statement

For a finite set `s` of natural numbers, real `alpha`, positive
integers `d,q,W`, and nonnegative real `H`, put

```text
c(n) = lambda(n) exp(2 pi i alpha n),
F(h,x) = sum_(n in s) 1_[d(n-h),dn](x) c(n),
J(h) = integral_(x in R) |F(h,x)| dx,
B = H q/W^3.
```

The functions and integrals here are the actual finite sums.
In particular, no estimate is supplied as an assumption.
For every `h>=0`,

```text
J(h) <= d |s| h,                                      (1)
integral_(h in [0,B]) J(h) dh <= d |s| B^2/2.          (2)
```

Define the partial-summation endpoint cost using real division
(including the convention `0/0=0` when `H=0`):

```text
E = [W/(H q)] integral_(h in [0,B]) J(h) dh.
```

Then

```text
E <= d |s| H q/(2 W^5).                              (3)
```

If the integer parameters satisfy `d,q<=W`, this gives

```text
E <= |s| H/(2 W^3).                                  (4)
```

The Lean capstone can encode those integer ranges by
`d0,q0 : Fin W` and take `d=d0+1`, `q=q0+1`.
These are arithmetic domain data, not analytic assumptions.

## Closed paper proof

For each fixed integer `n`, the condition
`d(n-h)<=x<=dn` defines a closed measurable subset of the
`(h,x)` plane, since both defining functions are continuous.
Consequently `F` and `|F|` are measurable. For fixed `h`, each
summand has compact support in `x`, so both `F(h,.)` and its
norm are integrable. Its norm integral is exactly

```text
integral_R |1_[d(n-h),dn](x)c(n)| dx
 = max(dh,0) |c(n)|.
```

Triangle inequality, finite additivity of the integral, and
`|lambda(n)|<=1` give (1). This also includes `n=0`, where
the arithmetic function vanishes. The exponential has norm one.

Measurability of parameter integrals gives measurability of `J`.
On `[0,B]`, (1) dominates it by the integrable nonnegative
function `d |s| h`. Therefore `J` is integrable on this interval;
integrating (1) and using `integral_0^B h dh=B^2/2` proves (2).
Thus the argument does not rely on assigning zero to a
nonintegrable Bochner integral.

If `H=0`, both sides of (3) vanish. If `H>0`, multiply (2)
by `W/(Hq)>=0` and substitute `B=Hq/W^3`. Exact algebra
gives (3). Finally `dq<=W^2` proves (4).

The same proof gives (1)--(2) with `|s|` replaced by
`sum_(n in s)|c(n)|` for arbitrary complex coefficients.
That coefficient-mass version is also dependency-closed.

## Application and boundary

In the major-arc argument of
[Matomäki--Radziwiłł--Tao](https://arxiv.org/pdf/1503.05121v3),
Appendix A's mean-square estimate requires a minimum window
length. In the integral after (4.4), split at `B=Hq/W^3`.
Above this point, division by any positive integer `d0<=q`
leaves a window of length at least `H/W^3`. Below it, (4)
pays the contribution directly. If the support lies in
`[1,X/d]`, its cardinality is at most `X/d`, yielding the
cost `XH/(2dW^3)`. Also `B<=H/d` follows from `dq<=W^2`
and `W>=1`, so the endpoint lies in the large-window branch.

This is a repairable omitted case in the written application,
not a claim that the source theorem is false. The certificate
does not supply the complex mean-square theorem or uniform
nonpretentiousness of `lambda*chi`.

## Attack and status

- Corpus search for finite-support short-window integral bounds
  found the logarithmic overlap/Gallagher machinery, but no
  exact first-moment statement used here.
- The proof is elementary support geometry and integration.
  Verdict **BRIDGE**; no scientific-priority claim.
- Zero window length, empty support, `n=0`, measurability,
  integrability, and the small-window range are included.
- The current research core remains the actual arithmetic
  cancellation estimate. This endpoint payment does not replace it.

## Gates

- [x] Exact statement and source application audited.
- [x] Complete paper proof, including parameter integrability.
- [x] Lean coefficient-mass and actual Liouville bounds.
- [x] Lean weighted endpoint payment and range comparison.
- [x] Foreground leaf check, transitive axiom audit, umbrella import.

## Log

- 2026-10-24 — Isolated the short-window case during the
  major-arc audit. The exact paper statements are now formalized and audited.

## Lean certificate

Module: `formal/GaloisForLFunctions/twin-prime/ShortFourierEndpoint.lean`.
Namespace: `TwinPrime.ShortFourier`.

- `window_eq_short_sum`: exact identification with the actual finite short sum.
- `firstMoment_le`: general coefficient-mass bound.
- `measurable_window`, `stronglyMeasurable_firstMoment`,
  `integrableOn_firstMoment`: all parameter-integrability obligations.
- `integral_firstMoment_le`: integrated coefficient-mass bound.
- `firstMoment_liouville_le`, `integral_firstMoment_liouville_le`:
  inequalities (1)--(2) for the actual Liouville phase.
- `endpointCost_le`: inequality (3), including `H=0`.
- `endpointCost_le_of_bounded_parameters`: inequality (4).
- `minimum_window_le`, `split_le_endpoint`: both split-range comparisons.
- `endpointCost_on_initialSegment_le`: replaces support size by its
  positive integer carrier length.

The foreground leaf check passed without warnings. Fifteen transitive
axiom audits contain only `propext`, `Classical.choice`, and `Quot.sound`.
The own umbrella imports the module; no umbrella was compiled.
This closes the endpoint card, not the main arithmetic estimate.
