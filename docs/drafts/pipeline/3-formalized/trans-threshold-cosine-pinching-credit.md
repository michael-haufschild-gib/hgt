# Positive cosine pinching credit at every fixed bandwidth

- **Stage:** 3-formalized
- **Type:** THEOREM / ACTUAL ZERO-SIDE SOURCE
- **Route:** Argon §4.1.
- **Target:** For every fixed positive bandwidth λ, the explicit unconditional `δλ=1/[200(10+720π²λ²)²]>0` and, at every sufficiently large height, disjoint pairs of actual simple critical zeta zeros whose normalized finite-grid overlap squares sum to at least `δλ N(T,2T)`. Bandwidth `4/3` is the trans-threshold specialization.

## Fixed source

Use bandwidth `4/3`, the canonical taper and width one, and cosine shape parameter one.
At height T the test window is
`phiD stdProfile 1 (params43.L T) 1`.
Realize it as a literal `Params` profile by
`x ↦ phiD stdProfile 1 (params43.L T) 1 (params43.L T/2−x)`;
retain `lam=4/3`, `w=1`. This separates the cosine shape from the bandwidth.
Its admissibility follows from the existing shape-one theorem without asserting `Params.Valid`,
whose definition requires bandwidth at most one.

## Proof route

1. The explicit triple-floor theorem gives `c=1/(10+720π²λ²)` for the shape-one
   cosine kernel on nonnegative gap pairs of span at most `6λ`. Its weighted circle
   identity strengthens the [additive rigidity theorem](cosine-kernel-additive-rigidity.md).
2. Uniform bulk finite-grid approximation follows with arbitrary error from the actual
   window's Parseval identity, derivative tail bound, and taper error. The existing
   `eventually_pairGridOverlap_atD_close` is restricted to `Params.Valid` and error `1/500`;
   it cannot be instantiated directly.
   `CosineWindowArbitraryBandwidth.lean` proves the finite bound
   `16(C/w)²/T+24w/L`, with `C=cDT`, and convergence for every positive bandwidth. It also proves
   the exact Poisson normalization and positive window mass for this source.
3. The existing unconditional simple critical census and negligible boundary strips give
   at least `5N/8` bulk simple critical zeros. At scale `α'=l(T)/(4π)`, Riemann--von
   Mangoldt gives `α'T≤3N/4` for large T. The existing short-triple packing inequality
   `9r≥3m−2α'T−6` then supplies at least `N/100` disjoint triples.
   Scaled span three becomes span `6λ` in the actual kernel coordinates, so no upper
   bandwidth restriction enters this packing argument.
4. Approximate each selected kernel correlation within c/2. Each triple contributes a
   distinct pair with overlap at least c/2, giving credit at least `c² N/200`.

## Boundaries

The conclusion is actual zero-side pinching, not a new prime-pair estimate or a 75% theorem.
The new cosine window must retain its own prime-side diagonal and surplus calibration;
the box-window constant `29/36` cannot be reused without proof.

## Lean

`CosineWindowArbitraryBandwidth.lean` proves window realization, finite-height approximation,
arbitrary-error convergence, Poisson normalization, and positive window mass.
`PositivePinchingEveryBandwidth.lean` proves `zetaCosine_explicit_disjointPairs` and
`zetaCosine_explicit_rankTrace` for the actual finite zero Gram `Az`, retaining the
boundary census `NII` explicitly. The positive-credit statements and bandwidth-four-thirds
specialization are corollaries. All ten public theorem audits across the sampling and
pinching leaves contain only `propext`, `Classical.choice`, and `Quot.sound`.

Both exact production leaves pass `lake --old env lean`; umbrella imports are present.

## Remaining

Matched prime-side certificate and signed discrepancy bound for the identical cosine window.
