# The actual cosine prime certificate with pinching

- **Stage:** 1-in-progress
- **Type:** CANDIDATE / ACTUAL PRIME-GRAM TRANSPORT
- **Route:** Argon §4.1.
- **Parents:** [Actual pinching](../3-formalized/trans-threshold-cosine-pinching-credit.md), [cosine coefficient](../3-formalized/cosine-shape-one-improves-trans-threshold-calibration.md).

## Target

For the actual shape-one cosine window at bandwidth `4/3`, retain the matching
signed prime surplus and prove the simple-critical certificate with coefficient
`Hcos(4/3)+δ`, up to an arbitrarily small error. The formalized coefficient obeys
`Hcos(4/3)≥3/4+79/1250`; actual zero-side pair credit has δ>0.
The [explicit triple floor](../3-formalized/explicit-weighted-cosine-triple-floor.md) gives
`δλ=1/[200(10+720π²λ²)²]` for the actual pair and rank–trace credit.

## Exact source gap

`zetaCosine_positive_rankTrace` concerns the finite zero Gram `Az`.
`cosineWindowRate_fourThirds_eventually` evaluates its literal window moments.
Neither estimates the matching prime Gram or transfers the retained pair credit
through the tail seam. The existing trans-threshold certificate uses a box window.

## Mechanism

Keep the archimedean diagonal moment b and prime lag moment J in the generic
continuous-form expansion. `ThmD.PP.sumA2g_close` supplies the window moment
partial summation; the existing box proof instead replaces these moments by
one and one third. A generic `AdmWindow` supplies `LocalHypsCoreW` without the bandwidth cap.
The shape-one admissible window has a uniform derivative
constant, so its frozen, height-dependent profile must be transported through
the generic local-window and tail bounds. Retain the coalescent prime sum with
that same window at every step.

The resulting signed surplus bound remains the arithmetic problem; replacing
it by an unsigned factor-two envelope is excluded by the phase-resonance example.

## Endpoint conjecture

The same certificate should extend to every fixed `0<λ≤2`. At λ=2,
`θ₀=O(log T)` but its hat-unit normalization `θ₀/(aL)` is bounded.
The perturbation loss is then `O(1+√F)`, where F is the normalized prime
Frobenius square. When the proposed lower bound is positive, its retained
surplus forces `F=O(N)`; otherwise the conclusion is trivial. Thus this loss
is `o(N)` without requiring `θ₀→0`. The wide trace error is `O(√X+log T)=O(T)`,
also `o(N)`. Endpoint transport is not yet formalized.
