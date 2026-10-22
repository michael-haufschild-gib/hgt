# Failed route: Suzuki PNT-envelope/sublinearity Cesàro closure

- **Route:** Use the unconditional square-root magnitude envelope and PNT sublinearity of the weighted Chebyshev remainder to bound its anchored checkpoint high-pass, then feed that bound through completed Abel and aligned Gamma energy into the common HB/FZZ-P/RBH/PW-B Ward endpoint.
- **Status:** RETIRED — unconditional Lean no-go for this proof-strategy class.
- **Exact killing theorem:** `RHTower.suzukiPNTEnvelopeCesaroProducerRouteKilled`.

## Why it fails

`a(n)=sqrt n` obeys every abstract input used by the proposed step: it is nonnegative, monotone, lies in the exact square-root envelope, and is sublinear. Yet the sharp corpus prefix estimate implies

`anchoredCesaroHighPass a N ≥ sqrt(N+1)/3 - 2`,

so its current tends to `+∞`. Magnitude control does not control cancellation between a terminal value and its anchored history, even at the same asymptotic scale.

## Strongest positive survivor

`RHTower.tendsto_suzukiSqrtEnvelopeWitness_highPass_atTop` proves positive escape of the exact current, and `RHTower.suzukiSqrtEnvelopeWitness_highPass_lower` gives its explicit cofinal lower envelope.

Consequence for the live source problem: SWA-1 can survive only through signed arithmetic cancellation across weighted-Chebyshev checkpoints, a spectral oscillation identity, or a stronger invariant implying such cancellation. PNT `O(sqrt N)`, `o(N)`, positivity, monotonicity, and generic Tauberian regularity alone are terminal.

## Verification

Module `GaloisForLFunctions.RHTower.Suzuki.SuzukiPNTEnvelopeCesaroNoGo` passes direct Lean checking, targeted `lake build`, formal lint, and axiom audit. Imported by the RHTower umbrella. Frontier map was not modified by this work.
