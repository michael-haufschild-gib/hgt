# Suzuki PNT-envelope Cesàro producer no-go (2026-08-31)

## Result
Killed the abstract strategy
`PNT O(√N) envelope + sublinearity -> bounded Suzuki anchored-Cesàro high-pass`,
even after granting nonnegativity and monotonicity.

Witness: `a n = Real.sqrt n`. Corpus theorem
`unitRieszSqrtPrefixMass_upper` gives
`anchoredCesaroHighPass a N >= (1/3) * sqrt(N+1) - 2`,
hence the current tends to `+∞` although `|a n| <= sqrt n` and `a n / n -> 0`.

## RH route consequence
Exact corpus chain:
weighted Chebyshev mass-error high-pass -> completed Suzuki Abel source ->
aligned Gamma completed energy (RH-equivalent) -> common HB/FZZ-P/RBH/PW-B Ward endpoint.
This result kills envelope-only, PNT-sublinearity-only, positivity, and monotone-regularity
proofs of the first arrow. Surviving SWA-1 work must prove genuinely signed arithmetic
cancellation across checkpoints or a stronger invariant implying it.

## Lean
- Module: `GaloisForLFunctions.RHTower.SuzukiPNTEnvelopeCesaroNoGo`
- Capstone: `suzukiPNTEnvelopeCesaroProducerRouteKilled`
- Positive survivor: `tendsto_suzukiSqrtEnvelopeWitness_highPass_atTop`
- Explicit lower law: `suzukiSqrtEnvelopeWitness_highPass_lower`
- Direct Lean PASS; targeted build PASS (14114/14114)
- Axioms: `propext`, `Classical.choice`, `Quot.sound`
- Formal lint PASS
- Wired into `GaloisForLFunctions.RHTower`

## Docs
- `docs/drafts/pipeline/3-formalized/suzuki-pnt-envelope-cesaro-producer-no-go.md`
- `docs/drafts/pipeline/5-failed/suzuki-pnt-envelope-sublinearity-cesaro-closure.md`

Frontier map was read-only and not edited by this work.