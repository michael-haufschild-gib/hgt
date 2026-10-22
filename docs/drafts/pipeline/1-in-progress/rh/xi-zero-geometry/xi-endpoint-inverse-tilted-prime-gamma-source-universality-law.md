# Xi-endpoint inverse-tilted prime–Gamma source universality law

- **ID:** xi-endpoint-inverse-tilted-prime-gamma-source-universality
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Source:** theorem-first closure of the inverse-tilted finite-prime/Gamma source identity and
  the cofinal Xi endpoint boundary limit
- **Statement:** Along every explicit endpoint approach point
  `zₙ = (1/2 - 1/(n+3))i`, the normalized inverse-tilted dyadic prime/Gamma source is exactly
  `-(XiC'/XiC)(zₙ)/zₙ`; consequently this concrete finite-prime source converges to the completed
  Xi endpoint curvature `-(XiC'/XiC)(i/2)/(i/2)`.

## Gates

- [x] 0 → 1 in-progress: generated from verified Lean endpoints
- [x] 1 → 2 fully-proven: dependency-closed paper proof, `[PROVED HERE]`
- [x] 2 → 3 formalized: exact-file Lean check passed; final global axiom audit pending
- [x] 3 → 4 publication-ready: post-proof literature audit found no exact collision

## Corpus inputs

- `inverseTiltedPrimeGammaSourceTrace_eq_continuedPrimeArchSourceRelativeTrace`
- `xiEndpointApproach_source_eq`
- `tendsto_normalizedContinuedPrimeArchSource_endpoint`

## Proof

`[PROVED HERE]` At the `n`th endpoint approach, put `ε = 1/(n+3)`.  Then
`0 < ε < 1/2 < 1`, and the centered zeta coordinate is exactly the real point `ε`.  The real
zero-free strip theorem supplies `ζ(ε) ≠ 0`; hence the inverse-tilted source theorem identifies
its reconstructed trace with the canonical continued prime–Gamma trace at that point.  Dividing
both sides by the same nonzero endpoint coordinate and negating identifies the two normalized
sources.  The endpoint theorem identifies the canonical normalized source pointwise with
`-(XiC'/XiC)(zₙ)/zₙ` and proves its limit.  Eventual equality transfers that limit to the
inverse-tilted source.  No computation is used.

## Strict gain over corpus endpoints

The inverse-tilted theorem only reaches a germ at the functional-equation center `z = 0`.  The
endpoint theorem only uses the abstract canonical continued prime–Gamma trace.  Their closure
transports the concrete inverse-tilted finite dyadic prime source to the distinct completion
boundary `z = i/2`, pointwise along the full cofinal sequence and in the limit.

## Lean certificate

- Module:
  `GaloisForLFunctions.RHTower.XiEndpointInverseTiltedPrimeGammaSourceUniversalityLaw`
- Main theorem:
  `inverseTiltedPrimeGammaSource_endpointUniversality`
- Source:
  `formal/GaloisForLFunctions/RHTower/XiEndpointInverseTiltedPrimeGammaSourceUniversalityLaw.lean`
- Exact-file check:
  `lake env lean GaloisForLFunctions/RHTower/XiEndpointInverseTiltedPrimeGammaSourceUniversalityLaw.lean`
  passed warning-free on 2026-07-23.
- Umbrella:
  imported by `formal/GaloisForLFunctions/RHTower.lean`.

## Novelty protocol

No literature search occurred before the dependency-closed proof.  Post-proof searches for the
joint phrases “inverse-tilted dyadic prime Gamma source Xi endpoint”, “Riemann Xi logarithmic
derivative endpoint i/2 prime Gamma trace”, and “finite prime source endpoint curvature” found
adjacent literature on Xi logarithmic derivatives and standard finite/infinite-prime plus Gamma
completion, but no statement identifying an inverse-tilted dyadic source pointwise along
`(1/2-1/(n+3))i` or transporting it to the `i/2` endpoint.  Closest primary result inspected:

- J. Arias de Reyna, *Riemann and the logarithmic derivatives of zeta*,
  <https://arxiv.org/abs/2605.27552>.

## Log

- 2026-07-23 — Whole-corpus terminal scan exposed the common continued prime–Gamma carrier.
- 2026-07-23 — Dependency-closed proof completed from existing Lean endpoints.
- 2026-07-23 — Exact theorem checked warning-free and wired into the RHTower umbrella.
- 2026-07-23 — Post-proof collision audit found no exact literature match.
