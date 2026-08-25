# Cubic raw Euler/Wold magnitude overshoot (2026-08-25)

Formalized unconditional Route-P irregular-RH no-go:
- Let `T = -(normalizedPrimeArchMoment 2 - normalizedPrimeArchMoment 0 ^ 3 / 4)` and `S = ∑' n, sourceHorizontalEulerGammaWoldCubicNaturalDefect n`.
- Proved `0 < T < 1/10000`, using exact theta/Xi cubic identity, `thetaCuspRawEvenMoment_two_mul_zero_lt_six_mul_one_sq`, and `normalizedPrimeArchMoment_zero_lt_twentyNine_over_sixHundredTwentyFive`.
- Proved prime-2 identity `defect 2 = (95/16)*(log 2)^3` and `1/5 < S`, using nonnegativity, summability, and `one_third_lt_log_two`.
- Therefore `2000*T < S`, and signed raw current `-S` is strictly more negative than Xi residual `-T`. Identity-scale cubic landing is impossible.
- Positive survivor/design law: a viable coefficient-faithful microlocal landing must provide genuine source-derived contraction exceeding factor 2000; sign agreement alone is insufficient, while grade-forgetting normalization collapses to zero.

Lean module: `formal/GaloisForLFunctions/RHTower/RoutePPrimitiveGammaJuliaStokesPrimeGammaWallCubicRawMagnitudeOvershoot.lean`.
Stage-3 card: `docs/drafts/pipeline/3-formalized/route-p-prime-gamma-wall-cubic-raw-magnitude-overshoot.md`.
Direct module check and direct olean emission passed. Six new public declarations have only `[propext, Classical.choice, Quot.sound]`. Scratch and emitted olean removed. No target/umbrella build. Frontier map untouched.

Corpus audit found prior sign/chamber landing and normalized collapse but no raw magnitude comparison. Primary literature audit found general irregular RH/Malgrange/Fredholm tau/log-concave moment results, no exact completed-Xi Euler/Wold cubic magnitude theorem; absence is inference, not priority claim.