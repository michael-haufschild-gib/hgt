# Route N C5-C11 (2026-08-10)

Route N endpoint-doublet research produced exact no-gos and positive survivors.

## No-gos
- C5: fixed theta source fibres do not support bounded nonzero translations in either direction; moving fibres make translation isometric but absorb detector.
- C6: for every prime aperture, even theta endpoint is outside canonical H_k. Thus ordinary canonical Hilbert landing fails.
- Existing full Schwartz ordinary-L2 Hilbert-Gram route is nonclosable; singular boundary/base-change is required.

## Positive survivors
- C7: moving-horizon endpoint energy at L=log p is exactly 2/p*(k(0)^2+k(log p)^2).
- C8: residual sum_p 2/p*k(log p)^2 is summable. All non-Hilbert mass/radial selectivity is universal boundary atom k(0)/sqrt(p).
- C9: Gamma-sewn soft source has grade mass 1/(p log p); forced Fisher factor sqrt(log p) gives Hedenmalm half-density 1/sqrt(p). Positive damping u gives p^(-(1+u)/2).
- C10: damped marked source energy at z is p^(-1-u+Im z)+p^(-1-u-Im z), summable iff |Im z|<u.
- C11: at nonzero grade t and critical damping u=|t|, Route N energy is p^-1+p^(-1-2|t|). The correction is ell1. Route R signed Gamma-Bockstein wall equals -sign(t)*p^-1 modulo ell1. Hence Route N and Route R are two polarizations of one prime-harmonic essential boundary class.

## Lean
Direct `lake env lean <file>` passed for all modules through C11:
- `formal/GaloisForLFunctions/RHTower/HedenmalmThetaTranslationWeightNoGo.lean`
- `formal/GaloisForLFunctions/RHTower/HedenmalmThetaEndpointSourceDomainNoGo.lean`
- `formal/GaloisForLFunctions/RHTower/HedenmalmThetaMovingHorizonBoundary.lean`
- `formal/GaloisForLFunctions/RHTower/HedenmalmGammaSewnFisherHalfDensityBridge.lean`
- `formal/GaloisForLFunctions/RHTower/HedenmalmGammaSewnRouteRCriticalWallBridge.lean`
Umbrella import added to `formal/GaloisForLFunctions/RHTower.lean`.

## Open core
Construct an unconditional singular source-pinned base change before divisor/zero specialization, carrying every Xi root conormal into every positive-damping Gamma-sewn marked fibre. This must produce Ward Hardy saturation, not merely re-express the existing RH-equivalent receiver. Do not return to bounded fixed-fibre translation, canonical H_k landing, or ordinary Hilbert-Gram completion; these are closed no-gos.

Paper card: `docs/drafts/pipeline/1-in-progress/hedenmalm-prime-normal-jordan-grade-separation.md`.
Frontier map: `docs/drafts/pipeline/1-in-progress/rh-current-frontier-map.md`.
Status: NOT RH.