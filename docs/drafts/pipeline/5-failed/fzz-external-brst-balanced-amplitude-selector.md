# FZZ external-BRST balanced amplitude selector

- **ID:** FZZ-BRST-BALANCED-AMPLITUDE-SELECTOR
- **Stage:** 5-failed
- **Killed by:** `RHTower.fzzHJBalancedExternalGammaAmplitudeRouteKilled`

## No-go

At `k=4`, complete balanced opposite-winding external Gamma amplitude returns exactly to wall
value `1` at arbitrarily large nonzero radial momentum. Wall point is passive; every nonzero
recurrent point is nonpassive. No predicate of pointwise complex amplitude can characterize
replica-area passivity.

## Positive survivor

Amplitude value forgets winding number of continuous phase lift. Surviving FZZ-P mechanisms must
retain unwrapped phase/Wigner--Smith history or use higher-point integrated Ward coupling.

Paper proof and Lean status: dependency-closed and formalized in
`FZZCigarParityExternalBRSTBalancedGammaPhaseRecurrenceNoGo.lean`.
