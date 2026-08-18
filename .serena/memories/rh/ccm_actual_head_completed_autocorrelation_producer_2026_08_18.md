# Route O / CCM actual-head completed autocorrelation producer (2026-08-18)

Created `formal/GaloisForLFunctions/RHTower/CCMActualHeadCompletedAutocorrelationProducer.lean`, wired after `CCMActualHeadGammaWallOutgoingProducer` in `RHTower.lean`.

## Exact new identities

For `C_f(h)=Re(<U_h f,f>+<U_-h f,f>)/2`, Lean proves `E_f(h)=2||f||^2-2C_f(h)`.

Completed-error quadrature collapses exactly to

`2 int_[0,2a] 2cosh(h/2) C_f(h) dh - 2 sum_{n<=e^(2a)} Lambda(n)/sqrt(n) C_f(log n)`.

All completed endpoint, cumulative prime mass, and scalar polar mass cancel. No derivative or BV regularity of the L2 head autocorrelation is used.

After prior first-Gamma-mode cancellation, outgoing boundary current is

`4||f||^2 + 2 int_[0,2a] exp(h/2) C_f(h) dh - 2 sum Lambda(n)/sqrt(n) C_f(log n)`.

Full producer is

`2 gamma0 ||f||^2 + GammaHigher(f) + outgoingBoundaryCurrent(a,f)`.

Lean proves it equals prior outgoing producer and restricted-Weil source quadratic. On canonical finite heads it equals `epsilon_a ||v_(a,n)||^2 + headTailDefect`, and its nonnegativity iff literal reverse-prime bound.

## Killed conjecture

Do not use ground modulus or `C_f>=0`: `SuzukiScrewDisjointCrossCoupling.lean` proves failure of first Beurling-Deny criterion for all scalar shifts at large aperture. Full restricted form is not positivity preserving.

Do not split higher-Gamma energy into norm and autocorrelation integrals: Gamma density is singular at zero, so separate pieces diverge; only defect form is lawful.

## Verification

- `lake env lean GaloisForLFunctions/RHTower/CCMActualHeadCompletedAutocorrelationProducer.lean` passed.
- targeted `lake build GaloisForLFunctions.RHTower.CCMActualHeadCompletedAutocorrelationProducer` passed; one new leaf built.
- key theorem axiom audit: only `propext`, `Classical.choice`, `Quot.sound`.
- `scripts/formal_tools.py lint --check-generated` found only pre-existing unrelated unreachable HTGeometry modules.
- formal API/gap/overview and search index regenerated.

## Remaining hard core

Sign the boundary-current producer cofinally on canonical Gamma-Slepian heads while keeping nonnegative vanishing head defect. Exact object is no longer a bulk defect comparison but a signed boundary-transfer current. Route map remained read-only.