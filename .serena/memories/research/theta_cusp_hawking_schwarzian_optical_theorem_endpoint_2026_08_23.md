# Theta-cusp Hawking Schwarzian optical theorem endpoint (2026-08-23)

Added `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingSchwarzianOpticalTheoremEndpoint.lean` and umbrella import in `formal/GaloisForLFunctions/RHTower.lean`.

## Closed theorem
For theta mirror source `k = thetaCuspFullSource`:
- `Fourier(k'')(w/(2*pi)) = -w^2 XiC(w)`.
- Standard normalized right-moving Born energy shell from `K(u,v)=2 i u v XiC(u+v)` is exactly
  `w^4 Xi(w)^2/(48*pi^2)`.
- Plancherel and evenness give
  `integral_(0,infty) w^4 Xi(w)^2 dw = pi * integral_R |k''(x)|^2 dx`.
- Hence total normalized Born pair energy equals quadratic Davies--Fulling Schwarzian backreaction energy:
  `thetaCuspHawkingBornRightQuadraticEnergy = thetaCuspHawkingSchwarzianQuadraticEnergy`.

This is coefficient-exact and uses the actual theta source; no RH or passivity assumption.

## Scientific status
- [LITERATURE] moving-mirror Schwarzian/Bogoliubov energy equality and Butera pair-emission backreaction.
- [BRIDGE] theta specialization.
- [PAPER-PROVED] [LEAN-PROVED] exact optical theorem.
- [FALSIFIED] real-frequency energy identity as RH producer: both sides see only `Xi(w)^2`, invariant under all-pass phase.
- [OPEN CORE] derive phase-sensitive complex-frequency local optical theorem identifying causal Hawking channel with anomaly boundary term `C*B + B†*C`, or prove cancellation from source law.

## Verification
Direct `lake env lean GaloisForLFunctions/RHTower/ThetaCuspHawkingSchwarzianOpticalTheoremEndpoint.lean` passed. Forbidden declaration scan clean. Key theorem axioms only `[propext, Classical.choice, Quot.sound]`.
