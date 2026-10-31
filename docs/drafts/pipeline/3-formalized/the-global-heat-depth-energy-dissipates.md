# Global squared-depth dissipation for the actual heat divisor

- **Stage:** 3-formalized
- **Type:** Unconditional theorem
- **Source:** `docs/reports/review-3010/obstacles-summary.md` Q3/functional.
- **Statement:** For `t>0`, the sum of squared imaginary parts of all nonreal heat
  zeros, with multiplicity, is finite and obeys
  `E(b)+2∫_a^b N(t)dt≤E(a)` for `0<a≤b`.

## Proof

For a finite simple conjugation-invariant packet with velocity
`z_i'=2Σ_{j≠i}(z_i−z_j)⁻¹`, symmetrization gives
`E'=-4Σ_{i<j}(Im z_i−Im z_j)²/|z_i−z_j|²≤-2N`.
Every conjugate pair contributes exactly four. The full canonical product
shows that real exterior zeros contribute nonpositive imaginary work.

On each compact positive-time interval, one fixed ball contains every nonreal
zero. Forward simplicity in this ball identifies `E'` with the finite sum of
actual zero velocities. The count is antitone and constant on short punctured
forward intervals. Hence `E(t)+2∫_a^t N(s)ds` has nonpositive derivative on
those intervals; its continuity extends comparison across every collision.

## Canonical-product input

`RHTower.logDeriv_eq_tsum_of_even` supplies the absolutely convergent
renormalized field `Σ(1/(z−a)+1/a)` for every even entire function with the
proved order-one envelope. Apply it to `riemannHeat t`. The finite nonreal
copy set is closed under `a↦−a`, so its counterterms sum to zero. Each real
exterior copy contributes imaginary part `−Im z/|z−a|²`. Thus the exterior
work has the required sign before taking the regular part at a simple zero.

## Lean declarations

Owner: `ArithmeticElectrostatics`.

- `TheRealExteriorDissipatesHeatDepth`: `riemannHeat_realExteriorWork_nonpos`.
- `TheGlobalHeatDepthIsContinuous`: `continuousOn_heatGlobalVerticalEnergy`.
- `SimpleHeatZeroBranches`: `exists_simple_heat_zero_branch`.
- `TheSimpleHeatPacketDissipatesDepth`: `heatGlobalPacket_drift_le`.
- `TheGlobalHeatDepthHasItsZeroVelocityDerivative`:
  `heatGlobalVerticalEnergy_hasDerivWithinAt_of_simple`.
- `TheGlobalHeatDepthDissipates`:
  `heatGlobalVerticalEnergy_add_integral_count_le`,
  `antitoneOn_heatGlobalVerticalEnergy`,
  `heatGlobalVerticalEnergy_eq_zero_iff`.

All six leaves passed direct `lake --old env lean` checks. Endpoint transitive
axiom closures contain only `propext`, `Classical.choice`, `Quot.sound`.
Umbrella imports are present. The energy vanishes exactly when every heat
zero is real.

## Scope

Finiteness of the unheated squared-depth series is separate and unproved.
No continuous extension of the positive-time functional to zero is asserted.
Positive-time dissipation alone does not bound growth as `t↓0`.
