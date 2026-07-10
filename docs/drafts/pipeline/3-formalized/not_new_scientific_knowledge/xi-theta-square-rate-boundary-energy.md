# Exact boundary energy of the infinite square-rate reader symbol

- **ID:** xi-theta-square-rate-boundary-energy
- **Stage:** 3-formalized
- **Type:** BRIDGE THEOREM (Lean), [PROVED]
- **Date:** 2026-07-10
- **Module:** GaloisForLFunctions.RHTower.XiThetaSquareRateBoundary
- **Paper proof:** ../../2-fully-proven/new/xi-theta-square-rate-boundary-energy.md

## Formal surface

- `norm_thetaSquareBlaschkeSymbol_mul_I`: unit norm of the canonical quotient on the punctured
  imaginary boundary.
- `norm_thetaSquareBlaschkeNodeSlope`: exact node-slope norm `pi/(2 n sinh(pi n))`.
- `norm_thetaSquareBlaschkeReaderSymbol_mul_I`: exact dimensionless Cauchy boundary profile.
- `integral_sq_norm_thetaSquareBlaschkeReaderSymbol_boundary`: squared dimensionless boundary norm
  `(4/pi) sinh(pi n)^2`.
- `integral_sq_norm_thetaHeatRateReaderSymbol_boundary`: physical boundary energy
  `4 sinh(pi n)^2`.
- `normalized_boundary_energy_thetaHeatRateReaderSymbol`: standard half-plane normalized energy
  `(2/pi) sinh(pi n)^2`.

## Certificate

- Direct source check passed.
- Targeted build passed: `lake build GaloisForLFunctions.RHTower.XiThetaSquareRateBoundary`
  (8602 jobs).
- Axiom audit passed for the boundary inner identity, exact node-slope norm, Cauchy profile, and
  both boundary-energy theorems; only `propext`, `Classical.choice`, and `Quot.sound` occur.
- Generated theorem API refreshed; formal lint passed.
- No full or umbrella build.
- No sorry, admit, axiom, opaque, or unsafe declaration.

## Scope

The module proves exact boundary data. It does not encode a half-plane Hardy space, prove the
uniform interior-line supremum, or construct the inverse Paley-Wiener L2 representative.
