# Degree-six endpoint: the fixed-reader comparison IS RH (2026-08-07)

The requested closing step `R_phys(B_6) = tau_6(B_6)` (with `tau_6(B_6) = 0`) unfolds, using only the
corpus's own definitions, to `Re rho = 1/2`. Verified in situ:

- `deningerHalfDensityMateGain n s = exp((2*s.re - 1) * log n)` — positive, depends on `Re s` ONLY
  (`DeningerOneSidedFramedMateCurvatureTransgression.lean:134`).
- `deningerOrdinaryIntegerBVGreenStokesBoundaryEvaluation n s = n⁻¹ * (1 - gain⁻¹)`
  (`DeningerOrdinaryIntegerBVGreenStokesRadialComparison.lean:213`); reflection `s ↦ 1 - s̄` inverts
  the gain.
- Hence `routeRDeningerBVGreenReflectedBoundary rho = 2 * sinh((2*Re rho - 1) * log 6)`.

## Why no source theorem can close it

1. The operator side is `rho`-free: `B_6` fixed, `tau_6(B_6) = 0`, and EVERY pair-cyclic reader gives
   0. The physical side is odd and strictly increasing in `Re rho - 1/2`. Equating them at `rho` is
   literally the critical-line statement at `rho`; there is no residual comparison content.
2. Any law implying the comparison at all zeros implies RH ⇒ it cannot be "strictly weaker".
3. The real residue is a SIGN: the zero set is stable under `rho ↦ 1 - rho̅` and
   `R_phys(1 - rho̅) = -R_phys(rho)` unconditionally, so `R_phys ≡ 0` on zeros ⟺ `R_phys ≥ 0` on
   zeros. Any manifestly nonnegative representation of `R_phys(B_6)` contradicts antisymmetry unless
   the value is 0 — which is exactly why every positive-unit representation in this lane transports
   the sign rather than removing it. Same wall as `mem:five-lanes-one-wall`.

Conclusion: the degree-six endpoint needs an analytic one-sided input on the divisor side
(`Re rho ≤ 1/2` for Xi-zeros), not a Hochschild/cyclic/trace/gauge statement about `B_6`. Recorded on
`docs/drafts/pipeline/1-in-progress/route-r-degree-six-bv-green-physical-cyclic-producer.md`.
