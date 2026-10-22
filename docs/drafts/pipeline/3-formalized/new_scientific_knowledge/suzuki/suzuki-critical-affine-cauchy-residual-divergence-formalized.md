# Suzuki critical affine-Cauchy residual divergence — formalization certificate

## Status

`[LEAN-PROVED] [UNCONDITIONAL] [SOURCE-PURE] [NO RH PREMISE] [NOVELTY UNVERIFIED]`

## Paper source

`./suzuki-critical-affine-cauchy-residual-divergence.md`

## Lean source

`formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiCriticalAffineCauchyResidualDivergence.lean`

## Formal theorem surface

- `suzukiCriticalAffineCauchyResidual_eq_twoBoundary`: exact connector to corpus affine
  two-boundary residual at `a=1/2`, `w=0`, `lambda=log p`.
- `scaled_primeHarmonic_le_suzukiCriticalAffineCauchyResidualMass`: global lower comparison
  `1/(6400000*p)`.
- `not_summable_suzukiCriticalAffineCauchyResidualMass`: canonical critical repair diverges.

## Scientific result

Midpoint Lorentz numerator and affine Cauchy residual numerator coincide, but corresponding
triple-log cancellation cannot repair critical rooted Hilbert topology.  Required mechanism must
change prime power scale.  Positive survivor is critical aperture quarter-shift current.

RH is not claimed proved.

## Verification

- Direct Lean check passed.
- Axiom audit: only `propext`, `Classical.choice`, and `Quot.sound`; no project axiom or RH premise.
- Forbidden-token scan: clean.
- Final targeted build passed:
  `lake build GaloisForLFunctions.RHTower.RiemannHypothesisSOTA2026` (`9450/9450`).
- Repository lint reached module but remains red on six unrelated concurrent unreachable modules.
