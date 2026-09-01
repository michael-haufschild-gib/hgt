# Finite half-density tensor-power radial no-go

Module: `GaloisForLFunctions.RHTower.SourceGammaFiniteHalfDensityTensorPowerRadialNoGo`.

Facts:
- Degree-`n` literal physical half-density prime-two/three norm ratio is `(3/2)^(n*t/2)`, `t=2 Re(rho)-1`.
- Two-prime Gamma Ward compatibility is exactly `n=4 ∨ Re(rho)=1/2`.
- For `n≠4`, universal actual-Xi compatibility is equivalent to RH, so only a wall receiver.
- Degree `4` has exact Ward exponent and admits fitted ghosts at every Xi divisor unconditionally, so exact radial matching is nonselective.
- Closed theorem: `sharedWardFiniteHalfDensityTensorPowerRadialGhostRouteKilled`.
- Survivor: source-natural phase/sign/cohomological compatibility beyond radial norm.

Audit: direct Lean and targeted module build pass; umbrella wired; axioms only `propext`, `Classical.choice`, `Quot.sound`. Card: `docs/drafts/pipeline/3-formalized/source-gamma-finite-half-density-tensor-power-radial-no-go.md`.