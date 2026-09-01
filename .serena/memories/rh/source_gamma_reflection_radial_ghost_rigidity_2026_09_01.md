# Source/Gamma reflection-radial kill

Formal module: `GaloisForLFunctions.RHTower.SourceGammaReflectionRadialGhostRigidity`.

Facts:
- Two-prime Gamma Ward forces `‖u₂‖/‖u₃‖=(3/2)^(2t)`.
- Any FE-even radial ratio at `t,-t` forces `t=0`; exact Fisher-frame distortion is even, hence killed.
- Actual physical half-density ratio is `(3/2)^(t/2)` and reflection-reciprocal; compatibility with Ward forces `t=0` by strict monotonicity.
- Universal actual-Xi versions are equivalent to RH; physical version is also equivalent to `SharedFourRouteWardEndpoint`.
- Closed theorem: `sharedWardReflectionRadialGammaGhostRouteKilled`.
- Survivor: source-derived reflection-reciprocal radial law with exact exponent `2t`.

Audit: direct Lean and targeted module build pass; umbrella wired; axioms only `propext`, `Classical.choice`, `Quot.sound`. Card: `docs/drafts/pipeline/3-formalized/source-gamma-reflection-radial-ghost-rigidity.md`.