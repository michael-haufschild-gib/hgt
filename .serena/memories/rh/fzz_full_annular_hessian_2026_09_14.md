# FZZ full depth-one annular Hessian

- Chain: neutral source → mixed Ward orientation → balanced-Gamma saturation → passivity → RH.
- Module: `FZZCigarParityTwoMarkedFullAnnularHessianNoGo.lean`.
- Exact response: `C(k)(L+μ(-exp u))+k²V(-exp u)`, contact plus connected tilted radial fluctuation.
- `C(k)<0`; response is surjective in geometry `L`, has one unique zero, and both signs at every physical level.
- Kill: depth-one annular factor cannot provide geometry-independent universal Ward orientation.
- Survivor: complete infinite neutral screening sum must source-fix geometry/phase/cross-depth correlations; full FZZ-P remains live.
- Audit: direct Lean PASS; targeted leaf build PASS; axioms standard only; lint PASS.