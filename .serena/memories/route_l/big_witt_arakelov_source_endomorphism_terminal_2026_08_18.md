# Big-Witt / Arakelov source-endomorphism terminal (2026-08-18)

## Outcome
Route exhausted within Big-Witt / Scaling-Site / completed-Xi source architecture; no RH proof.

## New formal module
`formal/GaloisForLFunctions/RHTower/BigWittArakelovSourceEndomorphismTerminal.lean`, wired into `RHTower.lean`.

## Exact results
- `deningerBigWittFrobeniusTwoRingHom_arakelovBigWittReporter`: positive survivor `F₂(T(w rho)) = T(w(P₂ rho))`.
- `arakelovPowerLift_two_eq_self_iff`: fixed points of `P₂` are exactly `rho=0` or `rho=1`.
- `ccmZetaCircleCover_not_arakelovPowerLift_two`: actual zeta-circle cover fixes critical point and cannot induce `P₂`.
- `arakelovPowerLift_two_eq_rational`: `P₂ rho = rho² (2 rho - 1)⁻¹`.
- `not_continuousAt_arakelovPowerLift_two`, `not_differentiable_arakelovPowerLift_two`: critical-line pole at `1/2`.
- `DeningerEntireArakelovSquarePullbackExists`: precise requested global entire-source endomorphism property.
- `not_deningerEntireArakelovSquarePullbackExists`: impossible; coordinate image would make `P₂` entire.
- `bigWittArakelovCompletedXi_source_endomorphism_terminal`: bundles reporter law, global source no-go, cover incompatibility, actual Euler jet dilation, scaled target ideal, and RH equivalences for right stability/preperiodicity.

## Literature boundary
- Connes–Consani 2026 arithmetic Jacobian uses idele-class translations and trace formula, not a global Frobenius endomorphism on Xi cohomology.
- Scaling-Site cover preserves centered label.
- Zeta Spectral Triples still requires unproved spectral convergence to zeros.

## Verification
- `lake env lean GaloisForLFunctions/RHTower/BigWittArakelovSourceEndomorphismTerminal.lean`: PASS.
- `lake build GaloisForLFunctions.RHTower.BigWittArakelovSourceEndomorphismTerminal`: PASS.
- Axioms: `[propext, Classical.choice, Quot.sound]`.
- New file has no `sorry`, `admit`, `axiom`, `opaque`, or `unsafe`.
- Repository-wide lint still fails only on unrelated unreachable modules; new module is reachable from RHTower umbrella.
