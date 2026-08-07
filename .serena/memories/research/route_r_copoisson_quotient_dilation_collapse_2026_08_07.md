# Route R bilateral co-Poisson quotient dilation collapse (2026-08-07)

## Conjecture loop
- C6 full-jet obstruction: failed; live theorem only needs top conormal quotient.
- C7 aperture defect as ordinary boundary: falsified by principal/noncompact aperture no-go.
- C8 extended trace normalization: already corpus-known; trace-level only.
- C9 leakage Gram/Douglas factorization: already corpus-known.
- C10 bilateral literal co-Poisson source covariance: survived and is Lean-proved in `RHTower/BurnolCoPoissonSourceDilation.lean`.
- C11 Hilbert-adjoint quotient collapse: survived and is Lean-proved in `RHTower/BurnolCoPoissonQuotientDilationCollapse.lean`.

## Exact result
For r >= 1, both U_r and U_r^* send C_b into C_(b/r). Hence by adjunction both send C_(b/r)^perp back into C_b^perp. Therefore for y in Y_(b/r)=L_(b/r) cap C_(b/r)^perp:
- E_b(U_r y)=P_b(U_r y)
- E_b(U_r^* y)=P_b(U_r^* y)
where E_b is the co-Poisson quotient projection and P_b is plain extended-Sonin projection.

Route R corollaries:
- `coPoissonQuotientForward_eq_soninProjection_of_mem_next`
- `coPoissonQuotientInverse_eq_soninProjection_of_mem_next`

This removes the co-Poisson source-projection term from both physical Gamma orientations. Remaining dagger/Bockstein landing is a pure Sonin aperture-leakage problem.

## Verification
- `lake env lean GaloisForLFunctions/RHTower/BurnolCoPoissonQuotientDilationCollapse.lean`: pass.
- `lake build GaloisForLFunctions.RHTower.BurnolCoPoissonQuotientDilationCollapse`: pass.
- Axioms: `[propext, Classical.choice, Quot.sound]`.
- Both modules wired into `GaloisForLFunctions/RHTower.lean`.
- Full lint found only unrelated concurrent unreachable modules: EulerActivationOccupancyPhaseTransition, GammaCoPoissonSoninQuadrantFlatness, PrimeValuationInfiniteSupport, ProductOccupancyDichotomy. Neither new module was unreachable or contained forbidden declarations.

## Open core after reduction
Construct source-normal exact-couple morphism from first-trace edge to the pure Sonin aperture-leakage Bockstein, identify its Bockstein with full Xi top conormal, and prove inverse/dagger equality on that same relative class. Burnol completeness remains separately needed for full operator flatness, not for the projection collapse.