# CCM oriented wall-light incidence (2026-08-21)

New verified modules:
- formal/GaloisForLFunctions/RHTower/CCMActualHeadMatchedOrientedCharacteristicCocycle.lean
- formal/GaloisForLFunctions/RHTower/CCMActualHeadMatchedOrientedWallLightIncidence.lean

Core formal knowledge:
1. Matched prime-polar residual is real part of exact Hermitian complex characteristic cocycle. Odd radial phase has strictly positive first jet at every Suzuki prime-power wall.
2. For n=p^(e+1), literal Suzuki diagonal light imbalance satisfies
   ||ell_+(2*pi*xi)||^2 - ||ell_-(2*pi*xi)||^2
   = criticalMellinAtomWeight n * sin(2*pi*log(n)*xi).
3. Critical-weighted actual matched CCM cell has exact division-free spectral incidence normal form; arbitrary finite prime-power packets assemble.
4. Exact survivor:
   ||ell_-||^2 = (critical mass - light imbalance)/2.
5. Center no-go: matched incidence symbol is zero at xi=0, but negative-light energy is strictly positive (half critical mass). Thus oriented incidence alone cannot pointwise dominate raw negative light.

Higher principle:
Negative light has two irreducible source coordinates: scalar center reserve and oriented imbalance. Any Robin/Gamma/holonomy completion must source both. Scalar/even routes erase orientation; oriented-only routes miss center reserve. Seek coefficient-faithful two-channel Schur/trace transport.

Verification:
- direct leaf checks passed
- exact module builds passed
- axiom audits only propext, Classical.choice, Quot.sound
- wired into RHTower umbrella; umbrella not built
- formal lint failed only on four unrelated pre-existing/unowned HTGeometry umbrella reachability errors.

Do not edit docs/drafts/pipeline/1-in-progress/rh-current-frontier-map.md.
Next target: transport finite CCM wall-light incidence plus scalar center reserve into actual Robin-Gamma-holonomy rectangular trace; then lower-semi-bounded Schur residual.