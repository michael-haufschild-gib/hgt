# Prime/Gamma Stokes-wall Xi tau cold-boundary no-go (2026-08-25)

Formalized unconditional atTop no-go in `formal/GaloisForLFunctions/RHTower/RoutePPrimitiveGammaJuliaStokesPrimeGammaWallXiTauColdBoundaryNoGo.lean`.

- Prime-2 is unique cold Gibbs ground label; Tannery gives normalized prime-2 wall mass tending to 1.
- Exact cubic coherence expectation `E(d)` satisfies `w_d(2)^2 ≤ E(d) ≤ 1`, hence `E(d) → 1`.
- Exact Fredholm coefficients for every `d>0`: `a₁(d)=1`, `a₂(d)=(1-E(d))/2`.
- Thus projective log two-jet is `E(d)/2 → 1/2`.
- Final theorem `eventually_not_routePPrimitiveGammaJuliaStokesPrimeGammaWallXiTauScalarRescalingAt_atTop` excludes all sufficiently large apertures after arbitrary complex scalar time rescaling, using Xi's unconditional `<9/80` bound.
- Combined with `mem:route-p/prime-gamma-wall-xi-tau-boundary-neighborhood-no-go-2026-08-25`, any scalar-rescaled match is confined to a bounded intermediate aperture window.

Verification: targeted `lake env lean` passed; all 13 new public declarations depend only on `propext`, `Classical.choice`, `Quot.sound`; `git diff --check` passed. Lint remains red only on unrelated umbrella reachability for `SuzukiShiftedXiBoundaryFactorization` and `SecondOrderConstraintDescent`.

Wired into `formal/GaloisForLFunctions/RHTower.lean`; card promoted to `docs/drafts/pipeline/3-formalized/route-p-prime-gamma-wall-xi-tau-cold-boundary-no-go.md`. Frontier map remained read-only. Temporary `.olean` and scratch files removed.

Surviving open core: bounded intermediate-aperture regime; existing one-parameter Stokes channel fails at both endpoint regimes. Any RH-producing repair must provide new even Stokes/monodromy data or a source-native global intermediate-aperture exclusion/identification.