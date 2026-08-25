# Prime/Gamma wall Xi tau boundary-neighborhood no-go (2026-08-25)

## Result
Formalized a source-native finite-aperture irregular-RH obstruction:
`RHTower.eventually_not_routePPrimitiveGammaJuliaStokesPrimeGammaWallXiTauScalarRescalingAt`.

It proves
`∀ᶠ d : ℝ in 𝓝[>] 0, ¬ ∃ c : ℂ, canonicalXiSeamLog =ᶠ[𝓝 0] fun z ↦ Complex.log (D_d(c*z))`,
where `D_d` is the canonical Fredholm determinant of the actual discrete prime/Gamma Stokes-wall law at aperture `d`.

## Mechanism
Let `a_n(d)` be wall Fredholm coefficients and
`P(d)=(a₁(d)^2-2a₂(d))/(2a₁(d)^2)`.
Existing coefficient convergence and endpoint values `a₁(0)=1`, `a₂(0)=19/70` give
`P(d) → 8/35` as `d→0+`, hence eventually `Re P(d)>9/80`.
For arbitrary scalar `c`, the log jets are
`L₁=c a₁(d)`, `L₂=c²(2a₂(d)-a₁(d)²)`; if germ equality with Xi holds, Xi's positive first jet makes `c a₁(d)≠0`, so projectivization cancels `c`.
Xi's exact invariant is `m₁/m₀²<9/80`, contradiction.

Positive survivor: finite-aperture discretization cannot repair endpoint mismatch; viable irregular-RH bridge must add a new even Stokes/monodromy channel or leave this wild-wall neighborhood.

## Files
- `formal/GaloisForLFunctions/RHTower/RoutePPrimitiveGammaJuliaStokesPrimeGammaWallXiTauBoundaryNoGo.lean`
- import appended to `formal/GaloisForLFunctions/RHTower.lean`
- Stage-3 card: `docs/drafts/pipeline/3-formalized/route-p-prime-gamma-wall-xi-tau-boundary-neighborhood-no-go.md`
- Frontier map remained read-only.

## Verification
- Targeted `lake env lean GaloisForLFunctions/RHTower/RoutePPrimitiveGammaJuliaStokesPrimeGammaWallXiTauBoundaryNoGo.lean`: pass.
- `#print axioms` for all 11 new theorem declarations: only `propext`, `Classical.choice`, `Quot.sound`.
- `scripts/formal_tools.py lint`: new module accepted/reachable; global exit 1 only for unrelated umbrella reachability of `SmoothAFEZetaDisplacedDeepCoefficientIdentification`, `SuzukiShiftedXiBoundaryFactorization`, `SecondOrderConstraintDescent`.
- `git diff --check`: pass.
- Temporary scratch files and copied prerequisite/new oleans removed; no Lean process remained.

External literature audit: Bertola arXiv:0902.4716, Its–Lisovyy–Prokhorov arXiv:1604.03082, Desiraju arXiv:2008.01142, Yafaev arXiv:1511.04683. Exact source-specific obstruction not found; novelty label remains candidate, not priority claim.