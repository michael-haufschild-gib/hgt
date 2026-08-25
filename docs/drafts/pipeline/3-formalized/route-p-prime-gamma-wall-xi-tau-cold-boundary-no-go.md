# Prime/Gamma Stokes-wall Xi tau cold-boundary no-go

- **ID:** route-p-prime-gamma-wall-xi-tau-cold-boundary-no-go
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Labels:** `[LEAN-PROVED]` `[CANDIDATE NEW SCIENTIFIC KNOWLEDGE]` `[IRREGULAR-RH]` `[SOURCE-NATIVE]` `[NO-GO]`
- **Source:** exact positive-aperture prime/Gamma Stokes wall and its prime-log Gibbs weights
- **Statement:** For all sufficiently large positive apertures, no complex scalar rescaling of the canonical prime/Gamma Stokes-wall Fredholm determinant has logarithmic germ equal to `canonicalXiSeamLog`.

## Goal

Close the cold end of the actual finite-aperture irregular-RH family. Combined with the formalized wild-wall boundary no-go, this confines any remaining scalar-rescaled match to a bounded intermediate aperture window.

## Gates

- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: Lean theorem, targeted `lake env lean` green, new declarations axiom-audited
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Exact conjecture

With `D_d`, `X`, and the scalar-rescaling predicate from the boundary-neighborhood card,

`∀ᶠ d : ℝ in atTop, ¬ ∃ c : ℂ, X =ᶠ[𝓝 0] fun z ↦ Complex.log (D_d(cz))`.

## Frontier audit

- Existing corpus proves the right-wall limit `d→0+`, but no large-aperture limit for this wall law, its Fredholm coefficients, or its projective two-jet.
- `LowTemperatureCurvature.lean` supplies a general countable Gibbs ground-state selection mechanism; `EulerNormalizedTraceHankelFarRight.lean` supplies an analogous first-frequency Dirichlet extraction, but neither is applied to this Stokes wall.
- Exact literature searches found no prime/Gamma wall, `8/35`, `1/2`, or Xi germ exclusion of this form. General Stokes/tau and Hankel literature does not contain this arithmetic cold-boundary statement. This is an audit result, not a priority claim.

## Hostile audit

- **Rejected shortcut:** global monotonicity of wall coherence in aperture is neither in corpus nor justified; exponential tilting need not make a general pair kernel monotone.
- **Circularity:** none; cold concentration uses only positive prime weights and unique lowest prime `2`.
- **Infinite-tail loophole:** freeze the positive tail at one fixed aperture to obtain a summable Tannery majorant.
- **Normalization loophole:** normalized prime-2 mass is a ratio whose denominator has the same nonzero ground-state limit.
- **Scalar loophole:** projective logarithmic two-jet cancels arbitrary aperture-dependent complex time rescaling.
- **Verdict:** `SURVIVES PRELIMINARY ATTACK`.

## Approach

For `d>0`, wall weights are proportional to

`b_d(p)=log(p) p^{-(1+2d)}`.

After factoring the prime-2 Boltzmann scale, dominated convergence gives

`Σ_p b_d(p)/b_d(2) → 1`, hence normalized prime-2 mass `w_d(2)→1`.

For the normalized wall law, the order-one Fredholm coefficient is `a₁(d)=1`; the order-two determinant expansion gives

`a₂(d)=(1-E(d))/2`,

where `E(d)` is the exact cubic Stokes-coherence expectation. Therefore the projective logarithmic two-jet is `P(d)=E(d)/2`. Since `0≤E(d)≤1` and its diagonal prime-2 contribution is `w_d(2)^2`, squeeze gives `E(d)→1`, hence `P(d)→1/2`.

Because Xi's projective invariant is below `9/80<1/2`, the same germ argument as at the wild boundary excludes all sufficiently large apertures.

## Dependency-closed paper proof

For `d>0`, canceling the common factor `8d` in the transported current shows that the normalized wall mass at prime `p` is

`w_d(p)=b_d(p)/Z_d`, where `b_d(p)=log(p)p^{-(1+2d)}` and `Z_d=Σ_q b_d(q)`.

Let `r_d(p)=b_d(p)/b_d(2)`. Then `r_d(2)=1`. For every `p≠2`, primality gives `p≥3`, hence `0<2/p<1` and `r_d(p)→0` as `d→∞`. On `d≥1`, `0≤r_d(p)≤r_1(p)`. The series `Σ_p r_1(p)` is summable because it is a positive constant multiple of the already-summable prime weight `log(p)p^{-3}`. Tannery's theorem therefore gives

`Z_d/b_d(2)=Σ_p r_d(p)→1`.

The denominator is positive, so `w_d(2)=1/(Z_d/b_d(2))→1`.

Let `E(d)` be the normalized cubic Stokes-coherence expectation. Its atomic expansion has nonnegative summands bounded above by the product weights. Since the coherence kernel equals one on the diagonal,

`w_d(2)^2 ≤ E(d) ≤ (Σ_p w_d(p))^2=1`.

Thus `E(d)→1` by squeeze.

For the corresponding Fredholm determinant, probability normalization and unit kernel diagonal give `a₁(d)=1`. Expanding the `2×2` determinant and using kernel symmetry gives

`2a₂(d)=1-E(d)`.

Therefore

`P(d)=-(2a₂(d)-a₁(d)^2)/(2a₁(d)^2)=E(d)/2→1/2`.

Eventually `Re(P(d))>9/80`. If a scalar-rescaled wall tau logarithm had Xi germ, equality of first jets would force the scalar and `a₁(d)` nonzero, projectivization would identify `P(d)` with Xi's `m₁/m₀²`, and the unconditional bound `m₁/m₀²<9/80` would contradict the eventual wall inequality. ∎

## No-go closure

- **Exact killing theorem/mechanism:** unique prime-2 cold ground state forces Stokes coherence to one and projective tau curvature to one half.
- **Strongest positive survivor:** scalar-rescaled matches, if any, are confined away from both the wild wall and cold boundary to a bounded intermediate aperture regime.
- **New insight:** existing one-parameter prime/Gamma Stokes channel has incompatible Xi projective geometry at both ends; any repair must change even Stokes data, not select an extreme aperture.
- **Status:** formalized as `eventually_not_routePPrimitiveGammaJuliaStokesPrimeGammaWallXiTauScalarRescalingAt_atTop` in `RoutePPrimitiveGammaJuliaStokesPrimeGammaWallXiTauColdBoundaryNoGo.lean`. Targeted Lean check passed. All thirteen new public declarations use only `propext`, `Classical.choice`, and `Quot.sound`.

## Log

- 2026-08-25 — created in 1-in-progress after rejecting unsupported global monotonicity route.
- 2026-08-25 — promoted to 2-fully-proven after dependency-closed prime-2 Tannery proof.
- 2026-08-25 — promoted to 3-formalized after targeted Lean verification and new-declaration axiom audit.
