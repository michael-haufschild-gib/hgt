# Prime/Gamma Stokes-wall Xi tau boundary-neighborhood no-go

- **ID:** route-p-prime-gamma-wall-xi-tau-boundary-neighborhood-no-go
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Labels:** `[LEAN-PROVED]` `[CANDIDATE NEW SCIENTIFIC KNOWLEDGE]` `[IRREGULAR-RH]` `[SOURCE-NATIVE]` `[NO-GO]`
- **Source:** exact prime/Gamma Stokes wall family already formalized in Route P
- **Statement:** On a punctured right neighborhood of zero aperture, no complex scalar rescaling of the canonical prime/Gamma Stokes-wall Fredholm determinant has logarithmic germ equal to `canonicalXiSeamLog`.

## Goal

Use actual finite-aperture prime/Gamma Stokes data, rather than endpoint exponential-law foundations, to test the remaining Xi divisor bridge. The claim is unconditional and source-pure: aperture is the existing Stokes deformation, while arbitrary complex time rescaling is universally quantified away.

## Gates

- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: Lean theorem, targeted `lake env lean` green, new declarations axiom-audited
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Exact conjecture

Let `μ_d` be `routePPrimitiveGammaJuliaStokesWallHalfLineLaw d`, let

`D_d(z) = routePPrimitiveGammaJuliaStokesWallFredholmEntireDet μ_d z`,

and let `X(z) = canonicalXiSeamLog z`. Then

`∀ᶠ d in 𝓝[>] 0, ¬ ∃ c : ℂ, X =ᶠ[𝓝 0] fun z ↦ Complex.log (D_d(cz))`.

This is stronger than endpoint separation: `d > 0` gives the discrete, non-scalar prime/Gamma wall law itself.

## Internal frontier audit

- `RoutePPrimitiveGammaJuliaStokesWallFredholmCoefficientLimit.lean` proves coefficientwise convergence `a_n(d) → a_n(0)` as `d → 0+`.
- `RoutePPrimitiveGammaJuliaStokesWallFirstJetInvariant.lean` proves `a₁(0)=1`, `a₂(0)=19/70`, hence endpoint signed quadratic jet `-16/35`.
- `RoutePPrimitiveGammaJuliaStokesWallHilbertSchmidtEnergyLimit.lean` independently identifies limiting coherence energy `16/35`.
- `RoutePPrimitiveGammaJuliaStokesExpWallXiTauProjectiveJetNoGo.lean` excludes arbitrary scalar rescaling only at endpoint `d=0`.
- No corpus theorem excludes all finite positive apertures near zero after an aperture-dependent complex scalar rescaling.

## External frontier audit

Generalized monodromy/Stokes deformations and their tau functions occur in Bertola (2009), Its–Lisovyy–Prokhorov (2018), and Desiraju (2020); generalized Carleman/Hankel operators occur in Yafaev (2015). Exact searches found no treatment of this arithmetic prime/Gamma wall family, constants `16/35` or `8/35`, or a finite-aperture Xi germ obstruction. This is an audit result, not a priority claim.

## Hostile audit

- **Circularity:** none; inputs are unconditional wall-coefficient convergence and unconditional Xi moment bounds.
- **Fitted freedom:** scalar `c` may depend arbitrarily on `d`, but cancels from the projective two-jet whenever germ equality forces the first jet nonzero.
- **Complex-order loophole:** compare real part of the complex projective wall invariant with the real Xi invariant.
- **Zero-denominator loophole:** Xi first logarithmic derivative is positive, so any asserted germ equality forces `c a₁(d) ≠ 0`.
- **Rediscovery risk:** continuity of finite jets is routine; source-specific conclusion for exact prime/Gamma Stokes data appears absent from audited corpus and literature.
- **Verdict:** `SURVIVES PRELIMINARY ATTACK`.

## Approach

Write `a_n(d)` for the Fredholm coefficient and define

`P(d) = -(2a₂(d)-a₁(d)^2)/(2a₁(d)^2)`.

Coefficient convergence and endpoint values give `P(d) → 8/35` as `d → 0+`; therefore eventually `Re(P(d)) > 9/80`. For a scalar-rescaled determinant, logarithmic jets are

`L₁ = c a₁(d)`, `L₂ = c²(2a₂(d)-a₁(d)^2)`.

Thus `-L₂/(2L₁²)=P(d)` whenever `L₁ ≠ 0`. Germ equality with Xi would instead make this invariant `m₁/m₀²`, while the source-side Xi moment bound gives `m₁/m₀² < 9/80`, contradiction.

## Dependency-closed paper proof

Let `a_n(d)` denote the `n`th canonical wall Fredholm coefficient. Existing coefficient convergence gives

`a₁(d) → 1` and `a₂(d) → 19/70`

as `d → 0+`. Since the limiting denominator is nonzero, continuity of complex addition, multiplication, negation, and division gives

`P(d) = -(2a₂(d)-a₁(d)^2)/(2a₁(d)^2) → 8/35`.

Taking real parts preserves this limit. Since `9/80 < 8/35`, there is a punctured right neighborhood `U` of zero on which `9/80 < Re(P(d))`.

Fix `d ∈ U` and suppose that, for some `c : ℂ`, the germ of `log(D_d(cz))` equals the germ `X(z)` of the canonical Xi seam logarithm. The Fredholm power series has `D_d(0)=1`, first derivative `a₁(d)`, and second derivative `2a₂(d)`. The chain rule and the first two derivatives of logarithm at `1` therefore give

`L₁ = c a₁(d)` and `L₂ = c²(2a₂(d)-a₁(d)^2)`.

Xi's first logarithmic derivative is `m₀/2`, with `m₀>0`; germ equality hence implies `L₁≠0`. Consequently `c≠0` and `a₁(d)≠0`, so field cancellation is valid and

`-L₂/(2L₁²)=P(d)`.

Germ equality also identifies this projective two-jet with Xi's exact invariant `m₁/m₀²`. Both moments are real, so

`Re(P(d)) = m₁/m₀² < 9/80`,

contradicting the defining inequality for `U`. Thus no such `c` exists for any `d ∈ U`. Every dependency is an existing unconditional theorem; no RH or divisor hypothesis is used. ∎

## No-go closure

- **Exact killing theorem/mechanism:** continuity preserves the endpoint projective log-two-jet gap throughout a punctured right neighborhood of the genuine finite-aperture Stokes wall.
- **Strongest positive survivor:** finite-aperture discretization alone cannot repair the Xi mismatch; any viable irregular-RH bridge must add a new even Stokes/monodromy channel or leave this wild-wall neighborhood.
- **New insight:** obstruction is stable under both arbitrary scalar time normalization and the existing non-scalar prime/Gamma aperture deformation.
- **Status:** formalized as `eventually_not_routePPrimitiveGammaJuliaStokesPrimeGammaWallXiTauScalarRescalingAt` in `RoutePPrimitiveGammaJuliaStokesPrimeGammaWallXiTauBoundaryNoGo.lean`. Targeted Lean check passed. All eleven new theorem declarations use only `propext`, `Classical.choice`, and `Quot.sound`. Global lint remains red solely on three unrelated umbrella-reachability errors.

## Log

- 2026-08-25 — created in 1-in-progress after internal/external frontier audit and hostile test.
- 2026-08-25 — promoted to 2-fully-proven after dependency-closed projective-jet proof.
- 2026-08-25 — promoted to 3-formalized after targeted Lean verification and new-declaration axiom audit.
