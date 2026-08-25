# Prime/Gamma Stokes-wall Xi tau explicit cold no-go

- **ID:** route-p-prime-gamma-wall-xi-tau-explicit-cold-no-go
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Labels:** `[PROVED HERE]` `[CANDIDATE NEW SCIENTIFIC KNOWLEDGE]` `[IRREGULAR-RH]` `[SOURCE-NATIVE]` `[NO-GO]`
- **Source:** exact positive-aperture prime/Gamma Stokes wall and its prime-log Gibbs weights
- **Statement:** At every aperture `d ≥ 1`, no complex scalar rescaling of canonical prime/Gamma Stokes-wall Fredholm determinant has logarithmic germ equal to `canonicalXiSeamLog`.

## Goal

Replace asymptotic cold-boundary exclusion by explicit full half-ray `[1,∞)`. Combined with wild-wall boundary-neighborhood obstruction, this confines any possible scalar-rescaled Xi match to finite intermediate aperture below one.

## Gates

- [x] 0 → 1  in-progress: well-posed, source-pure, exact constants, Door passport sketch
- [x] 1 → 2  fully-proven: dependency-closed paper proof independently audited
- [x] 2 → 3  formalized: Lean theorem, targeted check, new declarations axiom-audited
- [ ] 3 → 4  publication-ready: standalone paper and novelty review

## Exact conjecture

With `D_d`, `X`, and scalar-rescaling predicate from preceding wall cards,

`∀ d : ℝ, 1 ≤ d → ¬ ∃ c : ℂ, X =ᶠ[𝓝 0] fun z ↦ Complex.log (D_d(cz))`.

Stronger quantitative target:

`w_d(2) > 12/25`, `E(d) > 9/40`, and `Re P(d) > 9/80` for every `d ≥ 1`.

## Frontier and literature audit

- Corpus has only punctured `d → 0+` and eventual `d → +∞` exclusions. It has no explicit cold threshold for this wall.
- Global monotonicity of full pair coherence remains unjustified and is not used.
- General irregular-Riemann–Hilbert/Fredholm-tau literature (Bolibruch–Malek–Mitschi; Bertola; Desiraju) supplies realization and determinant mechanisms, not this prime-log Gibbs aperture bound.
- Simon's total-positivity results for Cauchy kernels do not give this arithmetic normalized-mass constant.
- Exact searches found no prime/Gamma wall bound `w_d(2)>12/25`, coherence floor `9/40`, or Xi germ exclusion on `[1,∞)`. Audit result only; no priority claim.

## Hostile audit

- **Circularity:** none. Inputs are prime ordering, elementary logarithm bounds, summability, positive wall weights, and already-proved Xi projective bound.
- **Target-fed data:** none. Threshold `1` and constants `12/25`, `9/40` arise from source weights.
- **Infinite-tail loophole:** tail is dominated explicitly by integer series `Σ_{n>11} log n/n²`, with integral certificate `(log 11 + 1)/11`.
- **Strictness loophole:** rational certificate remains strict after all logarithm relaxations.
- **Scalar loophole:** projective logarithmic two-jet cancels arbitrary nonzero complex time rescaling.
- **Verdict:** `SURVIVES PRELIMINARY ATTACK`.

## Dependency-closed paper proof candidate

Write

`b_d(p)=log(p)p^{-(1+2d)}` and `Z_d=Σ_p b_d(p)`.

For `d≥1`, rescale by prime-2 Boltzmann factor:

`c_d(p)=exp(2d log 2)b_d(p)`.

Then `c_d(2)=log 2/2`, and positivity of energy gap `2(log p-log 2)` gives `c_d(p)≤c_1(p)` termwise. At `d=1`,

`c_1(p)=4 log(p)/p³`.

Split prime sum at eleven. Elementary bounds

`log 3<6/5`, `log 5<17/10`, `log 7<2`, `log 11<5/2`, `log 2>2/3`

and, for every prime `p>11`, `p≥13`, give

`Σ_{p>11} log(p)/p³ ≤ (1/13) Σ_{n>11} log(n)/n²`

`≤ (log 11+1)/143 < 7/286`.

Consequently

`Σ_{p>2} log(p)/p³`

`< (6/5)/27 + (17/10)/125 + 2/343 + (5/2)/1331 + 7/286`

`< 13/144 < 13 log(2)/96`.

Adding prime two yields

`Σ_p log(p)/p³ < 25 log(2)/96`,

so

`Σ_p c_d(p) ≤ Σ_p c_1(p) < 25 log(2)/24 = (25/12)c_d(2)`.

The normalized prime-two mass therefore satisfies

`w_d(2)=c_d(2)/Σ_p c_d(p)>12/25`.

Diagonal positivity of cubic Stokes coherence gives

`E(d)≥w_d(2)²>(12/25)²=144/625>9/40`.

Existing exact Fredholm calculation gives `P(d)=E(d)/2`, hence `Re P(d)>9/80`. Xi's projective invariant is strictly below `9/80`; equality of scalar-rescaled logarithmic germs would identify these invariants, contradiction. ∎

## No-go closure target

- **Killing mechanism:** explicit prime-two dominance on complete cold half-ray, not asymptotic condensation.
- **Strongest positive survivor:** any scalar-rescaled match must lie below aperture one and outside already-excluded wild-wall neighborhood.
- **Next live core:** bounded intermediate aperture window between two proved exclusions; repair must modify even Stokes data or source-to-Xi comparison.

## Formal certificate

- **Module:** `RoutePPrimitiveGammaJuliaStokesPrimeGammaWallXiTauExplicitColdNoGo.lean`
- **Capstone:** `forall_one_le_not_routePPrimitiveGammaJuliaStokesPrimeGammaWallXiTauScalarRescalingAt`
- **Quantitative chain:** prime cubic mass `< 25 log(2)/96`; prime-two wall mass `>12/25`; cubic coherence `>9/40`; projective wall jet real part `>9/80`.
- **Verification:** direct targeted Lean check passed. All five new public theorems use only `propext`, `Classical.choice`, and `Quot.sound`.
- **Lint:** new module passes formal lint rules. Repository lint remains nonzero only for five unrelated pre-existing umbrella-reachability errors.

## Log

- 2026-08-25 — exact source-only threshold conjecture formed after rejecting unsupported global coherence monotonicity.
- 2026-08-25 — hostile audit passed; rational constant and elementary log certificates checked against current Lean toolchain.
- 2026-08-25 — promoted to 2-fully-proven after dependency audit closed tail, strictness, normalization, and scalar-rescaling loopholes.
- 2026-08-25 — promoted to 3-formalized after targeted Lean verification and five-declaration axiom audit.
