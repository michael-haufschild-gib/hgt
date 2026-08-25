# Prime/Gamma cold wall all-order Fredholm collapse

- **ID:** route-p-prime-gamma-wall-cold-all-order-fredholm-collapse
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Labels:** `[PROVED HERE]` `[NOVELTY UNVERIFIED]` `[IRREGULAR-RH]` `[SOURCE-HORIZONTAL]`
- **Source:** atomic prime/Gamma Stokes Fredholm expansion and cold prime-2 condensation
- **Statement:** For every fixed Fredholm order `n ≥ 2`, the finite-aperture prime/Gamma wall coefficient tends to zero at the cold boundary.

## Goal

Obtain all-order source-side control of the irregular wall tau function. This exposes higher logarithmic jets without fitting target Xi data and tests whether the quadratic Gamma-six correction extends beyond order two.

## Gates

- [x] 0 → 1  in-progress: source-pure statement, corpus/literature audit, dependency-closed attack
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: targeted Lean check and new-declaration axiom audit
- [ ] 3 → 4  publication-ready: standalone paper and novelty review

## Exact candidate

Let `a_n(d)` be order-`n` coefficient of finite prime/Gamma wall Fredholm determinant. For each fixed `n ≥ 2`,

`a_n(d) → 0` as `d → +∞`.

Equivalently, every nonlinear coefficient collapses when normalized irregular Stokes mass condenses on prime `2`.

## Approach

1. Let `q₂` be constant `n`-tuple with every coordinate prime `2`.
2. For `n≥2`, Fredholm matrix at `q₂` has two identical rows, hence determinant integrand vanishes.
3. Restrict integral to complement of `{q₂}` and apply uniform Hadamard bound `(sqrt n)^n`.
4. Product-PMF atom mass is exactly `w₂(d)^n`, where `w₂(d)` is normalized prime-2 wall mass.
5. Existing cold condensation `w₂(d)→1` forces complement mass, hence `a_n(d)`, to zero.

## Hostile audit

- **Source purity:** only prime/Gamma wall PMF, cubic Stokes kernel, and Fredholm determinant expansion enter. No Xi moment, zero, or RH premise enters.
- **Repeated labels:** retained. Collapse works because dominant repeated tuple has determinant zero; it is not removed from series.
- **Uniformity:** theorem is coefficientwise for each fixed `n`; it does not claim interchange of cold limit with infinite Fredholm sum.
- **Order boundary:** `n≥2` is sharp. Orders zero and one survive and give limiting germ `1+z`.
- **Non-tautology:** cold condensation alone does not imply determinant collapse without diagonal rank degeneracy and uniform integrand control.

## Literature audit

- Novitskii studies convergence of classical Fredholm series for Hilbert--Schmidt kernels: <https://arxiv.org/abs/1210.1134>.
- Bertola's Malgrange/Fredholm framework supplies analytic tau sections for Riemann--Hilbert problems: <https://arxiv.org/abs/1703.00046>.
- Desiraju realizes a six-ray irregular Painleve-II tau as a Fredholm determinant: <https://arxiv.org/abs/2008.01142>.
- Audit found no arithmetic prime/Gamma atomic cold-collapse theorem or this all-order coefficient conclusion. Absence is audit inference, not priority claim.

## Dependency-closed paper proof

Fix `n≥2` and positive `d`. Write `μ_d` for product prime-label PMF and `F_n` for determinant integrand. Let `q₂(i)=2` for every `i : Fin n`. Since `0` and `1` are distinct indices and all labels of `q₂` agree, rows `0` and `1` of its Fredholm matrix agree. Therefore `F_n(q₂)=0`.

The integral defining `n! a_n(d)` is consequently supported on `{q₂}ᶜ`. Hadamard's bound gives `|F_n|≤(sqrt n)^n`, hence

`|a_n(d)| ≤ ((sqrt n)^n / n!) μ_d({q₂}ᶜ)`.

Because `μ_d` is a probability measure and its coordinates are independent,

`μ_d({q₂}) = ∏_{i : Fin n} w₂(d) = w₂(d)^n`.

Thus `μ_d({q₂}ᶜ)=1-w₂(d)^n`. Existing cold-wall condensation gives `w₂(d)→1`; continuity of fixed powers gives `1-w₂(d)^n→0`. Squeezing proves `a_n(d)→0`. Every dependency is already unconditional in the source-side corpus. ∎

## Formal certificate

- **Module:** `RoutePPrimitiveGammaJuliaStokesPrimeGammaWallColdAllOrderFredholmCollapse.lean`
- **Theorem:** `tendsto_routePPrimitiveGammaJuliaStokesPrimeGammaWallFredholmCoefficient_atTop_of_two_le`
- **Verification:** direct module check passed; theorem depends only on `propext`, `Classical.choice`, and `Quot.sound`.
- **Next consequence:** derive limiting cubic wall log jet and compare it against canonical Xi seam third jet plus even Gamma-six correction.

## Log

- 2026-08-25 — exact candidate formed from cold prime-2 atom plus diagonal Fredholm degeneracy.
- 2026-08-25 — corpus and external literature audits completed; dependency-closed paper proof obtained.
- 2026-08-25 — promoted to 2-fully-proven before formalization.
- 2026-08-25 — promoted to 3-formalized after targeted module check and one-theorem axiom audit.
