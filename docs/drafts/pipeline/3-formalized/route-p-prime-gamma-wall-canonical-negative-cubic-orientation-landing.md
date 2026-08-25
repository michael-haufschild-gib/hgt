# Canonical negative cubic source orientation landing

- **ID:** route-p-prime-gamma-wall-canonical-negative-cubic-orientation-landing
- **Stage:** 3-formalized
- **Type:** THEOREM / POSITIVE SURVIVOR
- **Labels:** `[NEW]` `[PAPER-PROVED]` `[IRREGULAR-RH]` `[SOURCE-HORIZONTAL]`
- **Source:** Euler third logarithmic jet, Wold coefficientwise counterterm, completed Xi
  Malgrange cubic residual

## Exact no-go

Existing completed-residue transport forces

`combinedLanding_N = -2 defectMoment_N / log(p_N)^3 · orientationBlock`

and this tends entrywise to zero. The newly proved wall--Xi cubic residual is strictly negative,
hence nonzero. Therefore this normalized grade-forgetting channel cannot equal the residual. Any
positive scalar selected from their quotient would be target fitting and is rejected.

## Strongest positive survivor

Before the collapsing prime-clock normalization, the literal source-renormalized current

`J_X = Σ_{n<X} (-EulerCubicNaturalAtom(n) + WoldNaturalCounterterm(n))`

has canonical negative orientation for every `X ≥ 3`; its summable limit is also strictly negative.
Both `J_X` and its limit lie in the same strict negative Stokes chamber as

`R_Xi = normalizedPrimeArchMoment(2) - normalizedPrimeArchMoment(0)^3/4`.

Equivalently, `R_Xi J_X > 0` for every `X ≥ 3`, and `R_Xi J_∞ > 0`.

## Closed paper proof

The exact coefficientwise identity gives

`J_X = -Σ_{n<X} naturalDefect(n)`.

Every natural defect is nonnegative; the `n=2` term is strictly positive. Thus every cutoff
containing `2` has `J_X<0`. Summability and the same positive `n=2` term make the total defect tsum
strictly positive, so `J_∞<0`. The formalized theta score theorem gives `R_Xi<0`; products of the
two negative quantities are strictly positive. Existing source convergence supplies `J_X→J_∞`.

## Novelty audit

- Corpus contains source current, completed-residue collapse, and cubic residual formula, but not
  residual sign or this canonical chamber landing.
- Bertola's Malgrange-form framework and later Fredholm/RH tau-function literature describe
  monodromy dependence and tau divisors, not this completed-zeta Euler/Wold source orientation.
- Searches for an Euler--Gamma/Wold cubic Malgrange landing found no exact arithmetic statement.
  Absence is audit inference, not priority claim.

## Formal targets

- `sourceHorizontalEulerGammaWoldCubicNaturalDefect_nonneg`
- `sourceHorizontalEulerGammaCubicNaturalRenormalizedNegativeCurrent_neg`
- `sourceHorizontalEulerGammaCubicNaturalRenormalizedLimit_neg`
- `routePPrimitiveGammaJuliaStokesPrimeGammaWallCanonicalNegativeCubicOrientationLanding`

No hypotheses in the capstone beyond cutoff condition `3 ≤ X`; no Xi-zero selection, fitted scale,
new axiom, or numerical computation.

## Lean realization

- Module:
  `formal/GaloisForLFunctions/RHTower/RoutePPrimitiveGammaJuliaStokesPrimeGammaWallCanonicalNegativeCubicOrientationLanding.lean`
- Normalized-collapse no-go:
  `not_tendsto_sourceHorizontalEulerWoldNormalizedCubicDefect_to_xiResidual`
- Positive-survivor capstone:
  `routePPrimitiveGammaJuliaStokesPrimeGammaWallCanonicalNegativeCubicOrientationLanding`
- Direct and targeted module checks passed; umbrella import wired without umbrella build. Axiom
  audit of all five new public theorems reports only `propext`, `Classical.choice`, and
  `Quot.sound`.

## Literature

- M. Bertola, *The dependence on the monodromy data of the isomonodromic tau function*,
  <https://arxiv.org/abs/0902.4716>.
- M. Cafasso, P. Gavrylenko, O. Lisovyy, *Tau functions as Widom constants*,
  <https://arxiv.org/abs/1712.08546>.
- H. Desiraju, *Fredholm determinant representation of the Painlevé II tau-function*,
  <https://arxiv.org/abs/2008.01142>.

## Log

- 2026-08-25 — exact normalization-collapse no-go isolated; quotient scaling rejected as target
  fitting.
- 2026-08-25 — strongest unnormalized orientation survivor proved on paper and promoted directly to
  Stage 2.
- 2026-08-25 — no-go and strongest source-natural survivor formalized exactly; card promoted to
  Stage 3.
