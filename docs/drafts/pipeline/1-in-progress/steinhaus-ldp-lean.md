# Regular-variation weighted Steinhaus LDP: the Lean build

- **ID:** `steinhaus-ldp-lean`
- **Stage:** 1-in-progress
- **Type:** LEAN INFRASTRUCTURE
- **Opened:** 2026-08-23
- **Blocks:** `docs/drafts/pipeline/2-fully-proven/not_new_scientific_knowledge/09-mobius-prime-sums/regular-variation-weighted-steinhaus-ldp.md`

## Inventory (searches run 2026-08-23)

`formal_tools.py research`: "Steinhaus Haar circle Laplace transform Bessel I0 product",
"modified Bessel function first kind integral representation exp cos", "large deviation principle
Gartner Ellis Cramer rate function", "slowly varying function Karamata uniform convergence regular
variation", "prime sum weighted p to the minus alpha asymptotic partial summation".

ALREADY OWNED (do not rebuild):

- `HTGeometry/SteinhausLaplaceProduct.lean` — the entire one-circle layer:
  `steinhausProjection`, `steinhausLaplace r = ∫ e^{r·Re ζ} dHaar`, the EXACT product formula
  `integral_exp_weightedSteinhausProjection` (the card's `(13)`), the envelopes
  `exp(−|r|) ≤ L(r) ≤ exp|r|`, `1 ≤ L`, evenness, positivity, and the cumulant
  `steinhausLogLaplace = log L` with:
  - `steinhausLogLaplace_eq_cgf` — it IS mathlib's `ProbabilityTheory.cgf`;
  - `integrableExpSet_steinhausProjection = univ`;
  - `analyticOnNhd_steinhausLogLaplace` — real-analytic on all of `ℝ`;
  - `iteratedDeriv_two_steinhausLogLaplace_pos` — the card's `m'(x) > 0`;
  - `strictConvexOn_steinhausLogLaplace`.
  So `log I₀` and everything the card says about it are corpus assets; the card's `I₀` is
  `steinhausLaplace` and its `log I₀(x)` is `steinhausLogLaplace x`.
- `RHTower/BesselIZeroODE.lean` — `besselI0` by its integral representation, with derivative and
  second-derivative integrals; `RHTower/BesselIZeroLowerBound.lean` —
  `exp z/(2π√z) ≤ besselI0 z`, the large-argument lower envelope the card's `(27)` needs.
- Mathlib: `ProbabilityTheory.mgf`, `cgf`, `analyticOnNhd_cgf`,
  `iteratedDeriv_two_cgf_eq_integral`, `Moments/Tilted.lean`.

NOT PRESENT anywhere: any large-deviation principle, any Gärtner--Ellis theorem, any
Legendre-transform API, any regular-variation / Karamata framework.

## Layer plan

The card's parts `3`, `4`, `5` are pure analysis of the rate function and need NO probability;
parts `1` and `2` need the LDP.  The analytic core is therefore built first.

- `S1` the weight profile `w_α(v) = (1−α)v^{−α}` on `(0,1]`, `∫₀¹ w_α = 1`, integrability.
- `S2` the cumulant `Λ_α(λ) = ∫₀¹ log I₀(λ w_α(v)) dv`; integrability from
  `0 ≤ steinhausLogLaplace ≤ |·|`, hence finiteness (the card's `(11)`--`(12)`).
- `S3` `Λ_α(0) = 0`, `Λ_α ≥ 0`, `Λ_α(λ) ≤ λ`, convexity.
- `S4` differentiability under the integral: `Λ'_α(λ) = ∫₀¹ w_α m(λ w_α)`, with `0 ≤ m < 1` and
  `m' > 0`; `Λ'_α` strictly increasing from `0` to `∫₀¹ w_α = 1`.
- `S5` `I_α(q) = sup_{λ ≥ 0}(λq − Λ_α(λ))`: finite and strictly increasing on `[0,1)`,
  `I_α(0) = 0`, `I_α(q) → ∞` as `q → 1⁻` (part `3`).
- `S6` the small-`q` trichotomy (part `4`), by `log I₀(x) ≍ x²/4` near `0` and the substitutions
  `(19)` / `(24)`.
- `S7` the large-`q` law (part `5`), from `log I₀(x) = x − ½log(2πx) + O(1/x)`.
- `S8` an LDP definition and the Gärtner--Ellis upper/lower bounds (parts `1`, `2`).
- `S9` prime Karamata `(9)`--`(10)`: the regular-variation layer.

## Log

- 2026-08-23 — Opened.  Inventory above; the one-circle cumulant layer is already complete in the
  corpus, which removes the special-function half of `S2`--`S4`.

## S1 and S2 closed (2026-08-23)

`HTGeometry/SteinhausWeightProfile.lean`:

- `weightProfile α v = (1−α)v^{−α}`, nonnegative, interval-integrable on `(0,1)` for `α < 1`
  (`intervalIntegral.intervalIntegrable_rpow'` needs exactly `−1 < −α`);
- **`integral_weightProfile : ∫₀¹ w_α = 1`** — the card's normalisation, from `integral_rpow` with
  `0^{1−α} = 0`;
- `rvCumulant α lam = ∫₀¹ log I₀(lam·w_α(v)) dv`, the card's `Λ_α`;
- `continuous_steinhausLogLaplace` (from the corpus's `analyticOnNhd_steinhausLogLaplace`);
- `intervalIntegrable_rvCumulant_integrand` — finiteness, from `0 ≤ log I₀(x) ≤ |x|` and the
  integrability of `w_α`.  This is the card's `(11)`–`(12)` at the level of well-definedness;
- `rvCumulant_zero`, `rvCumulant_nonneg`, and **`rvCumulant_le : Λ_α(λ) ≤ |λ|`**, the unit-mass
  bound.

NOTE for `S5`: finiteness of the Legendre transform for `q < 1` needs the LOWER envelope
`log I₀(x) ≥ x − log(2π√x)`.  The corpus owns it as
`RHTower/BesselIZeroLowerBound.exp_div_le_besselI0`, but for `besselI0` (a `(1/π)∫₀^π cosh(u sin θ)`
integral), not for `steinhausLaplace` (an `AddCircle` Haar integral).  The two are equal — the
bridge is `AddCircle` Haar ↔ `(1/2π)∫₀^{2π}`, plus `∫₀^{2π} e^{u cos} = ∫₀^{2π} e^{u sin}` by
translation — and that bridge is the next module.  Searches "AddCircle Haar integral equals
interval integral period bridge" and "steinhaus laplace equals bessel I0 cos integral" found no
existing version.
