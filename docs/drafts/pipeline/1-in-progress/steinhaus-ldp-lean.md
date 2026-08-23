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

## The linear lower bound and the interval bridge (2026-08-23)

`HTGeometry/SteinhausCumulantLower.lean` — the finiteness input for `S5`, obtained WITHOUT any
quantitative measure computation:

- `projArc c = {x : c < proj x}` is open and contains `0` (where `proj = 1`), so its Haar mass
  `arcMass c` is positive for every `c < 1` (`arcMass_pos`);
- restricting the Haar integral to that arc gives `I₀(x) ≥ μ_c·e^{cx}` for `x ≥ 0`
  (`arcMass_mul_exp_le_steinhausLaplace`), hence
  `le_steinhausLogLaplace : cx + log μ_c ≤ log I₀(x)`;
- integrated against the unit-mass profile,
  **`le_rvCumulant : cλ + log μ_c ≤ Λ_α(λ)`** for `λ ≥ 0`.
  Since `c < 1` is arbitrary this already forces `Λ_α(λ)/λ → 1`, which is exactly what makes
  `I_α(q) = sup_{λ≥0}(λq − Λ_α(λ))` FINITE for every `q < 1`: take `q < c < 1` and the supremum is
  at most `−log μ_c`.

`HTGeometry/SteinhausIntervalBridge.lean` — **the bridge**:

- `steinhausProjection_coe : proj ↑t = cos t` (from `fourier_coe_apply` at `T = 2π`);
- **`steinhausLaplace_eq_intervalIntegral : I₀(r) = (1/2π)∫₀^{2π} e^{r cos t} dt`**, via
  `AddCircle.integral_preimage` and `AddCircle.volume_eq_smul_haarAddCircle`.

This identifies the abstract Haar integral with the classical Bessel integral and is the gate to
every SHARP envelope: the upper bound `log I₀(x) ≤ x − ½log x + C` (needed for `I_α(q) → ∞`, and
for `S6`/`S7`) now reduces to `cos t ≤ 1 − 2t²/π²` on `[−π,π]` (Jordan's inequality via
`cos t = 1 − 2sin²(t/2)`) plus mathlib's Gaussian integral.

## `I₀` identified, both sharp envelopes inherited (2026-08-23)

Search "cosine upper bound quadratic Jordan inequality sin half angle" turned up
`RHTower/BesselIZeroUpperBound.lean`, which ALREADY proves
`besselI0_le_exp_div_sqrt : besselI0 z ≤ e^z·√(π/(2z))` by exactly the Jordan + Gaussian argument I
was about to redo, and `RHTower/BesselIZeroLowerBound.exp_div_le_besselI0` for the other side.  My
half-written re-derivation was discarded; instead the two objects are identified.

`RHTower/SteinhausBesselIdentity.lean`:

- `integral_exp_cos_eq_exp_sin` — `∫₀^{2π}e^{r cos} = ∫₀^{2π}e^{r sin}`, by `sin(t+π/2) = cos t`
  and one period shift;
- `integral_exp_sin_fold` — `∫₀^{2π}e^{r sin} = 2∫₀^{π}cosh(r sin)`, folding `[π,2π]` onto
  `[0,π]` with `sin(u+π) = −sin u`;
- **`steinhausLaplace_eq_besselI0 : I₀ = besselI0`**;
- hence, for free,
  `steinhausLogLaplace_le : log I₀(x) ≤ x + log√(π/(2x))` for `x > 0`, and
  `le_steinhausLogLaplace_sharp : x − log(2π√x) ≤ log I₀(x)` for `x ≥ 1`.

These are the card's `(27)` in both directions, and they are what `S5`'s divergence, `S6` and `S7`
consume.  Card 11 now stands at 4 Lean modules on top of the corpus's existing Steinhaus layer.

## S5, first half (2026-08-23)

`RHTower/SteinhausRateFunction.lean` — `rvLegendreSet`, `rvRate α q = sup_{λ≥0}(λq − Λ_α(λ))`, and:

- `bddAbove_rvLegendreSet` — **finiteness for every `q < 1`**: pick `q < c < 1`; the lower bound
  `Λ_α(λ) ≥ cλ + log μ_c` makes every element at most `λ(q−c) − log μ_c ≤ −log μ_c`;
- `rvRate_nonneg`, `le_rvRate` (every tilt is a lower bound), `rvRate_zero`, `rvRate_mono`.

Remaining in `S5`: strict monotonicity and `I_α(q) → ∞` as `q → 1⁻`.  The latter now follows from
`steinhausLogLaplace_le` once `∫₀¹ log w_α = log(1−α) + α` is available (the card's `(28)`), giving
`Λ_α(λ) ≤ λ − ½log λ + C_α` and hence `I_α(q) ≥ ½log(1/(2(1−q))) − C_α`.

## Part 3's divergence closed (2026-08-23)

`RHTower/SteinhausProfileLogIntegral.lean`:

- `integral_log_unit : ∫₀¹ log v = −1` (mathlib's `integral_log` is unconditional, and
  `0·log 0 = 0`);
- `weightProfile_pos`, `log_weightProfile : log w_α(v) = log(1−α) − α log v` for `v > 0`,
  `intervalIntegrable_log_weightProfile` (the `v = 0` endpoint is discarded a.e.);
- **`integral_log_weightProfile : ∫₀¹ log w_α = log(1−α) + α`** — the card's `(28)`;
- `log_sqrt_pi_div`, and **`rvCumulant_le_sub_half_log`**:
  ```
  Λ_α(λ) ≤ λ − ½log λ + (log π − log 2 − log(1−α) − α)/2      (λ > 0),
  ```
  the deficit, obtained by integrating the sharp upper envelope of `log I₀` against the profile.
  The pointwise inequality fails at the single point `v = 0`, so the comparison is done with
  `integral_mono_ae_restrict` after rewriting `restrict (Icc 0 1) = restrict (Ioc 0 1)`;
- `le_rvRate_log : ½log(1/(1−q)) − 1 − C_α ≤ I_α(q)` (take `λ = 1/(1−q)`);
- **`tendsto_rvRate_atTop : I_α(q) → ∞` as `q → 1⁻`** — part `3`'s divergence claim.

Card 11 now has 6 modules.  Remaining in part `3`: continuity and STRICT monotonicity, both of
which reduce to `Λ_α(λ)/λ → 0` as `λ → 0⁺` (dominated convergence against the integrable `w_α`,
using `(log I₀)'(0) = 0`).  Then parts `4`, `5`, and the LDP (`S8`) and Karamata (`S9`) layers.

## Sub-Gaussianity and strict positivity (2026-08-23)

Search "Hoeffding lemma bounded random variable sub gaussian mgf quadratic bound" found mathlib's
`hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero` and the corpus's
`HTGeometry/BoundedSumConcentration.hasSubgaussianMGF_of_centred_bounded`; the mathlib form is used
directly.

`RHTower/SteinhausSubgaussian.lean`:
- `integral_haar_eq_intervalIntegral` — the bridge, for an arbitrary integrand;
- `integral_steinhausProjection_eq_zero` — the projection is centred (`∫₀^{2π} cos = 0`);
- **`steinhausLogLaplace_le_sq : log I₀(x) ≤ x²/2`** — Hoeffding's lemma, since the projection lies
  in `[−1,1]` and is centred, so it is sub-Gaussian with proxy one.

`RHTower/SteinhausRatePositive.lean`:
- `integral_weightProfile_Icc : ∫₀^δ w_α = δ^{1−α}`;
- **`rvCumulant_le_split`** — splitting at `δ` and using `log I₀ ≤ x` below, `log I₀ ≤ x²/2` above:
  ```
  Λ_α(λ) ≤ λδ^{1−α} + (λ²/2)(1−α)²δ^{−2α}.
  ```
  So `Λ_α(λ)/λ → 0` as `λ → 0⁺`, with an explicit two-parameter bound rather than dominated
  convergence.
- **`rvRate_pos : 0 < I_α(q)` for `0 < q < 1`** — choose `δ = (q/2)^{1/(1−α)}` so that
  `δ^{1−α} = q/2`, then `λ = min(1, q/(2K))`; the tilt value is at least `λq/4 > 0`.

Card 11 is now at 8 modules.  Part `3` still needs strict monotonicity (which follows from
`rvRate_pos` plus the observation that any tilt with value `> I − ε` must have `λ > I − ε`, since
`λq − Λ ≤ λ`) and continuity.

## PART 3 CLOSED (2026-08-23)

`RHTower/SteinhausRateStrictMono.lean`:

- **`rvRate_strictMono`** — `I_α` is strictly increasing on `[0,1)`.  The mechanism: any tilt whose
  value exceeds `I − ε` satisfies `λ ≥ λq − Λ_α(λ) > I − ε` (because `Λ_α ≥ 0` and `q ≤ 1`), so
  moving `q` up by `d` gains at least `(I−ε)d`; taking `ε = I·d/4` makes
  `(I−ε)(1+d) = I(1 + d(3−d)/4) > I`.
- `rvRate_convex`, `convexOn_rvRate` — the rate is a supremum of affine functions of `q`, hence
  convex on `Iio 1`;
- **`continuousOn_rvRate`** — continuity on `Iio 1`, from `ConvexOn.continuousOn` on the open set.

Together with `rvRate_zero`, `rvRate_pos` and `tendsto_rvRate_atTop`, **part `3` of the card's
theorem is now completely Lean-proved**: `I_α` is continuous and strictly increasing on `[0,1)`,
`I_α(0) = 0`, and `I_α(q) → ∞` as `q → 1⁻`.

Card 11: 9 modules.  Remaining: parts `4` (the small-`q` trichotomy), `5` (the high-coherence
expansion), `S8` (the LDP and Gärtner--Ellis), `S9` (prime Karamata).

## The two second moments (2026-08-23)

`RHTower/SteinhausSecondMoments.lean`:

- **`integral_steinhausProjection_sq : ∫ proj² dHaar = 1/2`** — the variance of the circle
  projection, via the bridge and `∫₀^{2π} cos² = π`;
- **`integral_weightProfile_sq : ∫₀¹ w_α² = (1−α)²/(1−2α)`** for `α < 1/2` — finite exactly below
  the critical index, and the constant of the card's first regime:
  `I_α(q) ∼ [(1−2α)/(1−α)²]q²` is `q²/(4A)` with `A = (1/4)∫w_α²`.

Card 11: 10 modules.  The remaining input for part `4`'s sub-critical regime is
`log I₀(x)/x² → 1/4`, i.e. the second-order Taylor coefficient of the cumulant at the origin,
which is `Var/2` with `Var = 1/2` now available.
