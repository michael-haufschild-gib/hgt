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

## The cumulant's Taylor data at the origin (2026-08-23)

`RHTower/SteinhausCumulantTaylor.lean`:

- `mem_interior_integrableExpSet` — the exponential-integrability set is all of `ℝ`, so every
  mathlib `cgf` derivative formula applies at every tilt;
- `deriv_steinhausLogLaplace_zero : (log I₀)'(0) = 0` (from `deriv_cgf` and `∫ proj = 0`);
- **`iteratedDeriv_two_steinhausLogLaplace_zero : (log I₀)''(0) = 1/2`** (from
  `iteratedDeriv_two_cgf_eq_integral` at `0`, `mgf 0 = 1`, and `∫ proj² = 1/2`);
- **`tendsto_steinhausLogLaplace_div_sq : log I₀(x)/x² → 1/4`** as `x → 0` — the card's `(17)`.
  Proved by l'Hôpital (`HasDerivAt.lhopital_zero_nhdsNE`): the ratio of derivatives is
  `(log I₀)'(x)/(2x) = slope((log I₀)', 0, x)/2 → (log I₀)''(0)/2 = 1/4`, using that the first
  derivative vanishes at the origin.

Card 11: 11 modules.  The sub-critical regime of part `4` now needs only the dominated-convergence
step `Λ_α(λ)/λ² → (1/4)∫w_α²` (dominating function `w_α²/2`, integrable exactly for `α < 1/2`) and
the Legendre asymptotic `Λ ∼ Aλ² ⟹ I ∼ q²/(4A)`.

## The sub-critical integrand (2026-08-23)

`RHTower/SteinhausSubcritical.lean`:

- `weightProfile_sq_eq : w_α(v)² = (1−α)²v^{−2α}` and
  `intervalIntegrable_weightProfile_sq` — square integrability, valid exactly for `α < 1/2`;
- `rvQuadIntegrand α lam v = log I₀(lam·w_α(v))/lam²`, with
  **`rvQuadIntegrand_bound : |·| ≤ w_α(v)²/2`** (the dominating function, integrable precisely in
  the sub-critical range) and
  **`tendsto_rvQuadIntegrand : rvQuadIntegrand α lam v → w_α(v)²/4`** as `lam → 0⁺`, obtained by
  composing `log I₀(x)/x² → 1/4` with `lam ↦ lam·w_α(v)` (which maps `𝓝[>]0` into `𝓝[≠]0` because
  `w_α(v) > 0`).

Both hypotheses of dominated convergence are therefore in place; the remaining step of `(18)` is
the application of `tendsto_integral_filter_of_dominated_convergence` on `volume.restrict (Ioc 0 1)`
and the identification of the limit with `(1/4)∫₀¹ w_α² = (1−α)²/(4(1−2α))`.

Card 11: 12 modules.

## Equation (18) CLOSED (2026-08-23)

**`tendsto_rvCumulant_div_sq`**: for `α < 1/2`,
```
Λ_α(λ)/λ² → (1−α)²/(4(1−2α))   as λ → 0⁺,
```
by `tendsto_integral_filter_of_dominated_convergence` on `volume.restrict (Ioc 0 1)` with
dominating function `w_α²/2`.  The filter `𝓝[>]0` is countably generated, so the filter form of
dominated convergence applies directly; the limit integral is `(1/4)∫₀¹ w_α²`.

This is the card's `(18)`, the sub-critical leading term.  What part `4`'s first line still needs
is the Legendre step `Λ ∼ Aλ² ⟹ I ∼ q²/(4A)`, i.e. `I_α(q) ∼ [(1−2α)/(1−α)²]q²`.

Card 11: 13 modules.

## PART 4, FIRST REGIME CLOSED (2026-08-23)

**`tendsto_rvRate_div_sq`**: for `0 ≤ α < 1/2`,
```
I_α(q)/q² → (1 − 2α)/(1 − α)²   as q → 0⁺,
```
which is the first line of the card's `(6)`.

Chain:

- `SteinhausCumulantPositive.lean` — `steinhausLogLaplace_pos` (strict convexity plus evenness:
  `f(0) < (f(x)+f(−x))/2 = f(x)`) and `rvCumulant_pos`;
- `SteinhausCumulantSlope.lean` — `steinhausLogLaplace_scale_le : log I₀(tx) ≤ t·log I₀(x)` for
  `0 ≤ t ≤ 1` (convexity through the origin), hence
  **`rvCumulant_slope_mono : (λ/δ)Λ_α(δ) ≤ Λ_α(λ)`** for `δ ≤ λ`;
- `SteinhausSubcriticalRate.lean` — `eventually_le_rvRate_quad`: the tilt `λ = q/(2A′)` gives
  `I_α(q) ≥ q²/(4A′)` for every `A′` above the true constant;
- `SteinhausSubcriticalUpper.lean` — `eventually_rvRate_le_quad`: below `δ` the quadratic lower
  bound caps every tilt at `q²/(4A″)`, and beyond `δ` the nondecreasing slope makes the tilt value
  NEGATIVE once `q < Λ_α(δ)/δ`, which is where `rvCumulant_pos` is used;
- `SteinhausSubcriticalLimit.lean` — the two halves assembled through `tendsto_order`.

Card 11: 18 modules.  Remaining: the critical (`α = 1/2`) and super-critical (`α > 1/2`) lines of
part `4`, part `5`, the LDP (`S8`), and Karamata (`S9`).

## PART 4 CLOSED — all three regimes (2026-08-29)

The critical and super-critical lines of `(6)` are now Lean-proved, and the mechanism that closed
both is a single exact identity.

### The scaling identity (the step that removes `λ` from the integrand)

`HTGeometry/SteinhausScalingIdentity.lean` — **`rvCumulant_eq_rpow_mul_tail`**:
```
Λ_α(λ) = λ^{1/α} · ∫₀^{λ^{−1/α}} log I₀(w_α(u)) du      (0 < α < 1, λ > 0)
```
because `λ · w_α(λ^{1/α} u) = w_α(u)` identically (`mul_weightProfile_rpow`).  The substitution is
the LINEAR map `v = λ^{1/α} u`, so `intervalIntegral.smul_integral_comp_mul_left` does it in one
step.  Every small-tilt asymptotic of `Λ_α` is therefore a large-interval asymptotic of the FIXED
integrand `rvTailIntegral`.  Also holds `tendsto_rpow_neg_inv_atTop`.

### The abstract Legendre power law

`RHTower/SteinhausRatePowerAsymptotic.lean` — `rvLegConst p A = (p−1)p^{−p/(p−1)}A^{−1/(p−1)}`,
`rvLegTilt p A q = (q/(pA))^{1/(p−1)}`, and
- **`rvLegTilt_value`**: `λq − Aλ^p = rvLegConst p A · q^{p/(p−1)}` EXACTLY at that tilt (because
  `Aλ^p = λq/p` there);
- **`young_rvLegConst`**: `λq ≤ Aλ^p + rvLegConst p A · q^{p/(p−1)}`, i.e. mathlib's
  `Real.young_inequality` at `a = (pA)^{1/p}λ`, `b = q(pA)^{−1/p}`;
- `eventually_le_rvRate_pow` / `eventually_rvRate_le_pow` — the two halves, the second using the
  corpus's `rvCumulant_slope_mono` to kill every tilt beyond `δ`;
- **`tendsto_rvRate_div_rpow`**: `Λ_α(λ)/λ^p → A` ⟹ `I_α(q)/q^{p/(p−1)} → rvLegConst p A`.
This is `p = 2` for the sub-critical regime and `p = 1/α` for the super-critical one, so the two
lines of `(6)` are the SAME theorem at two exponents.

### Super-critical (`1/2 < α < 1`)

`RHTower/SteinhausSuperConstant.lean` — the fixed integrand `u ↦ log I₀(w_α(u))` is integrable on
`(0,∞)`: near `0` it is `≤ w_α(u)` (integrable for `α < 1`), near `∞` it is `≤ w_α(u)²/2`
(integrable for `2α > 1`).  `rvSuperConst α = ∫_{(0,∞)}` is the card's `K_α`;
`tendsto_rvTailIntegral` is `intervalIntegral_tendsto_integral_Ioi`.

`RHTower/SteinhausSupercriticalLimit.lean` — `rvSuperConst_pos`,
**`tendsto_rvCumulant_div_rpow_super`** (`Λ_α(λ)/λ^{1/α} → K_α`, the card's `(25)`),
`rvLegConst_inv_eq` (`rvLegConst (1/α) K = (1−α)α^{α/(1−α)}K^{−α/(1−α)}` — the card's `(7)`), and
**`tendsto_rvRate_div_rpow_super`**: `I_α(q)/q^{1/(1−α)} → C_α`.

### Critical (`α = 1/2`)

`HTGeometry/IntegralLogCesaro.lean` — **`tendsto_logAverage_atTop_of_tendsto`**: `u·f(u) → c`
implies `(∫₁^R f)/log R → c`.  Proved by transporting the corpus's
`tendsto_intervalAverage_atTop_of_tendsto` along `u = e^t` with
`intervalIntegral.integral_deriv_smul_comp`.  Fully reusable.

`RHTower/SteinhausCriticalCumulant.lean` — the integrand truncated below `1` (so it is globally
continuous, which the substitution lemma demands), `tendsto_mul_truncCritIntegrand`
(`u·h(u) → 1/16`, because `x = u^{−1/2}/2` gives `u = 1/(4x²)` and `log I₀(x)/x² → 1/4`), and
**`tendsto_rvCumulant_crit`**: `Λ_{1/2}(λ)/(λ² log(1/λ)) → 1/8`, the card's `(20)`.

`RHTower/SteinhausCriticalRate.lean` — the Legendre transform of a power law WITH a slowly varying
factor, which the abstract `p`-law cannot see:
- `critTilt A q = q/(2A log(1/q))` and **`critTilt_value`**: its value is EXACTLY
  `q²/log(1/q) · critLowerProfile A (log(1/q))` with
  `critLowerProfile A t = 1/(4A) − (log t + log 2A)/(4At)`.  No estimate is used — the identity is
  what makes the lower half a one-line limit;
- `eventually_rvRate_crit_le_profile` — the upper half, splitting the tilt range at `q/A`: below it
  `log(1/λ) ≥ log(1/q) + log A` caps every tilt by `q²/(4A(log(1/q)+log A))`; above it the value is
  already negative because `log(1/λ) ≥ 1` on `(0, e^{−1}]`; beyond `δ` the slope kills it;
- **`tendsto_rvRate_crit`**: `I_{1/2}(q)·log(1/q)/q² → 2`, the card's `(23)`.

All eight new modules are axiom-clean (`propext, Classical.choice, Quot.sound` only) and wired into
`RHTower.lean` / `HTGeometry.lean`.

Remaining: part `5` (the high-coherence endpoint, which needs the SHARP Bessel asymptotic
`log I₀(x) = x − ½log(2πx) + o(1)`; the corpus owns only the two non-matching envelopes), `S8` (the
LDP / Gärtner–Ellis), and `S9` (prime Karamata).

## PART 5 CLOSED — the high-coherence endpoint (2026-08-29)

The card's `(27)` in its SHARP form was the missing input: the corpus owned only two envelopes with
non-matching constants (`x − log(2π√x) ≤ log I₀(x) ≤ x + log√(π/(2x))`), which give `O(1)`, not
`o(1)`.  Laplace's method now supplies the exact constant.

`HTGeometry/SteinhausSharpAsymptotic.lean` (new; the only mathlib import added is
`Analysis.SpecialFunctions.Gaussian.GaussianIntegral`):
- `cos_sub_one_eq : cos y − 1 = −2 sin²(y/2)` (from `Real.sin_sq_eq_half_sub`) and
  `cos_sub_one_le : |y| ≤ π → cos y − 1 ≤ −2y²/π²` (Jordan, `Real.mul_le_sin`);
- `tendsto_sin_div_nhdsNE : sin y/y → 1`, from `hasDerivAt_iff_tendsto_slope` at `Real.sin`;
- `gaussKernel x u = exp(x(cos(u/√x) − 1))`, `gaussWindow x = Ioc(−π√x, π√x)`, `gaussIndicator`;
  `gaussKernel_eq : = exp(−2(√x·sin(u/(2√x)))²)` — the half-angle form that makes the pointwise
  limit `exp(−u²/2)` a one-line composition;
- **`tendsto_integral_gaussIndicator`**: dominated convergence with bound `exp(−2u²/π²)` gives
  `∫ gaussIndicator x → √(2π)`;
- `integral_gaussIndicator_eq`: for `x > 0` that integral IS `2π·√x·e^{−x}·I₀(x)`, via the linear
  substitution `u = √x t` and `Function.Periodic.intervalIntegral_add_eq` moving `[−π,π]` to
  `[0,2π]`, then the corpus's `steinhausLaplace_eq_intervalIntegral`;
- **`tendsto_sqrt_mul_exp_neg_mul_steinhausLaplace : √x·e^{−x}·I₀(x) → 1/√(2π)`** and
  **`tendsto_steinhausLogLaplace_sub_sharp : log I₀(x) − x + ½log(2πx) → 0`**.

`RHTower/SteinhausEndpointCumulant.lean`:
- `le_weightProfile : 1 − α ≤ w_α(v)` on `(0,1]`, which is why NO dominated convergence is needed
  in the mixture: `λ w_α(v) ≥ λ(1−α)` uniformly, so the error of the sharp asymptotic is uniformly
  small on the whole profile;
- `rvCumulant_deficit_eq` — the deficit is EXACTLY `∫₀¹ e(λ w_α(v)) dv`, using
  `∫₀¹ w_α = 1` and `∫₀¹ log w_α = log(1−α)+α`.  The pointwise split needs
  `integral_congr_ae` (not `integral_congr`): it fails at the single point `v = 0`, where
  `w_α(0) = 0` and `Real.log 0 = 0`;
- **`tendsto_rvCumulant_deficit`** — the card's `(29)`.

`RHTower/SteinhausEndpointRate.lean`:
- `endpointTarget α ε = ½log(1/ε) + ½log(π(1−α)) − (1−α)/2`, `endpointTilt ε = 1/(2ε)`;
- **`endpoint_tilt_value_le`** — `−λε + ½log(2πλ) ≤ −½ + ½log(π/ε)` for every `λ > 0`, which is
  `log z ≤ z − 1` at `z = 2λε`.  This is the ENTIRE optimality argument: no calculus;
- `endpoint_tilt_value_eq`, `endpointTarget_eq`, `tendsto_endpointTarget_atTop`;
- **`tendsto_rvRate_endpoint`**: `I_α(1−ε) − endpointTarget α ε → 0`.  Tilts below `λ₀` need no
  asymptotic at all — they contribute at most `λ₀`, while the target diverges, so
  `tendsto_endpointTarget_atTop` disposes of them.

All three modules axiom-clean and wired.  **Parts 3, 4 and 5 of the card are now completely
Lean-proved.**  Remaining: `S8` (the LDP and Gärtner–Ellis, parts 1 and 2) and `S9` (prime
Karamata, `(9)`–`(10)`).

## S9 opened — Karamata's uniform convergence theorem and Potter's bound (2026-08-29)

Searches first (`formal_tools.py research`): "slowly varying function regular variation Karamata
uniform convergence", "uniform convergence theorem for slowly varying additive shift measurable",
"prime number theorem chebyshev theta asymptotic equivalent x", "partial summation Abel prime sum
log p times f p".  The corpus has PNT (`chebyshevTheta_eventually_relative`,
`chebyshev_asymptotic`, `chebyshevTheta_sub_id_isBigO`) but NO regular-variation framework at all —
`RapidlyVarying` in `RapidConvexCurvatureResonance.lean` is a different (lattice) notion.

`HTGeometry/SlowShiftUniform.lean` — **the mathlib gap, additive form**.
`IsSlowShift h` = `h` measurable and `h(x+u) − h(x) → 0` for every fixed `u`.
- `shiftBadSet h c x = {v ∈ [0,2] : c < |h(x+v) − h(x)|}`, measurable (the `|·|` set is written as
  a union of two `measurableSet_lt`s: `Measurable.abs` is NOT in scope under narrow imports);
- **`tendsto_volume_shiftBadSet`** — its measure tends to `0`, by dominated convergence on the
  indicator along `atTop` (which is countably generated);
- **`isSlowShift_uniform_unit`** — the classical selection argument: for `u ∈ [0,1]` the sets
  `C = (·+u)⁻¹(good set at x) ∩ [0,2−u]` and `D = (good set at x+u) ∩ [0,2−u]` each miss at most
  `1/4` of an interval of length `2−u ≥ 1`, so they meet; at a common point `w` the identity
  `x + (w+u) = (x+u) + w` telescopes `h(x+u) − h(x)` into two controlled shifts.  Everything is
  done in `ℝ≥0∞` with `≤` only (no truncated subtraction): disjointness would give
  `2(2−u) ≤ (2−u) + 1/2`, contradiction.
- `abs_sub_le_of_unit_steps` — chaining `k` unit steps via `Finset.sum_range_sub`;
- **`isSlowShift_uniform_nonneg`**, **`isSlowShift_uniform`** (shifts in `[−U, U]`);
- **`isSlowShift_potter : |h y − h x| ≤ (y − x + 2)δ`** for `y ≥ x ≥ X₀(δ)`.

`HTGeometry/SlowlyVarying.lean` — the multiplicative form.
`IsSlowlyVarying L` = measurable, positive on `(0,∞)`, `L(cx)/L(x) → 1` for each `c > 0`.
- `slowLog L t = log L(e^t)` and `isSlowShift_slowLog` — the exponential bridge;
- **`isSlowlyVarying_uniform_log`** and **`isSlowlyVarying_uniform`**:
  `|L(cx)/L(x) − 1| ≤ ε` eventually, uniformly for `c` in any `[a,b]` with `a > 0`.  The passage
  from `|log r| ≤ log(1+ε)` to `|r − 1| ≤ ε` uses `1/(1+ε) ≥ 1 − ε`;
- **`isSlowlyVarying_potter`**: for `y ≥ x ≥ X₀`,
  `e^{−2δ}(x/y)^δ ≤ L(y)/L(x) ≤ e^{2δ}(y/x)^δ`.

All axiom-clean and wired into `HTGeometry.lean`.  This is exactly the input the card's `(9)`–`(10)`
need, and it is reusable well beyond this card (it is the whole Karamata layer).

### Remaining on S9 (the prime Karamata law `(9)`)

`W_X = Σ_{p≤X}(log p)p^{−α}L(p) ∼ X^{1−α}L(X)/(1−α)`.  Plan, now that UCT and Potter are available:
1. split `(0,1]` at a threshold `v₀`; on `[v₀,1]` use `N` uniform blocks `(v_{j−1}X, v_jX]`;
2. on each block `F(vX) = X^{−α}L(X)·v^{−α}·(L(vX)/L(X))` with the ratio in `[1−ε,1+ε]` by UCT and
   `v^{−α}` varying by at most `(1 + 1/(Nv₀))^α`;
3. `Σ_{p∈(aX,bX]} log p = θ(bX) − θ(aX) = (b−a)X(1+o(1))` by the corpus's PNT;
4. the head `v < v₀` is `≪ X^{1−α}L(X)v₀^{1−α−δ}` by Potter, which vanishes as `v₀ → 0`.
Then `(10)` is immediate and `(12)` follows by the same two estimates.

### Remaining on S8 (the LDP)

The planar LDP reduces to a ONE-dimensional one.  `Y_X` is rotation invariant, so
`Y_X =_d R_X e^{iΘ}` with `Θ` uniform and independent; for an open `G` a ball around `z₀` contains a
polar box, so the angular factor is a CONSTANT and does not affect the exponent, while for closed
`F` the norm map is proper, so `{|z| : z ∈ F}` is closed and the two rate infima agree.  Hence only
Cramér/Gärtner–Ellis on `ℝ` is needed, for `R_X = |Y_X|`, whose limiting cgf is `Λ_α(λ)` for
`λ ≥ 0` (the `I₀` polynomial factor is exponentially negligible by the sharp asymptotic already
proved) and `0` for `λ ≤ 0`, hence differentiable everywhere with Legendre transform `I_α`.

## S9, batch 2: the prime shell calculus and the Karamata head (2026-08-29)

Three more axiom-clean modules, all wired into `RHTower.lean`.

`RHTower/PrimeShellWeightedSum.lean` — the device that replaces Riemann–Stieltjes integration for a
merely measurable weight.
- `primeLogSum f a b = ∑_{p ∈ (⌊a⌋, ⌊b⌋]} log p · f p`;
- `mem_shell_of_mem_filter` — membership converts to the REAL shell `a < p ≤ b`
  (`Nat.floor_lt` / `Nat.le_floor_iff`; the `0 ≤ b` side condition is recovered from
  `1 ≤ ⌊b⌋₊` via `Nat.floor_of_nonpos`);
- **`primeLogSum_le` / `le_primeLogSum`** — the two-sided sandwich by the Chebyshev shell mass
  `θ(b) − θ(a)`, using the corpus's `chebyshevTheta_sub_eq_shellSum`;
- `primeLogSum_add` (shells add), `primeLogSum_nonneg`.

`RHTower/PrimePowerSumBound.lean` — a new mathlib-gap estimate.
- `chebyshevTheta_mono`, `chebyshevTheta_nonneg`,
  **`exists_chebyshevTheta_le_linear : θ(x) ≤ Cx`** for `x ≥ 1` (PNT at `ε = 1` plus monotonicity
  below the threshold — the corpus owned only the `ψ` version);
- **`exists_primeLogSum_rpow_le`**: for `0 < β < 1`,
  `∑_{p ≤ Y}(log p)p^{−β} ≤ K_β Y^{1−β}` with `K_β = C·2^β/(1 − 2^{β−1})`.
  Proved by HALVING INDUCTION (`Nat.strong_induction_on` on `⌊Y⌋₊`): the top shell `(Y/2, Y]` costs
  `(Y/2)^{−β}θ(Y) ≤ C2^βY^{1−β}` and the rest is the same statement at `Y/2`, contracting by
  `2^{β−1} < 1`.  No Abel summation, no differentiability of the weight.

`RHTower/PrimeKaramataHead.lean`
- `rvPrimeWeight α L t = t^{−α}L(t)`, `rvWeightSum α L X = primeLogSum (rvPrimeWeight α L) 0 X`
  (the card's `W_X`);
- **`exists_karamata_head_bound`**: for every `ε > 0` there is `v₀ ∈ (0,1)` with
  `∑_{p ≤ v₀X}(log p)F(p) ≤ ε X^{1−α}L(X)` eventually.
  The mechanism: at `δ = (1−α)/2` and `β = α+δ`, Potter gives `L(t) ≤ L(X)e^{2δ}(X/t)^δ` for
  `X₀ ≤ t ≤ X`, so the head above `X₀` is `≤ L(X)e^{2δ}X^δ·K_β(v₀X)^{1−β}
  = K_βe^{2δ}v₀^{1−β}·X^{1−α}L(X)` because `δ + 1 − β = 1 − α` exactly.  The fixed initial segment
  `p ≤ X₀` is a CONSTANT, and `X^{1−α}L(X) → ∞` because Potter also gives `L(X) ≫ X^{−δ}`.

Remaining for `(9)`: the body — the shell sandwich on `(aX, bX]` (UCT for `L(t)/L(X)`, monotonicity
of `v^{−α}`, PNT for `θ(bX) − θ(aX)`), and the Darboux/Riemann-sum assembly over `N` uniform blocks
of `[v₀, 1]`.

## `(9)` CLOSED — the prime Karamata law (2026-08-29)

**`RHTower.tendsto_rvWeightSum`** (axiom-clean, wired):
```
0 ≤ α < 1, L slowly varying  ⟹  W_X / (X^{1−α} L(X)) → 1/(1−α)
```
with `W_X = ∑_{p ≤ X}(log p)p^{−α}L(p)`.  This is the card's `(9)`.

Four more modules complete the chain:

`RHTower/PrimeKaramataShell.lean` — **`karamata_shell_bounds`**: on `(aX, bX]` with `0 < a ≤ b ≤ 1`,
```
b^{−α}(1−ε)((b−a)−2ε)·X^{1−α}L(X) ≤ ∑_{p∈shell}(log p)F(p)
                                   ≤ a^{−α}(1+ε)((b−a)+2ε)·X^{1−α}L(X).
```
The weight factors as `X^{−α}L(X)·(t/X)^{−α}·(L(t)/L(X))`: the power factor is antitone
(`Real.rpow_le_rpow_of_nonpos`), the slowly varying factor is `1 ± ε` by the UCT, and the shell mass
is `(b−a)X ± 2εX` by PNT (`a + b ≤ 2` is what turns `ε(a+b)X` into `2εX`).  `ε < 1` is needed so
that the lower constant stays nonnegative.

`RHTower/PrimeKaramataDarboux.lean` — `primeLogSum_chain` (the shell analogue of
`sum_integral_adjacent_intervals`), `integral_rpow_neg_unit`, and **`rpow_darboux`**: the two Riemann
sums of `v^{−α}` on `[v₀,1]` bracket the integral.  Proved by the affine substitution
`v = v₀ + hu` (`intervalIntegral.integral_comp_mul_add`) reducing to mathlib's unit-step
`AntitoneOn.integral_le_sum` / `AntitoneOn.sum_le_integral`.

`RHTower/PrimeKaramataBody.lean` — `karamataNode`, its monotonicity/endpoints,
**`karamata_shells_bounds`** (the shell sandwich summed over the partition, via
`Filter.eventually_all_finset`) and **`rvWeightSum_decomp`** (`W_X` = head + the `N` shells, via
the chain lemma and `Finset.sum_range_succ'`).

`RHTower/PrimeKaramata.lean` — `primeLogSum_head_mono`, `karamata_darboux_gap`
(`Sup − Slow = v₀^{−α} − 1` by `Finset.sum_range_sub'`), and the assembly.

TRAPS (cost several rebuilds, worth recording):
- the numeric endgame must be done with `linarith only` / `nlinarith only`.  With the full context
  (which holds the shell inequality, the decomposition and the Darboux bracket) plain `linarith`
  times out in the simplex — even on `0 ≤ 1 + ε`;
- `clear_value` on the `set` variables is required before the endgame, and every statement proved
  from their DEFINITION (`hSup0`, the `hnodes` rfl) must come before it;
- purely numeric facts that do not mention `X` must be proved BEFORE `filter_upwards`, otherwise
  they inherit the huge context;
- prefer term-mode `add_nonneg zero_le_one hε0.le` over `by linarith` for trivial side goals.

Remaining on S9: `(10)` (`d_X a_{p,X} → w_α(v)` uniformly, now immediate from `(9)` plus the UCT and
`π(X) ∼ X/log X`) and `(12)`.  Then S8.

## `(10)` and `(12)` CLOSED (2026-08-29)

`RHTower/RVNormalizedWeight.lean` — the card's `(10)`.
- `rvPrimeCount X = π(⌊X⌋)`, `rvNormReal α L X t = d_X·(log t)t^{−α}L(t)/W_X`;
- **`rvNormReal_eq`** — the EXACT four-factor decomposition
  `rvNormReal = w_α(t/X) · [π(X)/(X/log X)]·[log t/log X]·[L(t)/L(X)]·[X^{1−α}L(X)/((1−α)W_X)]`,
  proved by `field_simp` after splitting `(t/X)^{−α}` and `X^{1−α}`;
- `two_factor_bounds`, `four_factor_bounds` — a product of four factors in `[1−c, 1+c]` lies in
  `[(1−c)^4, (1+c)^4]`;
- `tendsto_rvPrimeCount_ratio` (the corpus's `tendsto_primeCounting_ratio`),
  `tendsto_rvWeightSum_inv` (the reciprocal Karamata ratio);
- **`rvNormReal_bounds`**: `(1−c)^4 w_α(t/X) ≤ d_X a_{p,X} ≤ (1+c)^4 w_α(t/X)` uniformly on
  `(aX, bX]`.  The `log t/log X` factor is uniform because `log(t/X)` stays in `[log a, log b]`.

`RHTower/PrimeCountShell.lean` — the UNWEIGHTED prime shell: `primeCountSum`, `primeShellCard`,
**`primeShellCard_bounds`** (`(θ(b)−θ(a))/log b ≤ #shell ≤ (θ(b)−θ(a))/log a`), the two sandwiches
and the chain lemma.  This is what replaces `π(bX) − π(aX)`: only `θ` and `π(X)` are needed.

`RHTower/RVCumulantAverage.lean`
- **`steinhausLogLaplace_mono`** — the one-circle cumulant is monotone on `[0,∞)` (from
  `steinhausLogLaplace_scale_le` and nonnegativity; no new convexity work);
- `rvCumulantAverage`, `rvNormReal_nonneg`, **`rvCumulantAverage_head_le`** — the head of the
  average is `≤ λ·d_X·W_{v₀X}/W_X`, purely from `log I₀(x) ≤ x`;
- `tendsto_chebyshevTheta_div`, `tendsto_log_shift_ratio`, `tendsto_rvPrimeCount_ratio_inv`, and
  **`tendsto_shell_card_ratio`**: `#(aX, bX]/d_X → b − a`.  Proved by squeezing
  `#·log X/X` between the two `θ`-quotients and multiplying by `(X/log X)/d_X → 1`;
- `antitone_darboux` (the general antitone Darboux bracket), `rvProfileCumulant`,
  `antitoneOn_rvProfileCumulant`, `integral_rvProfileCumulant_head_le` and
  `integral_rvProfileCumulant_split`.

`RHTower/RVCumulantLimit.lean`
- `weightProfile_antitone`, `rvUpSum`/`rvLoSum` (the DISTORTED Riemann sums, continuous in the
  distortion parameter `c`), `rvDarboux_gap`;
- `rvCumulantAverage_decomp`, **`rvCumulantAverage_shell_bounds`**;
- **`tendsto_rvCumulantAverage`** — the card's `(12)`:
  `(1/d_X)∑_{p ≤ X} log I₀(λ d_X a_{p,X}) → Λ_α(λ)` for every `λ ≥ 0`.

The design point that made `(12)` tractable: the distortion `(1±c)^4` sits INSIDE `log I₀`, so it
cannot be pulled out multiplicatively.  Instead the finitely many Riemann terms are treated as a
continuous function of `c` and `c` is chosen AFTER `v₀` and `N` — no uniform continuity, no
Lipschitz estimate for `log I₀` is needed.

**S9 is complete.**  Remaining for card 11: S8, the LDP itself (parts 1 and 2).

## S8 opened — the complex Steinhaus sum and the Chernoff bound (2026-08-29)

`HTGeometry/SteinhausComplexSum.lean`
- `steinhausSum a x = ∑ a_i ζ_i` (the card's `Y_X`), `steinhausRotProj a s x = Re(Y e^{−is})`,
  `steinhausRotProj_eq_re`;
- `steinhausPhase_add_coe` — the phase shift `ζ(y + s) = ζ(y)e^{is}`, by
  `QuotientAddGroup.induction_on` and `fourier_coe_apply`;
- **`integral_exp_rot`** — the rotated one-circle Laplace transform EQUALS the unrotated one, by
  `MeasureTheory.integral_add_right_eq_self` (Haar translation invariance).  This is the only
  probabilistic input;
- **`integral_exp_steinhausRotProj`** — hence `E[e^{r Re(Y e^{−is})}] = ∏ I₀(r a_i)` for EVERY `s`;
- `rot_re_eq : Re(z e^{−is}) = ‖z‖cos(arg z − s)` and
  **`steinhausLaplace_norm_eq_rot_average`**: `I₀(t‖z‖) = (1/2π)∫₀^{2π} e^{t Re(z e^{−is})} ds`
  (the substitution `u = arg z − s` plus `Function.Periodic.intervalIntegral_add_eq`);
- **`integral_steinhausLaplace_norm`**: `E[I₀(t‖Y‖)] = ∏ I₀(t a_i)`, by Fubini
  (`integral_integral_swap`; integrability from continuity plus the uniform bound
  `|Re(Y e^{−is})| ≤ ∑|a_i|`).

This is the step that makes the whole upper bound sharp: NO covering of the circle of directions is
needed, and no `cos(π/K)` loss.

`RHTower/SteinhausChernoff.lean`
- `steinhausLaplace_mono` (monotone on `[0,∞)`, from the log version);
- `continuous_steinhausSum_norm`, `measurableSet_normGe`;
- **`meas_norm_ge_mul_le`**: `P(‖Y‖ ≥ q)·I₀(tq) ≤ ∏ I₀(t a_i)` for `t, q ≥ 0`.  Markov applied to
  the monotone function `x ↦ I₀(t‖Y(x)‖)`, whose integral is the Laplace product.

Remaining for S8: instantiate at `a = a_{p,X}`, `t = λ d_X` (using `(12)` and the sharp Bessel
asymptotic `log I₀(y) = y − ½log(2πy) + o(1)` to get `(1/d_X)log I₀(λ d_X q) → λq`), giving
`limsup (1/d_X) log P(|Y_X| ≥ q) ≤ Λ_α(λ) − λq` for every `λ ≥ 0`, hence `≤ −I_α(q)`.  Then the
LOWER bound (exponential tilting of the product of circle laws plus a tilted weak law), and finally
the planar LDP by the rotation-invariance reduction recorded above.

## The large-deviation UPPER bound closed (2026-08-29)

`RHTower/RVSteinhausModel.lean` — the card's model, instantiated.
- `rvPrimeFinset X`, `rvWeightFun α L X` (the `a_{p,X}`), `rvPrimeCount_mul_rvWeightFun`
  (`d_X a_{p,X} = rvNormReal`), **`sum_rvWeightFun = 1`**, `rvWeightFun_nonneg`,
  `sum_steinhausLogLaplace_rvWeightFun` (the tilted cumulant sum IS the prime average of `(12)`);
- `rvDeviationProb α L X q = P(‖Y_X‖ ≥ q)`, `rvDeviationProb_le_one`, and
  **`rvDeviationProb_pos`** — strictly positive for `q < 1`, because `{‖Y‖ > q}` is OPEN and
  contains the all-aligned point (where `‖Y‖ = ∑ a_i = 1`), and Haar is open-positive;
- **`log_rvDeviationProb_le`** — the Chernoff bound in log form:
  `log P ≤ ∑_p log I₀(λ d_X a_{p,X}) − log I₀(λ d_X q)`;
- `tendsto_steinhausLogLaplace_div_id : log I₀(y)/y → 1` (from the sharp asymptotic),
  `tendsto_rvPrimeCount_atTop`, `tendsto_rvPrimeCount_logI0 : log I₀(λ d_X q)/d_X → λq`;
- **`eventually_log_rvDeviationProb_le`**: for every `0 < q < 1` and every `ε > 0`,
  ```
  (1/d_X) log P(|Y_X| ≥ q) ≤ −I_α(q) + ε   eventually.
  ```
  A near-optimal tilt is extracted from `exists_lt_of_lt_csSup`; it is automatically nonzero
  because the value at `λ = 0` is `0 < I_α(q) − ε/2`.

This is the `limsup` half of the card's `(5)`.  Everything it uses — `(12)`, the sharp Bessel
asymptotic, the rotational Laplace identity — is now Lean-proved.

REMAINING for card 11:
1. the `liminf` half of `(5)`: exponential tilting of the product of circle laws, a tilted weak law
   of large numbers (Chebyshev on the tilted variance `∑ a_p²(log I₀)''(λ d_X a_p)`), and the
   change-of-measure inequality;
2. part `1`, the planar LDP, via the rotation-invariance reduction: the radial LDP transfers
   because the norm map is proper (closed sets stay closed) and every open set contains a polar box
   whose angular factor is a constant.

## The lower-bound route, designed (2026-08-29)

The tilted measure is NOT needed.  The three-way split of the exact exponential moment does the
whole job, because both side pieces can be compared with the SAME product formula at a different
tilt:

```
∫ e^{tW} dμ = ∏ I₀(t a_i)                                  (the corpus identity)
∫_{W<q}   e^{tW} dμ ≤ e^{(t−s)q}   ∏ I₀(s a_i)   (s < t)
∫_{W>q+δ} e^{tW} dμ ≤ e^{(t−u)(q+δ)} ∏ I₀(u a_i) (u > t)
⇒ ∫_{q≤W≤q+δ} e^{tW} dμ ≥ ∏I₀(t a_i) − (both sides)
⇒ P(W ≥ q) ≥ e^{−t(q+δ)} ∫_{q≤W≤q+δ} e^{tW} dμ.
```
At `t = λd_X`, `s = λ'd_X`, `u = λ''d_X` the two side pieces are exponentially smaller exactly when

* `(Λ_α(λ) − Λ_α(λ'))/(λ − λ') > q`  (chord slope on the left of `λ` exceeds `q`), and
* `(Λ_α(λ'') − Λ_α(λ))/(λ'' − λ) < q + δ` (chord slope on the right is below `q+δ`).

Both hold for `λ` near the maximiser of `λq − Λ_α(λ)` PROVIDED `Λ_α` is differentiable with
`Λ'_α(λ*) = q` — which is the card's `(16)`.  So the remaining layer is:

- `S8-a` `|(log I₀)'| ≤ 1` (the tilted mean of a variable bounded by one);
- `S8-b` `Λ'_α(λ) = ∫₀¹ w_α(v) m(λ w_α(v)) dv` by differentiation under the integral, dominated by
  `w_α ∈ L¹` — this is exactly the card's `(16)`;
- `S8-c` `Λ'_α` is continuous and strictly increasing from `0` to `∫₀¹ w_α = 1`, hence hits every
  `q ∈ (0,1)`;
- `S8-d` the three-way split above, and `P(‖Y‖ ≥ q) ≥ P(W ≥ q)` since `‖Y‖ ≥ Re Y`;
- `S8-e` assembly: `liminf (1/d_X) log P(|Y_X| ≥ q) ≥ −I_α(q)`, then the card's `(5)` and, by the
  rotation-invariance reduction, the planar LDP of part `1`.
