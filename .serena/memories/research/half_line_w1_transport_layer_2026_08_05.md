# Half-line W₁ transport layer (2026-08-05)

Built for card `2-fully-proven/mobius-fixed-current-von-mangoldt-critical-transport-weld.md`,
whose last Lean gate is "formalize the transport identities (14)–(22)".

## Mathlib has none of it

No Wasserstein distance, no quantile function, no inverse-transform sampling, no Laplace-transform
continuity theorem.  It *does* have `ProbabilityTheory.cdf`, `ProbabilityTheory.expMeasure`,
`cdf_expMeasure_eq`, `cdf_eq_real` (not `cdf_eq_toReal`), `Integrable.integral_eq_integral_meas_lt`
and `lintegral_eq_lintegral_meas_lt` (layer cake), `integral_exp_neg_Ioi_zero`.

## Built: `HTGeometry/HalfLineTransportDistance.lean`

- `survival μ t = μ.real (Ioi t)`; `halfLineW1 μ ν = ∫ t in Ioi 0, |survival μ t - survival ν t|`.
- `integral_survival_eq_mean` — layer cake: `∫₀^∞ S_μ = E[X]` for a half-line law.
- `integrableOn_survival` — finite mean ⇒ survival integrable on `Ioi 0`.
- `tendsto_halfLineW1_of_tendsto_survival` — **the criterion**: pointwise survival convergence plus
  convergence of first moments ⇒ `W₁ → 0`.
- `halfLineW1_triangle`, `tendsto_halfLineW1_pair`.
- `Exp(1)` reference law: `survival_expMeasure_one` (= `exp (-t)`), `expMeasure_one_nonneg_ae`,
  `integrable_id_expMeasure_one`, `integral_id_expMeasure_one` (mean one).

## The proof trick worth remembering

No compactness or uniform integrability is needed.  Use the pointwise identity
`|S - T| = S + T - 2 min S T`.  The minimum is dominated by the limit survival function (integrable
by the layer cake), so dominated convergence sends `∫ min` to the limit mean; the two outer
integrals are the two means; `m + m - 2m = 0`.

## Built: `HTGeometry/QuantileCoupling.lean`

Mathlib has `cdf` but no quantile and no inverse-transform sampling.

- `quantile μ p = sInf {x | p ≤ cdf μ x}`.
- `quantile_le_iff` — the Galois connection `quantile μ p ≤ x ↔ p ≤ cdf μ x` for `0 < p < 1`.
  Proof of the hard direction: the defining set is an up-set containing its infimum, because
  `cdf` is right-continuous (`StieltjesFunction.right_continuous` + `ge_of_tendsto` on `𝓝[>]`).
- `measurable_quantile` — needs the junk values: `quantile μ p = 0` for `p ≤ 0`
  (`Real.sInf_of_not_bddBelow` on `univ`) and for `1 < p` (`Real.sInf_empty`); the preimage of
  `Iic x` splits into `Ioo 0 1 ∩ Iic (cdf μ x)`, a constant region, and a subset of `{1}`.
- `map_quantile_eq` — inverse transform sampling, via `Measure.ext_of_Iic`.
- `monotoneCoupling`, `map_fst_monotoneCoupling`, `map_snd_monotoneCoupling`,
  `integral_quantile_eq_mean`, `integral_monotoneCoupling_abs_sub`,
  `lintegral_dist_monotoneCoupling`.

## Built: the (15) limit

- `tendsto_integral_abs_sub_of_tendsto` — abstract Scheffé cancellation on any measure space
  (nonneg + a.e. convergence + converging integrals ⇒ L¹ convergence).  Same `|a-b| = a+b-2 min a b`
  trick as the survival version; use this one for new work.
- `quantile_nonneg` (half-line support), `integrableOn_quantile` (via `integrable_map_measure` and
  `map_quantile_eq`).
- `tendsto_integral_monotoneCoupling_abs_sub` — a.e. quantile convergence + mean convergence ⇒
  monotone-coupling cost → 0.
- `tendsto_quantile_of_tendsto_cdf` — quantile convergence from cdf convergence, with the two
  local-strictness hypotheses on the limit cdf stated explicitly (no global strict monotonicity).
- `cdf_expMeasure_one_lt_of_lt`, `lt_cdf_expMeasure_one_of_lt`, `quantile_expMeasure_one`
  (`Q(p) = -log(1-p)`), `tendsto_quantile_expMeasure_one`, `expMeasure_one_Iio_zero`.
- **Capstone** `tendsto_integral_monotoneCoupling_expMeasure_one`: cdf convergence to `Exp(1)` plus
  means → 1 gives vanishing monotone-coupling cost.  This is exactly (15)'s shape.

## Built: `HTGeometry/DiscreteHalfLineLaw.lean`

`weightedPointLaw x w = Measure.sum fun i => w i • Measure.dirac (x i)` — the carrier for both
clock laws.  Needs no `Countable` on the index (`Measure.sum` is total).  Facts: set measure via
`Set.indicator` (avoid `if`, which needs `Decidable (x i ∈ s)`), total mass, probability criterion,
`lintegral`/`integral` as weighted sums, `weightedPointLaw_Iio_zero` (logarithmic points ⇒ half-line
law), survival function, `lintegral_exp_neg_weightedPointLaw` / `integral_exp_neg_weightedPointLaw`
(the Laplace transform = Dirichlet series at a shifted abscissa), `integral_id_weightedPointLaw`
(the mean).

## Built: `HTGeometry/CompactMomentWeakConvergence.lean`

The `[0,1]` half of the Laplace continuity theorem.

- `probabilityMeasure_ext_of_integral_pow_eq` — moments determine a law on `Icc a b`.
- `probabilityMeasure_tendsto_of_integral_pow_tendsto` — moment convergence ⇒ weak convergence.
- Helpers: `integrable_continuousMap`, `continuous_integral_real_continuousMap`,
  `abs_integral_continuousMap_le`, `integral_polynomial_eq_sum`.

Technique: skip the closed-kernel/CLM machinery the torus file uses.  Approximate a continuous `f`
by a polynomial via `polynomialFunctions_closure_eq_top` + `Metric.mem_closure_iff`, bound each
integral by the uniform norm, conclude the functional difference is below every tolerance
(`le_of_forall_pos_le_add`), then `MeasureTheory.ext_of_forall_integral_eq_of_IsFiniteMeasure`.
Weak convergence reuses the corpus's general `continuous_integral_complex_continuousMap`-style
pattern: `tendsto_nhds_of_unique_mapClusterPt` + `eq_of_mapClusterPt_of_tendsto`
(both already general in the compact space `X`, in `TorusFourierWeakConvergenceLaw`).

Traps: `polynomialFunctions` membership destructures to a conjunction (`obtain ⟨p, -, hp⟩`);
`Algebra.mem_top`, not `Subalgebra.mem_top`; `ContinuousAt` needs the `Tendsto` statement spelled
out before `exact`.

## Built: Laplace continuity (item 2 CLOSED)

`HTGeometry/ExponentialCompactification.lean` + `HTGeometry/LaplaceContinuityHalfLine.lean`.

- `expProj x = Set.projIcc 0 1 _ (exp (-x))` — total continuous map ℝ → `Icc 0 1`; on the half line
  `(expProj x : ℝ) = exp (-x)` (`coe_expProj_of_nonneg`).
- `expPush μ = Measure.map expProj μ`, `expPushProb` bundles it.
- `integral_pow_expPush` — **the Laplace transform at `u = k` is the `k`-th moment** of the
  compactified law.
- `tendsto_expPushProb_of_tendsto_laplace` — Laplace convergence ⇒ weak convergence (via the
  compact-interval moment theory).
- `expMeasure_one_singleton` — no atoms (`gammaMeasure = volume.withDensity _`, so
  `Measure.restrict_eq_zero.mpr Real.volume_singleton`).
- `expTailSet t = Subtype.val ⁻¹' Ici (exp (-t))`; `expPush_expTailSet` identifies its mass with
  `μ (Iic t)`; `frontier_expTailSet_subset` (via `Continuous.frontier_preimage_subset` and
  `frontier_Ici`) plus `expPush_frontier_expTailSet` give the null frontier.
- `tendsto_cdf_expMeasure_one_of_tendsto_laplace` — **Laplace ⇒ cdf convergence**, using
  `ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'`.
- `tendsto_integral_monotoneCoupling_of_tendsto_laplace` — **(11) + (13) ⇒ (15)** in one theorem.

## Built: `HTGeometry/LogClockLaw.lean`

`logClockLaw w = weightedPointLaw (fun n => Real.log n) (fun n => ENNReal.ofReal (w n))`.

- `isProbabilityMeasure_logClockLaw` (needs `ENNReal.ofReal_tsum_of_nonneg`; summability is
  recovered from `∑' w = 1` by contradiction with `tsum_eq_zero_of_not_summable`).
- `logClockLaw_Iio_zero` (via `Real.log_natCast_nonneg`).
- `integral_exp_neg_logClockLaw` — **Laplace transform = shifted Dirichlet series**; needs
  `w 0 = 0` because `exp (-(u * log 0)) = 1` while `(0:ℝ)^(-u) = 0`.
- `integral_id_logClockLaw` — **mean = logarithmically weighted Dirichlet sum**.
- `tendsto_integral_monotoneCoupling_logClock` — the arithmetic form of (11)+(13) ⇒ (15).

## Built: `HTGeometry/RealDirichletSeries.lean`

- `lseriesTerm_ofReal`, `ofReal_tsum_eq_lseries` — a real `L`-series at a real abscissa is the real
  Dirichlet sum (needs `Complex.ofReal_cpow`, `Complex.ofReal_tsum`; no summability hypothesis).
- `summable_real_of_lseriesSummable` (via `Complex.summable_ofReal`),
  `summable_vonMangoldt_rpow`, `tsum_vonMangoldt_rpow_pos` (bound below by the `n = 2` term).
- `ofReal_tsum_vonMangoldt_eq` — **the real von Mangoldt Dirichlet sum is `-ζ′/ζ`**, i.e. the
  corpus's `vonMangoldtCurrent`, via mathlib `LSeries_vonMangoldt_eq_deriv_riemannZeta_div`.
- `eulerClockWeight`, `tsum_eulerClockWeight`, `eulerClockLaw`,
  `isProbabilityMeasure_eulerClockLaw`, `eulerClockLaw_Iio_zero`,
  `integral_exp_neg_eulerClockLaw` (**Laplace transform = `A(σ+u)/A(σ)`**).
- `summable_vonMangoldt_logMul_rpow`, `ofReal_tsum_vonMangoldt_logMul_eq` (**log-weighted sum =
  `-A′(σ)`**, via `LSeriesSummable_logMul_of_lt_re` + `LSeries_deriv`),
  `integrable_id_eulerClockLaw`, `integral_id_eulerClockLaw` (**mean = `-A′(σ)/A(σ)`**).
- In `DiscreteHalfLineLaw`: `integrable_weightedPointLaw` (mathlib `integrable_sum_dirac`).
- Trap: `LSeries.logMul f n = Complex.log ↑n * f n`; convert with
  `rw [← Complex.ofReal_natCast n, ← Complex.ofReal_log (Nat.cast_nonneg n)]`.  `LSeries.term` is
  an `if`, so rewrite the coefficient *function* (`hcoef`) before using `Summable.congr`.

mathlib assets found: `ArithmeticFunction.LSeriesSummable_vonMangoldt`,
`LSeries_vonMangoldt_eq_deriv_riemannZeta_div`, and `LSeries_deriv` (term-by-term differentiation,
which is what the clock mean needs next).

## Built: `HTGeometry/SquarefreeClockLaw.lean`

Generic `dirichletTotal` / `dirichletClockWeight` / `dirichletClockLaw` for any nonnegative
arithmetic weight, with mass, half-line support, Laplace transform (ratio of shifted totals) and
mean (ratio of the log-weighted total to the plain one).  Then `squarefreeWeight n = (μ n)^2`
with `squarefreeWeight_le_one` (from `moebius_eq_or`), summability via
`LSeriesSummable_of_bounded_of_one_lt_real`, positivity from the `n = 1` term, log-summability via
`LSeriesSummable_logMul_of_lt_re`, and the clock `squarefreeClockLaw` with its Laplace transform
and mean.

Trap: the `μ` notation for `moebius` is not in scope here even with `open ArithmeticFunction`;
write `moebius n`.

## Built: `HTGeometry/HalfLineScaling.lean`

`scaleLaw c μ = Measure.map (c * ·) μ` with half-line preservation, and the two transformation
rules `integral_exp_neg_scaleLaw` (rescaling multiplies the Laplace argument) and
`integral_id_scaleLaw` (rescaling multiplies the mean).  Then `scaledEulerClockLaw σ` and
`scaledSquarefreeClockLaw σ` at `c = σ - 1`, with Laplace transforms `A(σ+uε)/A(σ)`,
`Z(σ+uε)/Z(σ)` and means `ε·(-A′/A)`, `ε·(-Z′/Z)` — literally the card's (11) and (13).

## Built: `HTGeometry/ExponentialLaplaceValue.lean`

`integral_exp_neg_expMeasure_one : ∫ e^{-uy} d(expMeasure 1) = 1/(1+u)` for `u ≥ 0`, via
`expMeasure 1 = volume.withDensity (exponentialPDF 1)` (`rfl`),
`lintegral_withDensity_eq_lintegral_mul`, splitting at `Ioi 0` (the complement handled with
`compl_Ioi` + `Iio_ae_eq_Iic` since the density is only zero on `Iio 0`), and
`integral_comp_mul_left_Ioi` to scale `integral_exp_neg_Ioi_zero`.  Then
`tendsto_integral_monotoneCoupling_of_tendsto_laplace_value`, the transport capstone whose
hypotheses are the card's own limits `1/(1+k)` and mean `1`.

## Built: (15) in closed form

- `tendsto_integral_monotoneCoupling_pair` (in `QuantileCoupling`) — mutual cost from a common
  limit law, via the triangle inequality on quantile integrals plus `squeeze_zero`.
- `tendsto_integral_monotoneCoupling_pair_of_tendsto_laplace_value` (in `ExponentialLaplaceValue`)
  — **the two-clock critical transport statement**: hypotheses are exactly Laplace limits
  `1/(1+k)` and mean limits `1`.

## Built: `RHTower/MobiusCriticalTransportAssembly.lean`

`tendsto_integral_exp_neg_scaledEulerClockLaw`, `tendsto_integral_id_scaledEulerClockLaw`,
`tendsto_integral_exp_neg_scaledSquarefreeClockLaw` — three of the four clock limits.
Key find: the corpus already has the squarefree side in REAL Dirichlet form —
`RHTower.squarefreeMobiusMass sigma n = if Squarefree n then n^{-sigma} else 0`,
`squarefreeMobiusTotal`, `mobiusCriticalBoundaryParameter sigma u = sigma + u*(sigma-1)` (literally
my scaled abscissa), and `tendsto_squarefreeMobiusBoundaryLayerLaplace` along `𝓝[>] 1`.  So
`dirichletTotal_squarefreeWeight_eq_total` is a one-line `tsum_congr` and the limit follows by
composing with `ε ↦ 1 + ε`.  The Euler mean needs `deriv_lseries_vonMangoldt_eq` (the `L`-series and
the current agree on the open half plane, so `Filter.EventuallyEq.deriv_eq` applies).  Pattern for the remaining three limits: cast the clock's real Dirichlet ratio to ℂ
(`ofReal_tsum_vonMangoldt_eq_current` / `ofReal_dirichletTotal_squarefreeWeight_eq`), apply the
corpus's complex limit along `𝓝[>] 0`, then compose with `Complex.continuous_re` and use
`Tendsto.congr'` with `filter_upwards [self_mem_nhdsWithin]`.  Note: `ring` can succeed only via
its `ring_nf` fallback and then logs a "Try this" suggestion — write `ring_nf` directly to keep the
build message-free.

## Remaining for the card

1. Transport the corpus's analytic limits (11)/(13) to the Dirichlet-sum form.  Euler side done
   (`ofReal_tsum_vonMangoldt_eq`).  Squarefree side needs
   `dirichletTotal squarefreeWeight σ = ζ(σ)/ζ(2σ)`, which factors as
   (a) `μ(n)² = ∑_{d²|n} μ(d)` — DONE as `sum_moebius_sq_dvd`.  The multiplicativity route was
   avoided entirely: define `sqDivisorPart n = (n.factorization.mapRange (·/2) _).prod (· ^ ·)`,
   whose factorization is free from `Nat.factorization_prod_pow_eq_self_of_le_factorization`; then
   `d² ∣ n ↔ d ∣ sqDivisorPart n` by `Nat.factorization_le_iff_dvd` + `omega`, the square part is
   `1` iff `n` is squarefree (`Nat.squarefree_iff_factorization_le_one`), and
   `moebius_mul_coe_zeta` + `ArithmeticFunction.coe_mul_zeta_apply` give the divisor sum.
   Traps: `ζ` notation is not in scope (use `congrArg` on the equation); rewriting under an `if`
   needs `simp only`, not `rw`.
   Endpoints also proved: `ofReal_tsum_oneWeight_eq` (`∑ n^{-σ} = ζ(σ)`, via
   `LSeries_one_eq_riemannZeta`) and `ofReal_tsum_moebius_eq` (`∑ μ(n) n^{-σ} = 1/ζ(σ)`, via
   `LSeries_zeta_mul_Lseries_moebius` + `LSeries_zeta_eq_riemannZeta`).
   SQUAREFREE IDENTITY DONE: `ofReal_dirichletTotal_squarefreeWeight_eq`
   (`dirichletTotal squarefreeWeight σ = ζ(σ)/ζ(2σ)`).  Route that worked: divisor-sum convolution
   `sum_divisors_sqrtMoebius` (`∑_{a|n} sqrtMoebius a = μ(n)²`, proved by `Finset.sum_subset` onto
   the image of `(sqDivisorPart n).divisors` under `d ↦ d²`, then `Finset.sum_image`), then
   mathlib's `LSeries_convolution'` at the single abscissa σ, bridged to real sums, with the `2σ`
   entering only through the already-real `tsum_sqrtWeight`.  Traps: the `⍟` notation is scoped
   (write `LSeries.convolution`); the bridge produces a double coercion ℤ→ℝ→ℂ, so rewrite the
   coefficient function first; and
   (b) the square substitution `tsum_sqrtWeight` — DONE (in `SquarefreeClockLaw`, via
   `Function.Injective.tsum_eq` with support ⊆ range, `Nat.sqrt_eq'`, and
   `Real.rpow_natCast`/`Real.rpow_mul` for `(d²)^{-σ} = d^{-2σ}`).  Also proved:
   `squarefreeWeight_eq_indicator` (the weight is the squarefree indicator).
   mathlib has `LSeries_zeta_mul_Lseries_moebius` for `L(μ,s) = 1/ζ(s)`.
2. (15a)–(15c), (16)–(17), (18)–(22).
2. DONE — see above.
3. Then (14) follows from the criterion above with the proved moment input (13).
4. W₂ and (15a)–(15c), the four-unit Gini law (16)–(17), packet isometry (18)–(22).

Only item 1 (instantiating the two clock laws and identifying their weighted sums with the
Dirichlet quotients) still gates (14)–(15); everything else is proved.

## 2026-08-06 — the layer is complete

`(14)`–`(22)` of `mobius-fixed-current-von-mangoldt-critical-transport-weld` are all compiled
unconditionally.  New modules:

- `HTGeometry/QuadraticTransportCost.lean` — quadratic Scheffé from the L¹ one via
  `|a-b|² ≤ |a²-b²|` (nonneg reals); `W₂` criterion; centered form; the gap law of a coupling.
- `HTGeometry/ClockSecondMoment.lean` — second moment of a Dirichlet clock = second logarithmic
  Dirichlet sum = `(LSeries f)″` (apply `LSeries_deriv` twice; the second application needs the
  first on a whole half plane, so state the abscissa bound as `≤ (a : EReal)` with `a < σ`).
- `HTGeometry/PairGiniLaw.lean` — `E|X-X'| = EX + EX' - 2∫₀^∞ S_μ S_ν` via the survival function of
  the minimum; `∫₀^∞ S_{Exp(1)}² = 1/2`; `W₁`-continuity of the squared survival integral.
- `RHTower/ComplementaryPacketTwoPointDistance.lean` — `∫₀^∞ (B_h-B_k)² = D_ω(|h-k|)`.
- `RHTower/MobiusCriticalPacketTransport.lean` — `(19)`–`(22)`.

Traps worth remembering:
- mathlib has **no** Scheffé lemma in any form; build L² from L¹ by the squared-difference bound,
  never by Fatou.
- the second moment of `Exp(1)` is the **third** Gamma integral: `Gamma 3 = 2`, via
  `Real.Gamma_eq_integral` and `rpow_natCast`.
- transport statements need `IsProbabilityMeasure (μ i)` for **every** index, so clamp the
  parameter (`escape ε = if 0 < ε then 1 + ε else 2`) and transfer with `Tendsto.congr'`.
- `Measure.fst_prod`/`Measure.snd_prod` need the *other* factor to be a probability measure; use
  `Measure.quasiMeasurePreserving_fst.ae` to move a.e. statements onto a product.
- `integral_mono_of_nonneg` needs no integrability of the smaller function — the right tool when a
  parameter integral's measurability is not yet available.
