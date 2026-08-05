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

## Remaining for the card

1. Instantiate `weightedPointLaw` at the two clock weights and identify the resulting weighted sums
   with `Z(σ+uε)/Z(σ)`, `A(σ+uε)/A(σ)` and their logarithmic derivatives — pure arithmetic now, the
   measure-theoretic carrier is built.  The scalar limits are already proved in
   `RHTower/MobiusFixedCurrentVonMangoldt.lean`.
2. DONE — see above.
3. Then (14) follows from the criterion above with the proved moment input (13).
4. W₂ and (15a)–(15c), the four-unit Gini law (16)–(17), packet isometry (18)–(22).

Only item 1 (instantiating the two clock laws and identifying their weighted sums with the
Dirichlet quotients) still gates (14)–(15); everything else is proved.
