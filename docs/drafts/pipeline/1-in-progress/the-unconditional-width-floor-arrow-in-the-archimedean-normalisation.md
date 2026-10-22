# The unconditional width→floor arrow in the archimedean normalisation

- **ID:** width-floor-archimedean
- **Stage:** 1-in-progress
- **Type:** TARGET (discharge of `OffLineDepthLocallyBounded` / `OffLineDensityBound`)
- **Source:** `SquareRootThreshold.exists_ccmRestrictedWeilGroundEnergy_ge_neg_exp_of_offLineDepthLocallyBounded`
  (conditional); `RHTower.ErrorExponentAbscissaExcessLaw.abs_re_sub_half_le_iff_eventually_relaxed`
  (conditional on `OffLineDensityBound`); the unconditional local count
  `RHTower.card_le_of_ordinates_in_window`, `Nd_le_of_local_count`,
  `offLineDensityBoundBelow_of_local_count`.

## Target
For every `σ > zetaZeroWidth` there is `C` with

`Ẑ(F) ≥ −C e^{2σA} (∫F² + 𝒥(F))`

for every `C²_c` test `F` of aperture `A`, where `𝒥` is the Weil functional's own archimedean
Lévy energy (`biScaleLevyEnergy`), **with no hypothesis on the distribution of the zeros**.

This discharges the corpus's standing conditional input in the Weil-floor lane. The hypothesis
is not available unconditionally: `exists_unsignedDepthSamplingBound_iff` makes
`OffLineDepthLocallyBounded W` equivalent to an unsigned sampling bound at one aperture, and the
unconditional local count only gives the height-dependent `W(T) ≍ log T`.

## Why the archimedean normalisation is the right one
Three independent computations land on the same weight `log(2+|ξ|)`:

1. **Zero side.** Replacing the uniform window bound `W` by the unconditional count `≍ log T`
   turns the uniform weight of the sampling inequality into the weight `log(2+|ξ|)` against
   `|F̂|²`, which is `𝒥(F) + O(∫F²)` (two-sided digamma bounds for the arch symbol).
2. **Prime side.** The discrepancy transform gives the pairing at frequency `ξ` as
   `s(ξ)·Ê_L(ξ)` plus bounded terms with `s(ξ) = ½ + 2πiξ`
   (`gaugeDerivative_frequencyCharacter`, `fourierPairing_eq_discrepancy_transform`); the true
   size of the combination is `Re(−ζ′/ζ)(½+iξ) ≍ log|ξ|`, so the honest spectral bound is again
   the log weight.
3. **Smoothness.** For a `C²_c` test the transform decays like `|ξ|^{-2}`, so the high-zero tail
   is finite for each test but only `H²`-uniformly over the class; the `L²`-normalised infimum is
   precisely what has no such uniformity.

Since `riemannHypothesis_of_subexponential_odd_floor` tolerates any subexponential-in-aperture
defect, and the frequency — hence the log — is bounded along a fixed-shape test family, a floor
with this normalisation is as good as the exact one for every downstream use in the corpus.

## Two routes, with the owned inputs named
**Route A (zero side): a log-weighted sampling inequality.** Extend
`IntervalSourceTransformsSampledOnLocallyBoundedPoints` to a weight: for `f` vanishing off
`[−a,a]`, points `x_q + iy_q` with `|y_q| ≤ σ`, and `≤ A₀ log(|x|+3)` heights per unit window,

`Σ_q |Φ(x_q+iy_q)|² ≤ C(a) e^{2σa} (∫|f|² + ∫|f̂(ξ)|² log(2+|ξ|) dξ)`.

The unweighted case is owned (power series in the moment transforms, weighted Cauchy–Schwarz,
cell count, grid Parseval `hasSum_norm_sq_paperFT_grid`). What is missing is the comparison of a
log-weighted grid sum with the log-weighted integral for a transform of exponential type `a`
(Plancherel–Pólya with a slowly varying weight) — not owned, and the main new analysis.
Dyadic shells do not shortcut it: the owned inequality returns the full mass for each shell.

**Route B (prime side): spectral domination from the sharp log-derivative bound.** Prove
`|Re ν̂_A(ξ)| ≤ C e^{2σA} (1 + log(2+|ξ|))` for the windowed prime–polar measure at aperture `A`,
then integrate against `|F̂|²`. Owned inputs: the sharp Landau bound for `ζ′/ζ`
(`ZetaLogDerivSharpLandau`), Hadamard positivity in the strip, two-sided digamma. Missing: a
truncated explicit formula on the critical line with error uniform in `ξ` — the classical step,
and the one that makes the `|s(ξ)| ≍ |ξ|` of the gauge transport collapse to `log|ξ|`.

Route B is the shorter mathematical path and uses only the critical-line analytic toolkit;
Route A is self-contained but needs a genuinely new sampling inequality.

## Route A: first component built
`formal/GaloisForLFunctions/HTGeometry/LocalSamplingForCompactlySupportedSources.lean`
(unconditional, standard axioms, wired into `GaloisForLFunctions.HTGeometry`) supplies the
**localised** sampling bound that the owned global inequality lacks:

* `trapFn a = (2a)⁻¹(1_{[−a,a]} ⋆ 1_{[−2a,2a]})` — the trapezoidal cutoff, `≡ 1` on `[−a,a]`
  (`trapFn_eq_one`), supported in `[−3a,3a]`, continuous and integrable;
* `sampKernel a = 𝓕(trapFn a)` — by the convolution theorem the product of two box transforms,
  with `‖sampKernel a x‖ ≤ (8a + a⁻¹)/(1+x²)` (`norm_sampKernel_le`, from `|𝓕 1_{[−p,p]}| ≤
  min(2p, (π|x|)⁻¹)`), hence integrable with mass `≤ (8a + a⁻¹)π`
  (`integral_norm_sampKernel_le`);
* `fourier_eq_integral_mul_sampKernel` — the reproducing identity `Φ = Φ ⋆ G_a` for any integrable
  `f` vanishing off `[−a,a]`, proved from Fourier self-adjointness
  (`VectorFourier.integral_fourierIntegral_smul_eq_flip`) plus inversion for the cutoff, so no
  Fubini bookkeeping is needed;
* `norm_sq_fourier_le_integral` — `‖Φ(x₀)‖² ≤ (8a + a⁻¹)π · ∫ ‖G_a(x₀−x)‖ ‖Φ(x)‖² dx`, by the
  owned weighted Cauchy–Schwarz (`HTGeometry.sq_integral_weighted_le`).

`formal/GaloisForLFunctions/HTGeometry/LogarithmicDensitySamplingSums.lean` (unconditional,
standard axioms, wired into `GaloisForLFunctions.HTGeometry`) supplies the second component — the
`ℤ`-sum estimate that says a **logarithmic density is reproduced, not amplified**, by a kernel of
quadratic decay:

* `exists_bound_tsum_log_kernel` — `∃ C ≥ 0, ∀ x, Σ_{n ∈ ℤ} log(|n|+3)(1+(n−x)²)⁻¹ ≤ C log(|x|+3)`;
* ingredients: `log_abs_add_three_le` (submultiplicativity `log(|n|+3) ≤ log(|x|+3)+log(|n−x|+3)`),
  `log_le_two_mul_sqrt`, the comparison series `seriesTerm k = log(k+4)(1+(k−1)²)⁻¹` with
  `summable_seriesTerm` (via `16 k^{-3/2}`), its `ℤ`-indexed double `domTerm` with
  `tsum_domTerm_le`, and the one-unit reduction `log_kernel_frac_le` after translating by `⌊x⌋`.

`formal/GaloisForLFunctions/HTGeometry/LogDensityPlancherelPolya.lean` (unconditional, wired)
supplies the third component — **Plancherel–Pólya with a logarithmic weight**:
`sum_norm_sq_fourier_le`, for `f` supported in `[−a,a]` and a finite point set with at most
`A₀ log(|n|+3)` points per unit window,

`Σ_{x ∈ T} ‖Φ(x)‖² ≤ ((8a+a⁻¹)π)((8a+a⁻¹)·3A₀·logKernelConst) ∫ ‖Φ(y)‖² log(|y|+3) dy`,

with `sum_kernel_le` (a logarithmic density is reproduced by the kernel) and `kernel_window_le`
(one unit window costs a factor three) as the intermediate steps.

**What remains for Route A.**
1. The counting interface: feed `RHTower.card_le_of_ordinates_in_window` through
   `ZeroConfig.N t (t+1)` to get the per-unit-window count, matching the shape of step 1.
3. The depth direction `|Im z| ≤ σ` needs **no** multiplier comparison: the reproducing identity
   holds verbatim at a complex point with the kernel evaluated there,
   `Φ(z) = ∫ Φ(y) 𝓕T(z − y) dy` (Fubini plus Fourier inversion for `f`), and the box transforms
   obey `|S_p(w)| ≤ min(2p, (π|Re w|)⁻¹) e^{2πp|Im w|}`, so
   `|𝓕T(z−y)| ≤ e^{6πa|Im z|}(8a + a⁻¹)/(1 + (Re z − y)²)`. The right-hand side still involves
   only `Φ` on the real line, so the log-weighted energy of `Φ` is the only datum.
4. Assemble into the archimedean-normalised floor and discharge
   `OffLineDepthLocallyBounded` / `OffLineDensityBound` in the Weil-floor lane. The owned
   conditional floor `RHTower.re_W_ge_of_depth_offLineDensity` uses the uniform density `D` only
   through the Gram row sums (`window_tsum_inv_sq_le`); the weighted sampling inequality replaces
   that step, with the depth differences handled by
   `|Φ(z) − Φ(z̄)|² ≤ 2(|Φ(z)|² + |Φ(z̄)|²)`.

## Already in hand
`SquareRootThreshold.TheWidthBoundsTheEnergyNormalisedWeilFloor` (card
`3-formalized/width-to-floor-arrow-unconditional-in-the-energy-normalisation.md`): the same arrow
unconditionally, but normalised by `∫F² + sup|a′ − a/2|` — an `H¹` datum, a full power of the
frequency where the target has its logarithm. That module's Chebyshev-gauge bound
(`abs_fullPairing_autocorr_le`) is the skeleton Route B refines: everything except the sup bound
on `Ẽ·(a′ − a/2)` is reusable verbatim.

## Gates
- [x] 0 → 1  in-progress
- [ ] 1 → 2  fully-proven on paper
- [ ] 2 → 3  formalized
- [ ] 3 → 4  publication-ready

## Log
- 2026-10-22 — created; target and both routes scoped, owned inputs named, the `H¹`-normalised
  version formalised as the fallback.
- 2026-10-22 — Route A's first component built and wired: localised sampling bound with an
  explicit kernel of quadratic decay and explicit mass.
- 2026-10-22 — Route A's second component built and wired: the logarithmic density is reproduced,
  not amplified, by the kernel (`exists_bound_tsum_log_kernel`). Remaining: the counting interface,
  the depth direction, and the assembly.
