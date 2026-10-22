# The Weil floor in the archimedean normalisation, with no zero-distribution hypothesis

- **ID:** width-floor-archimedean
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) — discharge of `OffLineDepthLocallyBounded` / `OffLineDensityBound`
- **Source:** `SquareRootThreshold.exists_ccmRestrictedWeilGroundEnergy_ge_neg_exp_of_offLineDepthLocallyBounded`
  (conditional); `RHTower.ErrorExponentAbscissaExcessLaw.abs_re_sub_half_le_iff_eventually_relaxed`
  (conditional on `OffLineDensityBound`); the unconditional local count
  `RHTower.card_le_of_ordinates_in_window`, `Nd_le_of_local_count`,
  `offLineDensityBoundBelow_of_local_count`.

## Result
`exists_re_W_ge_logWeighted` (in
`formal/GaloisForLFunctions/SquareRootThreshold/TheUnconditionalWeilFloorInTheArchimedeanNormalisation.lean`,
wired into `GaloisForLFunctions.SquareRootThreshold`, standard axioms): for every `a > 0` there is
`C ≥ 0` with

`Re W(f, f) ≥ −C ∫ ‖𝓕 f(y)‖² log(|y| + 3) dy`

for every `C²` test `f` supported in `[−a, a]` (with `𝓕 f` and the weighted energy integrable),
**with no hypothesis on the distribution of the zeros**.

This discharges the corpus's standing conditional input in the Weil-floor lane. That hypothesis is
not available unconditionally: `exists_unsignedDepthSamplingBound_iff` makes
`OffLineDepthLocallyBounded W` equivalent to an unsigned sampling bound at one aperture, and
`ErrorExponentAbscissaExcessLaw.abs_re_sub_half_le_iff_eventually_relaxed` still needs a uniform
`OffLineDensityBound`; the unconditional local count only gives the height-dependent `W(T) ≍ log T`,
and the archimedean weight `log(|y|+3)` is exactly what that height dependence becomes.

**The zero-side inputs are only two:** the unconditional window count
`Zeta23.RvM.zetaZeroConfig_local_count` (through `Zeta23.Tail.LocalCount.ofWindowCount`) and the
strip `0 ≤ β ≤ 1` (which bounds the depth of the sample points by `1/(4π)`). Of the Weil summand
only `Re(u \bar v) ≥ −(|u|² + |v|²)/2` is used, so on-line and off-line zeros are treated alike.

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

**What remains for the sharp rate.**
0. The floor's constant carries `e^{6πaσ}` with `σ = 1/(4π)` from the strip; with the width `w` in
   place of `½` the exponent reads `3aw` where the dictionary's rate is `2aw`. The loss is the
   trapezoid's support radius `3a`: replacing `T_a` by `(2δ)⁻¹(1_{[−a−δ,a+δ]} ⋆ 1_{[−δ,δ]})` makes
   the radius `a + 2δ` and the rate `2(a+2δ)w → 2aw`, at the price of a constant `≍ δ⁻¹`. Only
   then does the floor compose with `zetaZeroWidth_le_of_graded_odd_fullZeroForm_floor` to read the
   width in the dictionary's unit.
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

## Where this sits in the programmes' own units
* **`SquareRootThreshold` research topic 8** asks for the `L²`-normalised width arrow: mechanism 31
  proves `width < β ⟹` floor at rate `2β` with an `H¹` datum, and the `L²` form "needs a bound on
  the off-line zeros in a single unit-height window". This card moves the normalisation from the
  `H¹` datum (a full power of the test's frequency) to the **archimedean weight** `log(|y|+3)` — its
  logarithm — and removes the zero-side hypothesis entirely: the only input is the unconditional
  window count. The residual is now exactly "replace `log` by `1`", i.e. the single-window input
  that research topic 8 names, and the log is not an artefact: it *is* the unconditional local
  count.
* **`ArithmeticContinuationAndCriticalEnergy` open problem 7** asks whether the actual source forces
  `E_−(u) ≤ E_+(u) + C_σ e^{2σA}‖u‖₂²` without a local depth-mass hypothesis. This card bounds the
  whole zero side (hence `E_−`) by `C e^{6Aσ}` times the log-weighted energy, with no depth-mass
  hypothesis; it does not compare `E_−` with `E_+`, so the open problem stands.
* **Selectivity, stated as the shared criteria require.** The *inequality* is nonselective: its
  proof uses only the logarithmic window count and the strip, both of which a Beurling system with
  an off-line zero satisfies, so it holds verbatim there — as `ScaleSignedIncidenceCriticality`
  requires of any floor whose loss grows with the frequency of the test. The *rate* is selective and
  faithful: `exists_re_W_ge_logWeighted_rate` has rate `6 a · zetaZeroWidth`, which vanishes exactly
  under RH and is `6aδ` for a configuration with an off-line zero of depth `δ`. This is the rate
  reading the admissibility layer calls the faithful one (`SSIC` §3.5), and the factor `6` against
  the faithful `2` is the trapezoid radius (see the sharpening below).

## Lean (unconditional, standard axioms only)
- `HTGeometry/LocalSamplingForCompactlySupportedSources.lean`: `trapFn`, `sampKernel`,
  `norm_sampKernel_le`, `integral_norm_sampKernel_le`, `fourier_eq_integral_mul_sampKernel`,
  `norm_sq_fourier_le_integral`.
- `HTGeometry/LogarithmicDensitySamplingSums.lean`: `summable_seriesTerm`, `summable_log_kernel`,
  `exists_bound_tsum_log_kernel`.
- `HTGeometry/LogDensityPlancherelPolya.lean`: `kernel_window_le`, `sum_kernel_le` (weighted,
  indexed), `sum_norm_sq_fourier_le`.
- `HTGeometry/ComplexLocalSamplingAtDepth.lean`: `boxTransform` and its two bounds,
  `sampKernelAt_eq` (complex-frequency product formula, by Fubini),
  `norm_sampKernelAt_le`, `fourierAt_eq_integral`, `sum_norm_sq_fourierAt_le`.
- `SquareRootThreshold/TheUnconditionalWeilFloorInTheArchimedeanNormalisation.lean`:
  `paperFT_eq_fourierAt`, `spectralSample_re/_im`, `exists_count_spectralSample` (nine unit
  ordinate windows per unit sample window), `abs_spectralSample_im_le`, `re_Wsummand_ge`, and the
  three floors — `exists_re_W_ge_logWeighted_of_depth` (rate `12πaσ` at any depth bound `σ`),
  `exists_re_W_ge_logWeighted` (unconditional, `σ = 1/(4π)` from the strip) and
  `exists_re_W_ge_logWeighted_rate` (rate `6 a · zetaZeroWidth`).

## The normalisation is the growth of the off-line count
The on-line zeros are free: their Weil summands are nonnegative
(`re_Wsummand_nonneg_of_onLine`, owned by `HodgeClassificationOfFiniteOffLineSets`), so only the
off-line zeros need to be sampled. Restricting the sampling to them makes the per-window weight the
**off-line** count, and the whole chain then interpolates in one parameter — the growth of that
count:

| per-window off-line weight | kernel sum | floor's normalisation |
|---|---|---|
| `≤ D` (uniform) | `≤ 3D·kernelConst` | `∫‖𝓕f‖²` — plain `L²` |
| `≤ A₀ log(|n|+3)` | `≤ 3A₀·logKernelConst·log(|y|+3)` | `∫‖𝓕f‖² log(|y|+3)` — archimedean |

Both instances are now in Lean: `sum_kernel_le_const` and `exists_bound_tsum_kernel` (the unweighted
uniform kernel bound) give `sum_norm_sq_fourierAt_le_const`, and
`exists_re_W_ge_l2_of_offLineDensity` is the `L²` end. **Honest standing of that end:** it
re-derives the owned `RHTower.re_W_ge_of_depth_offLineDensity` by the sampling route, with a worse
constant (rate `6aσ` against `2aσ`, the trapezoid radius again), so it is a second proof and not a
new theorem. What is new is the interpolation itself: it identifies the answer to research topic 8's
question — which single-window input replaces averaged zero density — as *the off-line count, and
nothing else*, with the floor's weight equal to that count's growth. Since the off-line count
vanishes under RH, the whole family is selective, unlike the inequality at the trivial depth.

## The depth-weighted substitution, and why the logarithm is irreducible
Tested and negative, with the reason. The crude term bound `Re(u \bar v) ≥ −(|u|² + |v|²)/2` throws away the depth. The sharp bound is
`Re(u \bar v) ≥ −|u − v|²/4` with `|u − v| ≲ δ_ρ · sup|∂û|` for a zero of depth `δ_ρ`, so the
sampling weight becomes `m_ρ δ_ρ²` instead of `m_ρ`. The weighted kernel sum `sum_kernel_le` already
accepts an arbitrary nonnegative weight, so the whole chain carries that substitution — and
`m_ρ δ_ρ²` per unit window is exactly what the unsigned sampling law
(`UnsignedDepthSamplingDetectsLocalMass`, SRT mechanism 33) controls. If the depth-weighted count is
bounded where the plain count is only logarithmic, the `log` disappears and the floor becomes
`L²`-normalised — which is research topic 8. The substitution itself goes through: `∂û` is the
transform of `−2πi t f(t)`, again a source supported in `[−a, a]`, so the whole toolchain applies to
it verbatim, and `|û(x+iy) − û(x−iy)| ≤ 2|y| sup|∂û|` turns the weight into `m_ρ δ_ρ²`.

**But the logarithm does not drop.** The quantity that then has to be bounded per unit window is the
depth mass `Σ_window m_ρ (Re ρ − ½)²`, and the unconditional bound for it is itself logarithmic —
`≤ 40 w² log(180T)` from `RHTower.card_le_of_ordinates_in_window` — so the substitution multiplies
the floor by `width²` and leaves the `log` where it was. A depth-mass bound *uniform* in the height
is exactly `OffLineDepthLocallyBounded`, which `exists_unsignedDepthSamplingBound_iff` shows is
equivalent to an unsigned sampling bound and is not available. So the logarithm in this card is not
an artefact of the crude term bound: it is the unconditional local count itself, in whichever weight
the term bound is written. The single-window input that research topic 8 asks for cannot be
manufactured from the count, and the depth weighting identifies precisely which form of it suffices:
`Σ_window m_ρ (Re ρ − ½)² ≤ C` with `C` free of the height.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven on paper
- [x] 2 → 3  formalized
- [ ] 3 → 4  publication-ready

## Log
- 2026-10-22 — created; target and both routes scoped, owned inputs named, the `H¹`-normalised
  version formalised as the fallback.
- 2026-10-22 — Route A's first component built and wired: localised sampling bound with an
  explicit kernel of quadratic decay and explicit mass.
- 2026-10-22 — Route A's second component built and wired: the logarithmic density is reproduced,
  not amplified, by the kernel (`exists_bound_tsum_log_kernel`).
- 2026-10-22 — the weighted Plancherel–Pólya inequality, its complex-frequency (depth) version,
  the counting interface and the Weil assembly are all built: `exists_re_W_ge_logWeighted` is the
  unconditional floor. Stage 3. The remaining item is the sharp rate (item 0 above).
