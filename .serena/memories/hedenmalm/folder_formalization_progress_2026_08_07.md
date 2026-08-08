# Hedenmalm folder → stage 3: progress log (2026-08-07).  NOT FINISHED — 3 of 9 moved.

Goal: formalize in Lean every proven statement of the 9 cards in
`docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/hedenmalm/`, then `git mv` each to
`3-formalized/new_scientific_knowledge/hedenmalm/` with an `<id>-formalized.md` companion.

## CHECK THESE CORPUS ASSETS BEFORE BUILDING ANYTHING
- `ContinuousLinearMap.IsHilbertSchmidt` — `HTGeometry/HilbertSchmidtOperator.lean:198`
- `IsHilbertSchmidt.isCompactOperator` — `HTGeometry/HilbertSchmidtCompact.lean:164`
- **`RHTower.isHilbertSchmidt_kernelOperator`** — `RHTower/SoninTimeBandHilbertSchmidt.lean:69`.
  Use for card 7 `(1)`.
- Determinants: only the DIAGONAL layer (`RHTower/ArithmeticDilationDeterminantZeros.lean`).
- `HTGeometry.LogarithmicResidueQuantization.logDeriv_residue_of_meromorphicOrder`
- `HTGeometry.QuantileCoupling.map_quantile_eq`; `MeasureTheory.lpBoundedMulCLM`

## IN STAGE 3 (3 cards + companions)
`hedenmalm-quantile-volterra-universal-boundary-defect` (all `(1)`–`(16)`),
`hedenmalm-reflection-folded-dirac-source-defect`, `hedenmalm-theta-flat-borel-holonomy-law`.

## STILL IN STAGE 2 — exact remaining items

### 4. `prime-translation-rank-one-anomaly` — OWN CONTENT COMPLETE `(3)`–`(18)`
Modules `HedenmalmPrimeTranslationAnomaly.lean`, `HedenmalmThetaSeriesExpansion.lean`.
ONLY BLOCKER: Jordan-length sentence of `(16)` cites card 7's analytic Fredholm multiplicity.

### 5. `two-prime-theta-interval-normal-frame` — `(3)`,`(4)`,`(5)`-mult,`(5a)`,`(6)`,`(7)` + two-prime
Module `RHTower/HedenmalmIntervalAnomaly.lean`:
`intervalMass`, `mass_mul_cdfFun_sub`, `integerAnomaly_eq_intervalMass` (4),
`intervalMass_add`, `integerAnomaly_mul` (5a),
`intervalMass_pos`, `centeredWindow`, `centeredWindow_eq`, `centeredWindow_pos`,
`cdfFun_neg`, `intervalMass_neg`, `centeredWindow_neg` (6),
`shiftMultiplier`, `shiftMultiplier_eq_zero_iff` (5-multiplier),
`centeredMultiplier`, `centeredMultiplier_eq`, `centeredMultiplier_eq_zero_iff` (7),
`pow_three_ne_pow_two`, `eq_zero_of_log_three_eq_log_two`, `no_common_zero_two_three`,
`no_common_zero_centered_two_three` (the headline two-prime theorem).
REMAINING: the factorization `hat r_n = q_n Ξ_C` (Fubini against the interval indicator:
`∫ r_n(x)e^{izx}dx = i n^{-1/2}∫∫ k(t)1_{t-L≤x<t}e^{izx}dx dt`), rapid decrease of `(6)`,
conormal generation, the two bounded self-adjoint channels, the essential compact-boundary symbol,
and the three frame obstructions (bounded corona, finite prime, summable all-prime).

### 6. `supersymmetric-fredholm-range-divisor` — range-divisor half done
`RHTower/HedenmalmFredholmRangeDivisor.lean`: `(5)`, `(6)`, `(7)`.
REMAINING: `(3)` weighted adjoint, `(4)` closedness + index `-1`, compact resolvent,
`(8)` Witten square, `(9)` supersymmetric Dirac, `(10)` strict positivity.
Needs an unbounded-Fredholm layer; mathlib has only `LinearPMap.adjoint`.

### 7. `theta-source-compressed-inverse-determinant` — `(4)`,`(5)`,`(6)`-pt-spectrum,`(7)` done
`RHTower/HedenmalmHilbertSchmidtNorm.lean`: `pinnedKernelSlice`,
`integral_pinnedKernelSlice_sq`, `tailEnergyDensity`, `integral_quantileSpeed_sq_slice` (5),
`sourceReflection`, `sourceInverse_sourceReflection` (7),
`xiC_eq_zero_of_solution_const` (6⟹), `sourceInverse_sourceModeF_eq_smul` (6⟸),
`sourceEvaluation_k` (Grushin scalar corner).
REMAINING: `(1)` assembled HS operator (use `isHilbertSchmidt_kernelOperator`);
`(6)` **multiplicity clause** — analytic Fredholm multiplicity + Grushin reduction to
`diag(I, Ξ_C)`; unblocks card 4.  `(8)` `det₂`.  `(9)` `tr(B²)` = variance
(2-D Fubini: `∫∫_{x<y}p(x)(1-p(y)) dxdy = E[(X-X')²]/4`).

### 8. `essential-inverse-flow-prime-tomography` — none; punctured Riesz trace, von Mangoldt weld.
### 9. `pair-weil-polarization-law` — one gate: Guinand–Weil test algebra in closed form.

## Recommended next order
card 5 remainder → card 9 → card 7 `(9)` → card 8 → then the three foundational builds
(analytic Fredholm multiplicity, `det₂`, unbounded Fredholm), which are the only genuinely large
pieces left.

## Modules created this session (14, all wired, all axiom-clean, all building)
`HTGeometry/`: `WeightedDensityL2`, `PositiveDensityQuantile`, `BoundedMultiplierHilbert`.
`RHTower/`: `HedenmalmQuantileNormalForm`, `HedenmalmQuantileMetric`,
`HedenmalmQuantileBoundaryFlux`, `HedenmalmQuantileRootMode`, `HedenmalmQuantileDivisorCharge`,
`HedenmalmPrimeTranslationAnomaly`, `HedenmalmFredholmRangeDivisor`,
`HedenmalmThetaSeriesExpansion`, `HedenmalmHilbertSchmidtNorm`, `HedenmalmIntervalAnomaly`.

## Lean traps (v4.32)
- `AEStronglyMeasurable.div` needs `ContinuousDiv` (absent for ℂ) — `mul` + `Continuous.inv₀`.
- `field_simp` needs the `≠ 0` hypothesis in context; check whether a trailing `ring` is needed.
- Derivatives of `‖·‖²`: stay in ℂ (`HasDerivAt.star`, `conj w * w = ((‖w‖^2:ℝ):ℂ)`).
- `star` vs `starRingEnd ℂ`: defeq — `show` converts, `rw` does not.
- `Integrable.star` does not exist; `⟨conj∘f measurable, h.2.congr'⟩`.
- `Set.uIcc_subset_Ioo` does not exist — `Set.ordConnected_Ioo.uIcc_subset`.
- `rw [someDef]` fails for defs applied to arguments — use `show`.
- `integral_add_right_eq_self`, `Integrable.comp_add_right`, `integral_neg_eq_self` need
  `(μ := volume)` or explicit ascriptions.
- Annotate integral binders `∫ x : ℝ, …` when the integrand casts `x` to ℂ.
- Improper FTC: `integral_Iic_of_hasDerivAt_of_tendsto'`, `integral_of_hasDerivAt_of_tendsto`.
- Half-line change of variables: `integral_image_eq_integral_abs_deriv_smul` +
  `HedenmalmThetaSeries.image_expChart`/`injOn_expChart`.
- Termwise integration: `MeasureTheory.integral_tsum`.
- `Measure.integrableOn_of_bounded` names its bound `M`; `setIntegral_const` yields `Measure.real`.
- `Real.exp_injective` breaks dependent elimination — `Real.exp_eq_exp.mp` + `mul_left_cancel₀`.
- `Nat.pos_iff.mp` does not exist — use `h.ne'`.
- `simp` rewrites `((Real.log ((3:ℕ):ℝ) : ℝ) : ℂ)` into `Complex.log 3`; go through
  `Complex.ofReal_inj` instead when moving a real identity out of ℂ.
- **`linear_combination` against `hI : I*I = -1`: never guess the coefficient.  Read the residual
  goal, factor it as `c · (I² + 1)`, and use `c`.**  Same for `hexp`-style side relations.
- Bash cwd persists; `cd formal` once, and re-`cd` after any `cd` to the repo root.

## Update — unconditional instantiation built (2026-08-07, later)

New module `formal/GaloisForLFunctions/RHTower/HedenmalmThetaSourceUnconditional.lean`
(wired into `RHTower.lean`, compiles clean).  It closes the "everything is stated over a
hypothesis class" objection:

- `thetaCuspFullSource_pos : ∀ x, 0 < thetaCuspFullSource x`  (new global positivity: `>0` half
  from `thetaCuspFullSource_pos_of_pos`, `<0` half from `thetaCuspFullSource_neg`, seam from
  `thetaCuspFullSource_zero_pos_for_cold_seam`).
- `thetaSource : PositiveDensitySource` — k := `thetaCuspFullSource`,
  continuity from `contDiff_thetaCuspFullSource`, integrability from `thetaCuspSchwartzReal`.
- `thetaSource_even`, `thetaBound := thetaCuspDerivativeExpConstant 0`, `thetaSource_le`,
  `tendsto_thetaSource_atBot/atTop`.
- `hasShiftedTail_thetaSource : |z.im| < 1 → HasShiftedTail thetaSource z`.
- `xiC_thetaSource : |z.im| < 1 → xiC thetaSource z = XiC z`
  (via `thetaCuspFourierLaplace_eq_XiC_on_strip` at `-z`, then `XiC_even`).
- `thetaMetricOperator` + `denseRange_thetaMetricOperator`,
  `not_boundedBelow_thetaMetricOperator`, `inner_thetaMetricOperator_quantileUnitary`.
- Unconditional card forms: `sourceInverse_sourceReflection_theta` (RBR = -B),
  `XiC_eq_zero_of_solution`, `sourceModeI_eq_neg_tail_iff_XiC`, `sourceModeI_neg_theta`,
  `intervalMass_neg_theta`, `centeredWindow_neg_theta`.

Card 7 statement (1) chain finished in `HedenmalmHilbertSchmidtNorm.lean`:
`norm_sq_pinnedSliceVec`, `pinnedKernelField`, `pinnedKernelField_apply`,
`norm_pinnedKernelField`, `continuousOn_quantileSpeed`, `continuousOn_pinnedKernelField`,
`aestronglyMeasurable_pinnedKernelField`, `HasFiniteKernelEnergy`, `memLp_pinnedKernelField`,
`pinnedKernelL2`, `isHilbertSchmidt_pinnedKernelOperator`,
`isCompactOperator_pinnedKernelOperator`.

### The one remaining analytic obligation of statement (1)
`HasFiniteKernelEnergy thetaSource`, i.e. `∫₀¹ q² t(1-t) dt = M ∫ p(1-p)/k < ∞`.
PROVEN ROUTE (elementary, no Gamma integrals needed), for x ≥ 1:
1. upper: `k(y) ≤ (1+W)·4π² e^{9y/2} e^{-π e^{2y}}` for y ≥ 0
   (`thetaCuspFullSource_sub_first_le` + `2πt⁴ - 3t² ≤ 2πt⁴`).
2. lower: `k(x) ≥ 2π² e^{9x/2} e^{-π e^{2x}}` for x ≥ 0
   (term₁ ≤ tsum since all terms ≥ 0, and `2πe^{4x} - 3e^{2x} ≥ π e^{4x}` for x ≥ 0).
3. convexity `e^{2y} ≥ e^{2x}(1 + 2(y-x))` for y ≥ x, so
   `e^{-πe^{2y}} ≤ e^{-πe^{2x}} e^{-2π e^{2x}(y-x)}`.
4. for x ≥ 1, `2πe^{2x} - 9/2 ≥ πe^{2x}`, so `∫_x^∞ k ≤ C e^{9x/2}e^{-πe^{2x}}/(π e^{2x})`.
5. divide: `(1-p(x))/k(x) ≤ C' e^{-2x}` on `[1,∞)`; evenness gives `[-∞,-1]`; the middle is
   continuous on a compact.
Do NOT try `k = H'` in closed form — the elementary primitive leaves a `+1/4 e^{x/2}θ̃` residue
(this is the `(D² - 1/4)` of the reflection law), so it does not close.

## Card 7 statement (1) is CLOSED and UNCONDITIONAL (2026-08-07)

`formal/GaloisForLFunctions/RHTower/HedenmalmThetaKernelEnergy.lean` (wired, builds, axiom-clean).
The route recorded above was executed exactly and works:
`thetaEnvelope x = e^{9x/2} e^{-π e^{2x}}`; `thetaEnvelopeUpper/Lower`;
`thetaCuspFullSource_le_envelope` (x ≥ 0), `thetaCuspFullSource_ge_envelope` (x > 0),
`thetaEnvelope_le_shift`, `thetaCuspFullSource_le_shift`,
`integral_Ioi_exp_neg_shift` (= 1/a, by improper FTC), `integral_Ioi_thetaCuspFullSource_le`,
`one_sub_cdfFun`, `tailEnergyDensity_le` (≤ C e^{-2x} on [1,∞)), `tailEnergyDensity_neg`
(evenness), `tailEnergyDensity_le_abs`, `integrable_tailEnergyDensity_thetaSource`,
`hasFiniteKernelEnergy_thetaSource`, `isHilbertSchmidt_thetaKernelOperator`,
`isCompactOperator_thetaKernelOperator`.

Traps hit: `div_le_div` is now `div_le_div₀`; `IntegrableOn.congr_fun` needs the fully qualified
name once the term came from `Integrable.const_mul`; `Tendsto.congr` goals carry `id t`, so `ring`
fails — use `simp [sub_eq_add_neg]`; `field_simp` often closes the goal, so a trailing `ring`
becomes "no goals".

Card 7 remaining: (6) multiplicity clause (analytic Fredholm multiplicity + Grushin reduction to
diag(I, Ξ_C)) — this is what card 4 (16) cites; (8) det₂ (absent from corpus AND mathlib);
(9) tr(B²) = M⁻¹∫x²k.

## Card 5 statements (5) and (7) CLOSED and UNCONDITIONAL (2026-08-07)

`formal/GaloisForLFunctions/RHTower/HedenmalmThetaIntervalTransform.lean` (wired, builds,
axiom-clean).  `hat r_n = q_n Ξ_C` and `hat c_n = a_n Ξ_C` for the actual theta source, on
|Im z| < 1, z ≠ 0.  Do NOT use 2-D Fubini: the working route is ONE integration by parts on the
line with `integral_of_hasDerivAt_of_tendsto`, using
`W_L(x) = ∫_x^{x+L} k`, `W_L' = k(·+L) − k`, boundary terms killed by
`intervalMass_le_exp : W_L(x) ≤ (L·thetaBound·e^L)·e^{−|x|}`.
The corpus already owned `shiftMultiplier` and `centeredMultiplier` with exactly the right
shapes — do not redefine them.

Traps: `HasDerivAt.comp` refuses to unify the composition point here — use
`HasDerivAt.comp_add_const x L h`.  `abs_add` is gone; use `abs_sub_abs_le_abs_sub`.
`integrableOn_const` now takes autoParams — use `Measure.integrableOn_of_bounded` instead.
`Continuous.congr` leaves a `Function.comp` redex — insert `show`.
For `linear_combination` after this integration by parts the coefficient is **+1**, not −1.

## Card 5 statements (7 closed form), (11), (15), (16), (18)-(20) CLOSED (2026-08-07)

`formal/GaloisForLFunctions/RHTower/HedenmalmTwoPrimeNormalFrame.lean` (wired, builds,
axiom-clean).  KEY SIMPLIFICATION: do NOT formalize (15)/(16) as jet identities via a Leibniz
rule.  mathlib's `analyticOrderAt` + `analyticOrderAt_mul` +
`AnalyticAt.analyticOrderAt_eq_zero` give the sharper statement directly:
`analyticOrderAt (a_n * XiC) ζ = analyticOrderAt XiC ζ` whenever `a_n ζ ≠ 0`.
Combined with `no_common_zero_centered_two_three` and `XiC_zero_ne` this is
`two_prime_retains_divisor`.

Also: `centeredMultiplier_eq_sin`, `analyticAt_centeredMultiplier`, `compactNormalMultiplier`,
`compactNormalMultiplier_eq` (NO outer minus sign — the two sign flips cancel),
`compactNormalMultiplier_root` (needs no hypothesis: `inv_neg`+`inv_inv`+`neg_neg`).

Trap: after `rw [e1]` a later `-(...)` has ALREADY been rewritten, so a second equation for the
negated form is dead; state the sine lemma with `-(w * I)` and normalise inside its own proof.

Card 5 remaining: (13)/(14) conormal generation — needs Wedderburn/Cartan B for entire functions
(two entire functions with no common zero generate the unit ideal).  ABSENT from corpus and
mathlib; this is the real blocker.  Then (17) cokernel rests on (14); plus the two self-adjoint
convolution channels and the three frame obstructions.

## Card 6 statements (11) and (12) CLOSED and UNCONDITIONAL (2026-08-07)

`formal/GaloisForLFunctions/RHTower/HedenmalmWeightedAdjointCore.lean` (wired, builds,
axiom-clean).  `integral_weighted_symmetry` = the weighted formal symmetry
`<D f, g>_{H_k} = <f, L g>_{H_k}`, `L = D + i k'/k`, on compactly supported differentiable data;
`hasDerivAt_halfDensity_mul` = the half-density conjugation `(k^{1/2}f)' = k^{1/2}(f' + (a/2)f)`.
Also `sourceDeriv`, `continuous_sourceDeriv`, `sourceLogDeriv`, `sourceWeightC` and its
derivative — reusable for any later weighted-operator work.

Method: build `F = f conj(g) / k`, note `HasCompactSupport F` (from `hfs.mul_right.mul_right`),
get `HasCompactSupport (deriv F)` from `HasCompactSupport.deriv` after `deriv F = F'` by
`funext fun x => (hderiv x).deriv`, then `integral_of_hasDerivAt_of_tendsto` with limits from
`HasCompactSupport.is_zero_at_infty` + `cocompact_eq_atBot_atTop`.

Traps: `HasCompactSupport.div_right` does NOT exist — rewrite `a / b` to `a * b⁻¹` by `funext` +
`div_eq_mul_inv` and use `mul_right`.  `Continuous.integrable_of_hasCompactSupport` needs an
explicit `(μ := (volume : Measure ℝ))` when the measure is not fixed by the goal.
For `√k` algebra, `rw [← Real.mul_self_sqrt]` loops (it rewrites the `k` inside `√k`) — `set s :=
Real.sqrt (...)` FIRST, then rewrite the bare `k`.

Card 6 remaining: the passage from formal symmetry to `A^* = L` after closure (3), closedness +
index −1 (4), compact resolvent, Witten square (8), SUSY Dirac (9), strict positivity (10).
mathlib has `LinearPMap.adjoint/closure/IsClosable` but NO unbounded Fredholm theory.

## Card 5 channels CLOSED (2026-08-07)

`formal/GaloisForLFunctions/RHTower/HedenmalmThetaPrimeChannels.lean` (wired, builds,
axiom-clean).  Statements (6) kernel properties, (7) symbol, (8) reality, (17) the two bounded
self-adjoint channels + the symbol zero set = real Xi divisor.

KEY MOVE: do NOT build convolution operators.  Define the channel on the FOURIER side as
`lpBoundedMulCLM` by the symbol `channelSymbol n t = centeredMultiplier n t * XiC t`; the corpus
multiplier layer then gives boundedness and self-adjointness for free
(`lpBoundedMulCLM_inner_general` needs only `conj φ = φ`).
Measurability of the symbol is free from the CLOSED FORM (measurable division), not from the
integral; the integral representation (`channelSymbol_eq_integral`, valid for t ≠ 0) is used only
for the bound and the reality.  At t = 0 the symbol is 0 by the `/z` convention, which is harmless
({0} is null) and makes both proofs a two-case split.

Traps: `MeasureTheory.integral_conj` does not exist — the name is bare `integral_conj`.
`Real.rpow_nonneg` takes the base nonnegativity FIRST.

## Card 5 frame obstruction (22)/(23) CLOSED (2026-08-07)

In `HedenmalmTwoPrimeNormalFrame.lean`: `frameSymbol n t = 2 n^{-1/2} sin(t log n / 2)`,
`mul_centeredMultiplier_eq_frameSymbol` (t·a_n(t) = b_n(t)), `abs_frameSymbol_le`,
`norm_centeredMultiplier_le` (≤ 2 n^{-1/2}/|t|), `tendsto_norm_centeredMultiplier_atTop`.

### The route for the remaining two Kronecker obstructions (25), (27)
BOTH inputs already exist — do not rebuild:
* `GaloisForLFunctions.linearIndependent_log_primes` (`Core.lean:284`) — ℚ-independence of
  `Real.log p` over `Nat.Primes`.
* `GaloisForLFunctions.kronecker_approx` (`HTGeometry/KroneckerWeylDensity.lean:277`) —
  Kronecker approximation for a ℚ-independent frequency family.

The ONLY gap: `kronecker_approx` returns some `t`, but (25) needs `t` arbitrarily large.
Its proof is a Bohr-mean contradiction, and a Bohr mean only sees the tail, so the identical
argument gives `∀ T, ∃ t > T, …`.  Strengthen `kronecker_approx` in place (add the `T` and change
`hpoint` to quantify over `t > T`), rather than trying to derive the large-`t` version from the
existing statement — there is no cheap derivation, since a bounded good set can still be infinite.

For (27): split the prime sum into a finite head and a tail bounded by `4 ∑ ω_p / p`; apply the
strengthened Kronecker to the head.  Note `|b_p|` is EVEN in t, so `liminf_{t→+∞}` and
`liminf_{|t|→∞}` agree.

## Kronecker recurrence built; card 5 (25) CLOSED (2026-08-07)

NEW REUSABLE CORPUS ASSET:
`formal/GaloisForLFunctions/HTGeometry/KroneckerApproxRecurrence.lean` —
`GaloisForLFunctions.kronecker_approx_atTop (hind) (θ) (hε) (T₀) : ∃ t, T₀ < t ∧ ∀ j, …`.
This is `kronecker_approx` with the approximating time pushed past any bound.  The proof is the
original Bohr-mean contradiction with ONE change: `hpoint` is only assumed for `t > T₀`, and in
`hbd` the window integral is split at `S = max T₀ 0`,
`‖∫_0^T g‖ ≤ S + q^K·T`, so `T⁻¹‖∫_0^T g‖ ≤ S/T + q^K`, and the two limits are compared with
`le_of_tendsto_of_tendsto` instead of `le_of_tendsto`.  Everything else is copied verbatim.

`formal/GaloisForLFunctions/RHTower/HedenmalmPrimeFrameObstruction.lean`:
`abs_sin_le_norm_expChar_sub_one`, `sq_frameSymbol_le` (frameSymbol² ≤ 4ε² when |sin| ≤ ε — uses
only `p^{-1/2} ≤ 1`, no rpow algebra needed), and
`exists_gt_sum_sq_frameSymbol_lt (P : Finset Nat.Primes) (hδ) (T) : ∃ t > T, ∑_{p∈P} b_p(t)² < δ`.
Trick: apply Kronecker with frequencies `Real.log p` at time `s` and return `t = 2s`; this avoids
needing a "scale a linearly independent family" lemma.

Remaining for card 5 frame obstructions: only (27), the summably weighted all-prime form.
Route: head/tail split with `tendsto_tsum_compl_atTop_zero` on `∑ ω_p/p`, then
`exists_gt_sum_sq_frameSymbol_lt` on the head.

## Card 5: ALL THREE frame obstructions CLOSED (2026-08-07)

`HedenmalmPrimeFrameObstruction.lean` now also has
`sq_rpow_neg_half` ((x^(-1/2))² = x⁻¹), `sq_frameSymbol_le_four_div` (b_p(t)² ≤ 4/p),
`summable_weighted_frameSymbol`, and
`exists_gt_tsum_weighted_frameSymbol_lt` — statements (24), (26), (27).

Traps: `tsum_le_tsum` is now `Summable.tsum_le_tsum`.
`tendsto_tsum_compl_atTop_zero` needs the function given EXPLICITLY (HO unification fails on the
triple coercion `((p : Nat.Primes) : ℕ) : ℝ`).
`Summable.sum_add_tsum_compl` produces the complement subtype as `↥(↑P)ᶜ`, NOT `{q // q ∉ P}`;
they are defeq, so restate the tail bound with `:= htailbound` in the `↥(↑P)ᶜ` shape before
`linarith` — linarith will not match the two spellings.

Card 5 remaining: ONLY (13)/(14) conormal generation + the (17) analytic cokernel that rests on it.
Both need Wedderburn/Cartan B for entire functions (Weierstrass product + Mittag-Leffler
interpolation) — absent from corpus and mathlib.

## Card 8 STARTED: symbol layer closed (2026-08-07)

`formal/GaloisForLFunctions/RHTower/HedenmalmEssentialFlowSymbol.lean` (wired, builds,
axiom-clean): `essentialFlowSymbol a L μ = 2μ(sin(a/μ) − sin((a−L)/μ))`,
`weilWidthAmplitude`, `weilFixedWidthSample`, `rootBlockForm`, and the two matching lemmas giving
`essentialFlowSymbol_root : Φ_{a,L}(−1/z) = F_{a,L}(i z)` — card 8 statements (3) and the
term-level content of (5).  No operator theory needed.

METHOD that made it work: do NOT try to prove the identity in one `field_simp`/`linear_combination`.
Introduce a `rootBlockForm` closed form and prove each side equals it separately.  The LHS side
needs `Complex.sin_neg` + `Complex.sin` + four `congr 1; ring` exponent rewrites, then
`field_simp; ring`.  The RHS side needs `hinv : (I*z)⁻¹ = -I * z⁻¹` (via `Complex.inv_I`),
`hinv' : (-(I*z))⁻¹ = I * z⁻¹`, and `← hUX`, `← hVY` to split `exp((a−L)(Iz))` into products;
then plain `ring` — NO `I*I = -1` is needed on either side once the inverses are rewritten.

Trap: after `Complex.sin` unfolds, the exponent appears as `(-(↑a * z)) * Complex.I`, not
`-(↑a * z * Complex.I)`; state the rewrite lemmas in the first shape.

Card 8 remaining: everything resting on the parent's missing Riesz-projection/trace layer —
(1), (4), (5) as a divisor sum, (6).

## Card 6: the ker A = 0 half of (4) CLOSED (2026-08-07)

`formal/GaloisForLFunctions/RHTower/HedenmalmSourceKernelTrivial.lean` (wired, builds,
axiom-clean): `not_integrableOn_exp_Ioi`, `not_integrable_exp_abs`,
`not_integrable_inv_thetaSource`, `not_integrable_const_mul_inv_thetaSource`.
The formal kernel of D is the constants, and `∫ 1/k = ∞` for the theta source (from
`k ≤ thetaBound · e^{−|x|}`), so no nonzero constant lies in `H_k`.

`0 < thetaBound` is NOT free: get it from `abs_thetaCuspFullSource_le 0` plus
`thetaCuspFullSource_pos 0`, and note `thetaBound` is a def for
`thetaCuspDerivativeExpConstant 0` — `linarith` needs a `show` to see through it.

## CORRECTION (2026-08-07): the Weierstrass half is NOT missing

Earlier notes said card 5 (13)/(14) needs "Weierstrass products + Mittag-Leffler".  Only the
SECOND is absent.  The corpus already owns the genus-one canonical product:

* `RHTower.canonicalProductE1Indexed_hasProdLocallyUniformlyOn (a) (ha : ∀ i, a i ≠ 0)
  (hsum : Summable fun i => 1 / ‖a i‖ ^ 2) : HasProdLocallyUniformlyOn … Set.univ`
  in `RHTower/CanonicalProduct.lean`;
* `HTGeometry/MovingCanonicalProduct.lean` — `movingCanonicalProduct_eq_zero_iff` and the
  `analyticOrderAt` computations at each zero;
* `HTGeometry/MovingEvenCanonicalProduct.lean` — the even version.

The zeros of `a_n` are `2πk/log n`, k ≠ 0, simple, growing linearly, so `∑ 1/|zero|²` converges
and the hypothesis is met directly.

What is genuinely absent from corpus AND mathlib: **Mittag-Leffler interpolation** — an entire
function with prescribed finite jets on a discrete set.  Wedderburn needs precisely that (an
entire `b` agreeing with `1/f` to order `m_z` at each zero `z` of `g`; then
`b f + ((1 - b f)/g) g = 1`).  That is the single remaining build for card 5.

## Card 7 (9): the variance side CLOSED (2026-08-07)

`formal/GaloisForLFunctions/RHTower/HedenmalmSourceMoments.lean` (wired, builds, axiom-clean):
`integrable_mul_thetaSource`, `integral_mul_thetaSource_eq_zero` (first moment = 0 by evenness),
`integral_quantileFun` (= 0), `integral_sq_quantileFun` (∫₀¹ Q² = M⁻¹∫x²k).

One line of work once you see it: `integral_comp_quantile S (fun x => x^j)` IS the moment
transfer.  Reuse `integrable_thetaCuspSecondMoment` (PrimeArchThetaFirstMoment.lean) and
`integrable_abs_mul_exp_neg_mul_abs` (WeightedEulerStripFourierAnalytic.lean) — do not rebuild
either.

Card 7 (9) still needs the OPERATOR side `tr(B²)`, i.e. the trace-class layer.

## MAJOR CORRECTION (2026-08-07): the corpus ALREADY HAS the trace-class layer

`formal/GaloisForLFunctions/HTGeometry/HilbertSchmidtTrace.lean` exists and contains:
`opTrace`, `inner_comp_apply`, `summable_inner_diag_comp`, `opTrace_comp_eq_hsInner`,
`opTrace_comp_eq_tsum_basis` (BASIS INDEPENDENCE), `opTrace_comp_comm` (CYCLICITY),
`norm_opTrace_comp_le`, `opTrace_adjoint_comp_self`, `re_opTrace_adjoint_comp_self`,
and the kernel weld `HilbertSchmidt.opTrace_toOperator_comp`.
Also `ContinuousLinearMap.hsInner` (operator level) in `HilbertSchmidtOperator.lean:321`.

So "trace class is missing" was WRONG.  Card 7 (9)'s operator side is now built on it:
`formal/GaloisForLFunctions/RHTower/HedenmalmThetaTrace.lean` — `thetaKernelOperator`,
`thetaTraceSq`, `summable_thetaTraceSq_diag`, `thetaTraceSq_eq_tsum_basis`,
`thetaTraceSq_eq_hsInner`, `norm_thetaTraceSq_le`.
What is left of (9) is only the EQUALITY of the two sides (kernel evaluation of the diagonal sum).

### PROCESS FAILURE TO NOT REPEAT
I created `HTGeometry/HilbertSchmidtTrace.lean` with `cat >` WITHOUT CHECKING IT EXISTED, and
destroyed the file; `TwoProjectionHilbertSchmidtEnergy.lean` imports it and broke.
Recovered with `git show HEAD:<path> > <path>` (NOT `git checkout`, which is banned here).
ALWAYS `ls`/`test -f` a target path before `cat >` in this tree.

## THIRD CORRECTION (2026-08-07): det_2 EXISTS in the corpus

`HTGeometry/FredholmDeterminant.lean` — the regularized Hilbert–Carleman determinant for an
ARBITRARY Hilbert–Schmidt kernel: `fredholmExp`, `fredholmExp_summable`, `fredholmDet`,
`logDeriv_fredholmDet` (Plemelj), `fredholmDet_ne_zero`, `hasDerivAt_fredholmDet`,
`fredholmDet_differentiableOn`, `fredholmDet_weld`.
`HTGeometry/FredholmDeterminantInfinite.lean` — the countable diagonal case with the closed-form
resolvent trace.
`HTGeometry/HilbertSchmidt.lean` — `resolventTrace`, `resolventTrace_summable`.
`HTGeometry/HilbertSchmidtMatrix.lean` — the operator/kernel bridge `toOperator`, `matrixOf`,
`isHS_matrixOf`, `matrixOf_toOperator`, `toOperator_matrixOf`.

So card 7 (8) is a TRANSFER + IDENTIFICATION problem, not a missing-theory problem.
Card 7's Lean-status text (which asserted no det_2 exists) has been corrected in place.

### Running score on my own "missing infrastructure" claims this session: 3 wrong out of 4.
Weierstrass products — already there.  Trace class — already there.  det_2 — already there.
Only Mittag-Leffler interpolation and analytic-Fredholm/Riesz-projection multiplicity survive
as genuinely absent (the latter: `grep -rln "rieszProj\|generalizedEigenspace\|algebraicMultiplicity"`
returns NOTHING in the corpus).
ALWAYS run the corpus audit BEFORE declaring a blocker.

## COMPLETED CORPUS AUDIT of the remaining blockers (2026-08-07)

Genuinely ABSENT from corpus and mathlib (verified by grep, nothing found):
* Mittag-Leffler / analytic interpolation — no `interpolat`/`MittagLeffler`/`prescribed` module
  for entire functions with prescribed jets.  Blocks card 5 (13)/(14) and the (17) cokernel.
* Analytic-Fredholm multiplicity / Riesz projections — `rieszProj`, `generalizedEigenspace`,
  `algebraicMultiplicity` return NOTHING.  Blocks card 7 (6), hence card 4 (16) and card 8.
* Unbounded Fredholm theory — no `IsFredholm`, no `fredholmIndex`, no compact-resolvent layer for
  `LinearPMap`.  The corpus `LinearPMap` files (RealCorona*, InfinitePhaseLadder*) are boundedness
  CLASSIFICATION, not Fredholm theory.  Blocks card 6 (4)-index, (8), (9), (10).

PRESENT but not yet applied (do NOT rebuild):
* det_2 — `HTGeometry/FredholmDeterminant.lean` + `FredholmDeterminantInfinite.lean`.
* trace class on HS products — `HTGeometry/HilbertSchmidtTrace.lean`.
* operator/kernel bridge — `HTGeometry/HilbertSchmidtMatrix.lean`.
* genus-one Weierstrass products — `RHTower/CanonicalProduct.lean`,
  `HTGeometry/MovingCanonicalProduct.lean`.

## Tree state at end of session
All 13 new Hedenmalm modules + `HTGeometry/KroneckerApproxRecurrence.lean` are wired into their
umbrellas, build, and contain no sorry/admit/axiom/opaque/unsafe.
`scripts/formal_tools.py lint` reports 9 "owned module unreachable from umbrella" errors — ALL
pre-existing and none of them mine (Prolate*, RouteEMovingTerminalKernelResonance,
CriticalGenericArc, CriticalGeometricSheetFibre, GenericJetInversePolynomial).  Do not wire them
blindly; they belong to other in-progress work.

## Card 7: B² is trace class (2026-08-07)

Added to `HedenmalmThetaTrace.lean`: `isTraceClass_thetaKernelOperator_sq`,
`isTraceClass_adjoint_comp_thetaKernelOperator`,
`re_opTrace_adjoint_comp_thetaKernelOperator` (Re tr(B†B) = ‖B‖²_HS).
Uses `RHTower.IsTraceClass` + `IsHilbertSchmidt.comp_isTraceClass` +
`IsHilbertSchmidt.adjoint_comp_self_isTraceClass` from
`RHTower/SoninTimeBandHilbertSchmidt.lean` — a FOURTH already-built layer (Schatten S₁ by
factorization, plus `tendsto_opTrace_pow_add_two_zero_of_isHilbertSchmidt_norm_lt_one`).

### The genuine gap for card 7 (9) is now ONE bridge
`hsNormSq_kernelOperator_eq_norm_sq` exists (Sonin file, line 111) but there is NO polarized
version.  Build `hsInner (kernelOperator μ K) (kernelOperator μ L) = ⟪K, L⟫_{L²(μ; E*)}`; then
`tr(B²) = ⟨B†, B⟩_HS` evaluates to the kernel double integral and (9) closes against
`integral_sq_quantileFun`.

## The card 7 (9) bridge is BUILT (2026-08-07)

NEW: `formal/GaloisForLFunctions/RHTower/KernelOperatorPolarization.lean` (wired, builds,
axiom-clean):
* `inner_kernelOperator_apply` — ⟪K̂ e, L̂ e⟫ = ∫ ⟪K x e, L x e⟫ dμ (polarizes the private
  `norm_kernelOperator_apply_sq` of the Sonin file);
* `norm_sq_kernelOperator_apply` — the PUBLIC diagonal case (the Sonin one is `private`);
* `hsInner_kernelOperator` — **⟪K̂, L̂⟫_HS = ∫ ⟪y_L(x), y_K(x)⟫ dμ** where `y = toDual.symm`.

NOTE the argument ORDER SWAP: `toDual.symm` is conjugate linear, so the L-vector comes first.
`E →L[ℂ] ℂ` has NO `InnerProductSpace` instance in mathlib, so the pairing MUST be written on the
Riesz vectors — do not try to state it as `⟪K, L⟫` on the dual Lp.

Traps: `L2.integrable_inner` needs `(𝕜 := ℂ)` explicitly; `MemLp.toLp` needs its function argument
explicitly; `omit [CompleteSpace E] in` must come BEFORE the docstring, not between docstring and
theorem; `MemLp.integrable_sq_norm` does not exist — use
`(memLp_two_iff_integrable_sq_norm h.1).mp h`.

Next step for card 7 (9): specialize `hsInner_kernelOperator` at `K = L = pinnedKernelL2 thetaSource`,
combine with `thetaTraceSq_eq_hsInner` and the adjoint kernel, and match against
`integral_sq_quantileFun`.

## Blocker found for the operator-level form of card 7 (5) (2026-08-07)

To get `hsNormSq thetaKernelOperator = M ∫ p(1-p)/k` one applies
`RHTower.hsNormSq_kernelOperator_eq_norm_sq`, which requires
`[TopologicalSpace.SeparableSpace E]` with `E = Lp ℂ 2 unitIntervalMeasure`.
**That instance does NOT resolve** (`infer_instance` fails).  Supplying it is the first step:
`unitIntervalMeasure = volume.restrict (Icc 0 1)` is a finite Borel measure on ℝ, so the standard
route is `MeasureTheory.Lp.instSeparableSpace`-style — find the exact mathlib instance and its
`CountablyGenerated`/`SecondCountableTopology` side conditions, then declare it once (probably in
`HedenmalmPinnedVolterraBoundaryDefect.lean` next to `unitIntervalMeasure`) so every later module
gets it.

Everything else for that statement is already in hand:
`HTGeometry.norm_l2_sq_eq_integral_norm_sq`, `norm_pinnedKernelField`, `norm_sq_pinnedSliceVec`,
`integral_quantileSpeed_sq_slice`.

### VERIFIED separability finding (supersedes the note above)
`infer_instance` for `SeparableSpace (Lp ℂ 2 volume)` and for
`SeparableSpace (Lp ℂ 2 unitIntervalMeasure)` BOTH fail in a scratch file.
BUT `RHTower.hsNormSq_fullToRestrictedTimeBandFourier_eq_rectangleArea`
(`SoninTimeBandHilbertSchmidt.lean:448`) applies `hsNormSq_kernelOperator_eq_norm_sq`
with `E = RealL2 = Lp ℂ 2 volume` and COMPILES.  So the instance is obtainable somehow.
Before writing a new instance, find out how that theorem elaborates (`set_option pp.all true`,
or check whether some import supplies it) — given that four "missing" claims this session were
wrong, assume it is present until proven otherwise.

Verified with raised `maxHeartbeats` and `synthInstance.maxHeartbeats`:
`SeparableSpace (Lp ℂ 2 volume)` FAILS, and
`SeparableSpace (Lp ℂ 2 unitIntervalMeasure)` FAILS, including when the goal is the exact
application `hsNormSq_kernelOperator_eq_norm_sq _ _` at `thetaKernelOperator`.
Yet `RHTower.hsNormSq_fullToRestrictedTimeBandFourier_eq_rectangleArea` compiles with
`E = RealL2 = Lp ℂ 2 volume`.  UNEXPLAINED.
NEXT SESSION: run `set_option trace.Meta.synthInstance true` inside
`SoninTimeBandHilbertSchmidt.lean` at line 448 to see which instance fires there; copy that path.
Do NOT write a fresh `SeparableSpace` instance before doing this — a duplicate instance is exactly
the kind of change that broke the tree earlier this session.

## Card 8 statement (2) CLOSED (2026-08-07)

Added to `HedenmalmEssentialFlowSymbol.lean`:
`compactEigenvalue_eq_of_spectralParameter` (μ = −1/z = −i/w at w = iz) and
`xiC_eq_xi_shift` / `xiC_eq_zero_iff_xi_shift` (XiC z = xi(1/2 + i z); note `XiC` is DEFINED as
`xi (1/2 + z * Complex.I)` in `RHTower/XiEntireReal.lean:22`, so this is a `congr 1; ring`).

Card 8 now has (2), (3) and the term-level content of (5).  Everything else on the card rests on
the parent card 7's Riesz-projection layer.

## Card 7 (6) forward half is now UNCONDITIONAL (2026-08-07)

Added to `HedenmalmThetaRootEndpoints.lean`:
`integrable_sourceModeU`, `tendsto_sourceModeU_atBot`, `tendsto_sourceModeU_atTop`
(all one line each from `norm_sourceModeU_le`), and
`XiC_eq_zero_of_solution_const` — the ⟹ half of the divisor equivalence at the actual source.

The ⟸ half (`sourceInverse_sourceModeF_eq_smul`) still needs its `hmass` hypothesis
`∫ sourceModeF thetaSource z = M` discharged; that is a normalisation computation, NOT free —
it is the one remaining hypothesis on that side.  The other three
(`HasShiftedTail`, `Integrable (sourceModeF …)`, `Tendsto (sourceModeU …) atBot 0`) are now all
available as theorems above.

## STRUCTURAL CONCLUSION: card 7 (6) and (8) are ONE problem (2026-08-07)

Because `det₂` already exists in the corpus, the natural formalization of "algebraic multiplicity"
is the ORDER OF VANISHING OF `det₂(I + zB)`.  With that definition:

* (6)'s multiplicity clause becomes `analyticOrderAt (fun z => det₂(I+zB)) z₀ = analyticOrderAt XiC z₀`;
* which follows immediately from (8), `det₂(I+zB) = Ξ_C(z)/Ξ_C(0)`.

So **(6) and (8) collapse to a single identification**, and that identification reduces via the
Plemelj identity `logDeriv_fredholmDet` to a TRACE FORMULA

    resolventTrace B z  =  -Ξ_C'(z)/Ξ_C(z)   (up to the regularisation shift),

which is the real mathematical content and is NOT a Lean-plumbing problem.  Note `fredholmDet`
converges only on `‖z‖·‖K‖_HS < 1`, so an analytic-continuation step is also needed.

Do NOT attack (6) by building Riesz projections — that is a strictly harder route to the same
statement.  `resolvent` DOES exist in mathlib (verified) if Riesz projections are ever wanted for
another purpose.

## Recommended order of attack for the three absent layers
1. The trace formula above (closes card 7 (6)+(8), unblocks card 4 (16) and card 8).  Hardest
   mathematically but needs no new infrastructure — only `fredholmDet`, `resolventTrace`,
   `HilbertSchmidtMatrix` bridge, all present.
2. Mittag-Leffler interpolation (closes card 5 (13)/(14)/(17)).  Pure infrastructure; the
   Weierstrass half is present (`canonicalProductE1Indexed_hasProdLocallyUniformlyOn`).
3. Unbounded Fredholm (card 6 (4)-index, (8)-(10)).  Largest, and nothing in the corpus to build on
   beyond mathlib's `LinearPMap.adjoint/closure/IsClosable`.

## Tree verified green at end of session: `lake build` of all 21 new modules — 9113 jobs, EXIT=0.

## OPEN PUZZLE — the `SeparableSpace` instance (three verified facts, 2026-08-07)

1. `lake env lean GaloisForLFunctions/RHTower/SoninTimeBandHilbertSchmidt.lean` compiles FROM
   SOURCE, exit 0.  So `hsNormSq_fullToRestrictedTimeBandFourier_eq_rectangleArea` really does
   discharge `[TopologicalSpace.SeparableSpace RealL2]` in that file's context.
2. In a scratch file that imports that module, `infer_instance` for
   `TopologicalSpace.SeparableSpace RealL2` FAILS (also for the unfolded `Lp ℂ 2 volume`, also with
   `synthInstance.maxHeartbeats 1000000`).
3. mathlib has NO `SeparableSpace (Lp …)` instance
   (`grep -rn "SeparableSpace (Lp" .lake/packages/mathlib/Mathlib/` — nothing), and the corpus
   declares none (`grep -rn "SeparableSpace" GaloisForLFunctions` — only binders, no instances).

These three cannot all be true under a naive reading, so something context-dependent is going on.
RESOLVE THIS FIRST before writing any `SeparableSpace` instance — it gates the operator-level form
of card 7 (5) (`hsNormSq thetaKernelOperator = M ∫ p(1-p)/k`) and any use of
`hsInner_kernelOperator` at `thetaSource`.
Suggested probe: add `set_option trace.Meta.synthInstance true in` immediately before
`hsNormSq_fullToRestrictedTimeBandFourier_eq_rectangleArea` in the Sonin file itself and read which
instance fires.

## SEPARABILITY PUZZLE SOLVED — and card 7 (5) closed at the operator level (2026-08-07)

The missing ingredient is `local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩`.
With that in scope, `TopologicalSpace.SeparableSpace (Lp ℂ 2 μ)` RESOLVES and
`hsNormSq_kernelOperator_eq_norm_sq` applies.  That is why the Sonin file works (it declares the
Fact locally at lines 32 and 325) and why every scratch test failed.
`infer_instance` for `SeparableSpace (Lp …)` will still look like it fails unless the Fact is
present — always add the Fact instance to any module using the kernel-operator HS lemmas.

Consequence, now proved in `HedenmalmThetaTrace.lean`:
`hsNormSq_thetaKernelOperator : hsNormSq thetaKernelOperator = M * ∫ tailEnergyDensity thetaSource`
— card 7 statement (5) at the OPERATOR level, unconditionally.

Route: `hsNormSq_kernelOperator_eq_norm_sq` → `HTGeometry.norm_l2_sq_eq_integral_norm_sq`
(namespace is bare `HTGeometry`, not `GaloisForLFunctions.HTGeometry`) → a.e. rewrite with
`MemLp.coeFn_toLp` + `norm_pinnedKernelField` + `norm_sq_pinnedSliceVec` → `restrict_Ioo_eq_restrict_Icc`
→ `integral_quantileSpeed_sq_slice`.
Trap: `rw [hc]` needs `pinnedKernelL2` unfolded first (`rw [pinnedKernelL2, hc, …]` after a `show`).

## The last endpoint datum of card 4 (12) / card 7 (6)-converse is COMPUTED (2026-08-07)

`HedenmalmThetaRootEndpoints.integral_sourceModeU`:
at a zero of `Ξ_C` with `|Im z| < 1` and `z ≠ 0`,
    `∫_ℝ u_z = -M / z`.
Proof: integrate the source ODE across the line.  `hasDerivAt_sourceModeU` gives
`u' = -(I z) u - I k`; `integral_of_hasDerivAt_of_tendsto` with the two boundary limits (both
proved) makes `∫ u' = 0`, and `∫ (k : ℂ) = (M : ℂ)` via `integral_complex_ofReal`.

So all THREE endpoint data of `sourceInverse_sourceModeF` are now available at `thetaSource`:
`Integrable (sourceModeF …)` (from `integrable_sourceModeU`),
`Tendsto (sourceModeU …) atBot 0` (from `tendsto_sourceModeU_atBot`), and the total mass.
CAUTION: `sourceInverse_sourceModeF` wants `hmass : ∫ sourceModeF = M`, and
`sourceModeF = -z • sourceModeU`, so `∫ sourceModeF = -z · (-M/z) = M` — CHECK THE SIGN when wiring
it up; the eigenvector statement `B f_z = -z⁻¹ f_z` should then be unconditional at `thetaSource`.

Trap: for the final algebra do NOT `field_simp` then `linear_combination` — derive
`J = -(I·M)/(I·z)` by `rw [eq_div_iff hIz]; linear_combination hsolve`, then `field_simp`.

## Card 7 (6) point-spectrum equivalence is now UNCONDITIONAL IN BOTH DIRECTIONS (2026-08-07)

`HedenmalmThetaRootEndpoints`:
`integrable_sourceModeF`, `integral_sourceModeF` (= M — the sign works out),
`sourceInverse_sourceModeF_eq_smul_theta : B f_z = -z⁻¹ f_z` at every zero of Ξ_C with
|Im z| < 1, z ≠ 0, NO hypothesis on the source.
Together with `XiC_eq_zero_of_solution_const` (the ⟹ half) this closes the point-spectrum content
of card 7 (6) and card 4 (12) at the actual arithmetic source.

What is still open in (6) is ONLY the multiplicity clause (order of Ξ_C = algebraic multiplicity),
which — see the structural note above — is the same problem as (8) and reduces to the trace formula.

## WHY card 7 (8) is hard — the two routes, analysed (2026-08-07)

(8) `det₂(I + zB) = Ξ_C(z)/Ξ_C(0)` is the single remaining blocker for cards 4, 7 and 8.
There are exactly two classical routes and BOTH need something the corpus lacks.

ROUTE A — Plemelj / power traces.
`logDeriv_fredholmDet` gives `logDeriv det₂(1 - wK) = -resolventTrace K w`, and
`resolventTrace K w = ∑_{n≥1} wⁿ tr(K^{n+1})`.  Matching against `-Ξ_C'/Ξ_C` expanded by the
Hadamard product needs the POWER-TRACE FORMULA `tr(Bᵐ) = ∑_j λ_jᵐ`, i.e. **Lidskii for a
NON-self-adjoint trace-class operator**.  The corpus has `HTGeometry/LidskiiSelfAdjoint.lean`
(self-adjoint only, built from a signed-step Gram–Schmidt); `B` is not self-adjoint (`RBR = -B`).
The Hadamard side IS available: `RHTower/XiHadamardFactorization.lean`
(`xiCanonicalProduct_multipliable`, `xiCanonicalProduct_factorization_at_support`,
`xiCanonicalProduct_analyticOrderAt_eq_XiC`).

ROUTE B — Grushin / Schur determinant.
`HTGeometry/SourceGrushinInverse.lean` gives only KERNEL equivalence
(`exists_sourceGrushinPencil_kernel_iff_eigen`), NOT a determinant identity.  Turning it into (8)
needs the bordered pencil to factor as `(invertible) ∘ diag(I, Ξ_C(z)/Ξ_C(0))` AND a
multiplicativity law for `det₂` — but `det₂` is only multiplicative up to
`exp(-tr((A-I)(B-I)))`, so a correction term must be computed.

CONCLUSION: (8) is not blocked by plumbing.  It needs either non-self-adjoint Lidskii or the
Grushin–Schur determinant factorisation with its `det₂` correction term.  Both are research-level.
Do not restart this by looking for a missing library — the audit is complete.

## Card 7 (9) reduced to ONE Fubini (2026-08-07)

`tr(B²) = opTrace (B ∘L B) = hsInner (B†) B`, and `hsInner_kernelOperator` evaluates that as a
single integral AS SOON AS `B†` is exhibited as a kernel operator.  For the pinned kernel the
transposed field is EXPLICIT:

    pinnedKernelFun S t u = i q(t) (1_{u ≤ t} − t)
    conj (pinnedKernelFun S u t) = −i q(u) (1_{t ≤ u} − u)

so `B†` is the kernel operator whose row at `t` is `u ↦ −i q(u)(1_{t ≤ u} − u)`.
That row IS in `L²(0,1)`: its energy is `∫ q(u)² (1_{t≤u} − u)² du`, and near `u = 0` the
integrand is `(q²u(1−u))·u/(1−u)` while near `u = 1` it is `(q²u(1−u))·(1−u)/u` — both the finite
HS integrand `q²u(1−u)` times a bounded factor.  So `hasFiniteKernelEnergy_thetaSource` already
supplies the integrability.

REMAINING STEP: prove `adjoint (kernelOperator μ K) = kernelOperator μ K^T` for this explicit
transposed field, i.e. `⟪B f, g⟫ = ⟪f, B^T g⟫`, which is ONE Fubini on `(0,1)²` with
square-integrable kernels (finite measure, so `MeasureTheory.integral_integral_swap` applies with
the product-integrability bound `‖K(t,u)‖‖f u‖‖g t‖`).
Then `tr(B²) = ∫ ⟪…⟫` and (9) closes against `integral_sq_quantileFun`.
This is a bounded, non-research build — unlike (8).

## First step of the (9) Fubini is built (2026-08-07)

`HedenmalmThetaTrace.integral_norm_sq_pinnedKernelFun (S) (ht : t ∈ Ioo 0 1) :`
`∫ u, ‖pinnedKernelFun S t u‖² ∂unitIntervalMeasure = q(t)² · t(1−t)`
— the row energy as an HONEST INTEGRAL of the kernel function rather than an `Lp` norm.  Derived
from `norm_sq_lp_eq_integral` + `norm_sq_pinnedKernelVec` + `MemLp.coeFn_toLp`; the only trap is
that `pinnedKernelVec` must be unfolded (`rw [pinnedKernelVec, hu]`) before the coeFn rewrite bites.

Remaining chain for (9):
1. Tonelli on `(0,1)²` for `‖pinnedKernelFun S t u‖²` to get
   `∫∫ ‖k‖² = ∫ q(t)² t(1−t) dt` = the HS energy (uses the lemma just built as the inner integral).
2. `MemLp (uncurry pinnedKernelFun) 2 (μ.prod μ)` from step 1.
3. Product integrability of `(t,u) ↦ conj(k(t,u)) conj(f u) g(t)` by Cauchy–Schwarz on the product.
4. `integral_integral_swap` ⟹ `⟪B f, g⟫ = ⟪f, Bᵀ g⟫` ⟹ `adjoint B = kernelOperator Kᵀ`.
5. `hsInner_kernelOperator` at `(Kᵀ, K)` ⟹ `tr(B²)` as a double integral; close against
   `integral_sq_quantileFun`.

## (9) chain: steps 1-3 built (2026-08-07)

In `HedenmalmThetaTrace.lean`:
* `integral_norm_sq_pinnedKernelFun` — inner row energy as an explicit integral;
* `measurable_quantileSpeed`, `measurable_uncurry_pinnedKernelFun` — joint measurability on the
  square (the indicator via `measurableSet_le measurable_snd measurable_fst`);
* `integrable_sq_norm_uncurry_pinnedKernelFun` — **the kernel is square integrable on `(0,1)²`**.

KEY MOVE for that last one: do NOT go through ℝ≥0∞/`lintegral_prod`.  Use
`MeasureTheory.integrable_prod_iff hmeas`, whose two obligations are exactly
(a) a.e. row-wise integrability (`memLp_two_iff_integrable_sq_norm` on `memLp_pinnedKernelFun`) and
(b) integrability of the row energy — which IS `HasFiniteKernelEnergy` after rewriting with
`integral_norm_sq_pinnedKernelFun`.  No ENNReal plumbing at all.

Remaining for (9): product integrability of `(t,u) ↦ conj k(t,u) · conj f(u) · g(t)` by
Cauchy–Schwarz/Hölder on the product (both factors now known `L²`), then
`integral_integral_swap` ⟹ `adjoint B = kernelOperator Kᵀ`, then `hsInner_kernelOperator`.

## (9) step 4 — the tools are confirmed present (2026-08-07)

`MeasureTheory.MemLp.integrable_mul` EXISTS (verified) — Hölder for conjugate exponents, so
`k · (conj f ⊗ g)` is product-integrable once BOTH factors are `MemLp … 2 (μ.prod μ)`.
* factor 1 is done: `integrable_sq_norm_uncurry_pinnedKernelFun` + `memLp_two_iff_integrable_sq_norm`.
* factor 2 (the TENSOR `(t,u) ↦ conj (f u) * g t`) still to build: same
  `integrable_prod_iff` pattern on `‖·‖² = |f u|²|g t|²`, whose two obligations are
  (a) rows: const × integrable, (b) `Integrable (fun t => ‖f‖² |g t|²)`.
  The only real risk there is the product-measure a.e.-strong-measurability of `fun p => f p.2`
  and `fun p => g p.1` — look for `AEStronglyMeasurable.comp_snd` / `.comp_fst` (or
  `.fst` / `.snd`) BEFORE hand-rolling it.
Then `integral_integral_swap` gives `⟪B f, g⟫ = ⟪f, Bᵀ g⟫`, hence `adjoint B = kernelOperator Kᵀ`,
and `hsInner_kernelOperator` finishes (9) against `integral_sq_quantileFun`.

## (9) step 4 COMPLETE (2026-08-07)

`HedenmalmThetaTrace.memLp_tensor (f g : Lp ℂ 2 unitIntervalMeasure) :`
`MemLp (fun p : ℝ × ℝ => conj (f p.2) * g p.1) 2 (μ.prod μ)`.
Both product-measurability lemmas exist and are the right ones:
`AEStronglyMeasurable.comp_snd` and `.comp_fst`.
Same `integrable_prod_iff` pattern as the kernel case; `RCLike.norm_conj` handles the conjugate.
Traps: `AEStronglyMeasurable.pow` takes a NAT exponent (`(h.norm).pow 2`), not a measurability
proof — `pow_const` does not exist on `AEStronglyMeasurable`.

With `MemLp.integrable_mul` this gives product integrability of
`(t,u) ↦ conj k(t,u) · conj f(u) · g(t)`, i.e. (9) step 4 is DONE.
Remaining: step 5 `integral_integral_swap` ⟹ `adjoint B = kernelOperator Kᵀ`
(needs the transposed field defined and shown to be an `Lp` element — its rows are
`u ↦ conj (pinnedKernelFun S u t)`, energy finite by the SAME product square-integrability read in
the other order), then step 6 `hsInner_kernelOperator`.

## (9) step 5a built; a real elaboration wall found (2026-08-07)

BUILT: `integrable_sq_norm_swap_pinnedKernelFun (S) (hfin) :`
`Integrable (fun p : ℝ × ℝ => ‖pinnedKernelFun S p.2 p.1‖^2) (μ.prod μ)`
— one line, `(integrable_sq_norm_uncurry_pinnedKernelFun S hfin).swap`
(`MeasureTheory.Integrable.swap` exists; `measurePreserving_swap` does NOT).

WALL (RESOLVED — see below): extracting the a.e. row statement
`∀ᵐ t, Integrable (fun u => ‖pinnedKernelFun S u t‖^2) μ`
from `(integrable_prod_iff hmeas).mp (…swap…)` DOES NOT ELABORATE — `isDefEq` times out even at
`maxHeartbeats 1000000`.  The problem is unifying `integrable_prod_iff`'s `f (x, y)` shape against
`fun p => ‖k p.2 p.1‖^2`; raising heartbeats does not help, so do NOT just bump the limit.
NEXT ATTEMPT: introduce `F : ℝ × ℝ → ℝ := fun p => ‖pinnedKernelFun S p.2 p.1‖ ^ 2` with `set`,
state `hmeas`/`hswap` about `F`, apply `integrable_prod_iff` to `F` alone, and only afterwards
`filter_upwards` and beta-reduce with a `show`.  The unfinished lemma was REMOVED from the tree
rather than left broken; `integrable_sq_norm_swap_pinnedKernelFun` is kept and compiles.

### The wall was self-inflicted — `Integrable.prod_left_ae` does it in one line
`MeasureTheory.Integrable.prod_left_ae : Integrable f (μ.prod ν) → ∀ᵐ y ∂ν, Integrable (fun x => f (x,y)) μ`.
Applied to the UNSWAPPED `integrable_sq_norm_uncurry_pinnedKernelFun`, this IS
`∀ᵐ t, Integrable (fun u => ‖pinnedKernelFun S u t‖²) μ` — no swap, no `integrable_prod_iff`, no
`set`, no heartbeat bump.  Built as `ae_integrable_sq_norm_transpose_row`.
LESSON: when `integrable_prod_iff` will not elaborate, look for the dedicated projection lemma
(`Integrable.prod_left_ae` / `.prod_right_ae`) before fighting the unifier.

## (9) step 6 — the remaining design decision (2026-08-07)

All five preceding steps are built.  Step 6 is a DEFINITIONAL choice, not a proof gap:

`Kᵀ(t) f = ∫ u, conj (pinnedKernelFun S u t) * f u du = ⟪w_t, f⟫` with
`w_t (u) = pinnedKernelFun S u t`  (because `innerSL ℂ w f = ∫ conj (w u) * f u`).
`w_t ∈ L²` holds only for A.E. `t` (`ae_integrable_sq_norm_transpose_row`), so the field
`t ↦ Kᵀ(t)` must be defined by a case split — `MemLp.toLp` where the row is `L²`, `0` elsewhere —
and then shown a.e. equal to the honest transpose.  Decide that construction deliberately; it is
the only remaining piece before `integral_integral_swap` gives `adjoint B = kernelOperator Kᵀ` and
`hsInner_kernelOperator` closes (9) against `integral_sq_quantileFun`.

Alternative worth weighing first: state (9) directly as the DOUBLE INTEGRAL
`opTrace (B ∘L B) = ∬ k(t,u) k(u,t) dt du` and prove that from `opTrace_comp_eq_hsInner` plus the
product Fubini, skipping the adjoint-as-kernel-operator construction entirely.

## Gate to the matrix model is named (2026-08-07)

`HedenmalmThetaTrace.separableSpace_unitIntervalL2 :`
`TopologicalSpace.SeparableSpace (Lp ℂ 2 unitIntervalMeasure)` — `inferInstance`, valid only
because the module declares `local instance : Fact ((2 : ENNReal) ≠ ⊤)`.
This is the prerequisite for `HilbertSchmidtMatrix` (`toOperator` / `matrixOf`) and hence for
`fredholmDet`, i.e. for even STATING card 7 (8).

Route to (8), for the record:
1. separable ⟹ countable Hilbert basis ⟹ isometry `Lp ℂ 2 unitIntervalMeasure ≃ₗᵢ ℓ²(ι)`;
2. transport `thetaKernelOperator` and take `matrixOf` (`isHS_matrixOf` gives `IsHS`);
3. `fredholmDet (matrixOf B̃) z` is then defined, and (8) is
   `fredholmDet (matrixOf B̃) (-z) = XiC z / XiC 0` (sign per `det₂(1 - wK)` convention);
4. the mathematical content is the trace formula — see the structural note above.
Steps 1-2 are plumbing; step 4 is the research.

## Card 7 (8): the object now EXISTS in Lean (2026-08-07)

`HedenmalmThetaTrace.lean` now carries the whole coordinate bridge:
`thetaIndex` (+ `Countable` from `orthonormal.countable_index`, needs separability;
`DecidableEq` by `Classical.decEq`), `thetaCoord` (= `hsBasis.repr`),
`thetaKernelMatrixOperator` (conjugate `B` by `thetaCoord`),
`isHilbertSchmidt_thetaKernelMatrixOperator` (`comp_left`/`comp_right` of the isometries),
`thetaKernelMatrix := HilbertSchmidt.matrixOf …`, `isHS_thetaKernelMatrix`,
`thetaFredholmDet z := HilbertSchmidt.fredholmDet thetaKernelMatrix z`,
`thetaFredholmDet_ne_zero`.

So `det₂` OF THE ACTUAL SOURCE INVERSE is now a defined, nonvanishing Lean object.
Statement (8) is finally EXPRESSIBLE:
`thetaFredholmDet (-z) = XiC z / XiC 0` (check the sign against the `det₂(1 - wK)` convention).
What remains is only its PROOF — the trace formula.  All plumbing is done.

## Card 7 (8) is now ONE analytic identification (2026-08-07)

Added: `differentiableOn_thetaFredholmDet`, `logDeriv_thetaFredholmDet`
(= `HilbertSchmidt.logDeriv_fredholmDet` at `thetaKernelMatrix`).

And `HilbertSchmidt.fredholmDet_weld` is EXACTLY the finishing tool:
given `L` holomorphic and nonvanishing on `ball 0 r` with
`logDeriv L = -resolventTrace K` there, it concludes `det₂(1 - zK) = c · L z`.

So (8) needs NOTHING further from determinant theory.  The single remaining obligation is
    `HilbertSchmidt.resolventTrace thetaKernelMatrix z = -Xi_C'(z)/Xi_C(z)`  (up to sign/shift),
i.e. the trace formula, which is the research content.  Everything else is instantiation.

## Card 6 (8) at the formal/core level CLOSED (2026-08-07)

`HedenmalmWeightedAdjointCore`: `integral_weighted_witten` — apply `integral_weighted_symmetry`
with `g := D f` (NOT with f and g swapped, which was my first, wrong, attempt) to get
`⟨f, L D f⟩ = ⟨D f, D f⟩`; plus `integral_weighted_energy_nonneg` showing the energy form equals
`∫ ‖f'‖²/k`, real and nonnegative.  That is the formal content of `L D = A*A ≥ 0`.

`ContDiff ℝ 1 (deriv f)` from `ContDiff ℝ 2 f` is `((contDiff_succ_iff_deriv).mp hf).2.2`.
`sourceWeightC` will not `rw` when applied — use `show`.

Card 6 (8) still lacks the OPERATOR statement (self-adjointness of the closure, compact resolvent);
that part still needs the unbounded-Fredholm layer.

## Card 6: EVERY statement now has its core-level content (2026-08-07)

`HedenmalmWeightedAdjointCore` additions: `weightedPair`/`sourceD`/`sourceL`,
`weightedPair_D_left`, `conj_weightedPair_integrand`, `weightedPair_L_left`,
`weightedPair_dirac_symmetry` (card 6 (9)), `integral_weighted_witten` +
`integral_weighted_energy_nonneg` (card 6 (8)), and
`eq_zero_of_shifted_kernel` (card 6 (10) strictness: `(A+α)f = 0` with compact support ⟹ f ≡ 0,
via `f(x)e^{iαx}` constant + ℝ noncompact).

Traps: `HasDerivAt.cexp` gives `exp(...) * c`, not `c * exp(...)` — use `congr_deriv; ring`.
`Set.ne_univ_iff_exists_not_mem` and `image_eq_zero_of_nmem_tsupport` do NOT exist; use
`by_contra` + `Set.eq_univ_of_forall` + `IsCompact.ne_univ`, and `subset_tsupport` with
`Function.mem_support`.

What remains on card 6 is UNIFORM: the passage from each core identity to the operator statement
after closure (A* = L, index −1, compact resolvent, self-adjointness, operator strict positivity).
That is the unbounded-Fredholm layer.

# ============ BUILD PLANS FOR THE THREE REMAINING LAYERS ============
(written 2026-08-07 at the end of the long formalisation session; all supporting
 assets below were VERIFIED present, not guessed)

## PLAN A — Wedderburn / Mittag-Leffler  (closes card 5 (13),(14),(17)-cokernel)

Target: `f g : ℂ → ℂ` entire with no common zero ⟹ `∃ a b entire, a*f + b*g = 1`.
Reduction (classical): find entire `b` with `b ≡ 1/f` to order `m_z` at each zero `z` of `g`;
then `a := (1 - b*f)/g` is entire and `a*g + b*f = 1`.
For card 5 the zeros are SIMPLE (`a_n` has simple zeros at `2πk/log n`, k ≠ 0), so only VALUE
interpolation is needed — no jets.

Concrete steps:
1. Weierstrass side is DONE in the corpus:
   `RHTower.canonicalProductE1Indexed_hasProdLocallyUniformlyOn` needs only
   `∀ i, a i ≠ 0` and `Summable (fun i => 1 / ‖a i‖^2)`; the zeros `2πk/log n` satisfy both.
   `HTGeometry/MovingCanonicalProduct.lean` gives `movingCanonicalProduct_eq_zero_iff` and the
   `analyticOrderAt` at each zero.
2. Build the interpolation series
   `b z = ∑_k c_k · G z / ((z - w_k) * deriv G w_k) · (z / w_k)^{m_k}`
   with `m_k` chosen so that `∑_k |c_k / deriv G w_k| · (R/|w_k|)^{m_k} < ∞` on each `|z| ≤ R`.
   The convergence engine is the same `Summable`+`HasProdLocallyUniformlyOn` machinery.
3. `b` is entire and `b w_k = c_k` (the k-th term is the only one not vanishing at `w_k`).
Estimate: several hundred lines; the analysis is standard but the locally-uniform bookkeeping is
the bulk.

## PLAN B — the trace formula  (closes card 7 (6)+(8), unblocks cards 4 and 8)

Target: `HilbertSchmidt.resolventTrace thetaKernelMatrix z = -Xi_C'(z)/Xi_C(z)` (sign/shift TBD),
then `HilbertSchmidt.fredholmDet_weld` finishes (8) immediately, and (6)'s multiplicity is the
order of vanishing of `thetaFredholmDet`.
Everything else is BUILT: `thetaKernelMatrix`, `isHS_thetaKernelMatrix`, `thetaFredholmDet`,
`logDeriv_thetaFredholmDet`, `differentiableOn_thetaFredholmDet`.
Two routes, both research-level:
* B1 Lidskii for a NON-self-adjoint trace-class operator (`tr(B^m) = ∑ λ_j^m`), then match with
  the Hadamard product `RHTower/XiHadamardFactorization.lean`.  The corpus Lidskii is
  self-adjoint only and `B` is not self-adjoint (`RBR = -B`).
* B2 Grushin–Schur: factor the bordered pencil as `(invertible) ∘ diag(I, Xi_C(z)/Xi_C(0))` and
  push it through `det₂`, which is multiplicative only up to `exp(-tr((A-I)(B-I)))` — that
  correction term must be computed.
`HTGeometry/SourceGrushinInverse.lean` currently gives only KERNEL equivalence, not determinants.

## PLAN C — unbounded Fredholm  (closes ALL of card 6's operator half in one go)

Card 6 already has EVERY statement's core-level content in Lean.  What is missing is uniform: the
passage core-identity ⟹ operator-statement after closure.  Needed, none of which mathlib has:
`IsFredholm` for `LinearPMap`, the index, compact resolvent, and self-adjointness of a 2×2 block
Dirac operator.  mathlib supplies only `LinearPMap.adjoint`, `.closure`, `.IsClosable`.
Build order: closability of `D` on `C_c^∞` in `H_k` (use `integral_weighted_symmetry` for the
symmetric-pair criterion) → identify `A^*` with the maximal `L` → closed range from the explicit
two-ended solution → index −1 from `ker A = 0` (`not_integrable_const_mul_inv_thetaSource`) and
`ker A^* = ℂ k` (`integral_range_pairing`).

## PLAN A step 1 BUILT (2026-08-07)

`HedenmalmTwoPrimeNormalFrame`: `centeredMultiplierZero n k = 2πk/log n`,
`centeredMultiplierZero_ne_zero` (n ≥ 2, k ≠ 0), `norm_centeredMultiplierZero`, and
`summable_inv_sq_centeredMultiplierZero` — `Summable (fun k : ℤ => 1/‖w_k‖²)`.

That is EXACTLY the hypothesis of
`RHTower.canonicalProductE1Indexed_hasProdLocallyUniformlyOn`, so the Weierstrass product over the
zeros of `a_n` can now be formed (index over `ℤ`, and Lean's `1/0 = 0` makes the k = 0 term
harmless — `Real.summable_one_div_int_pow` covers the whole of `ℤ`).

Next in Plan A: form the canonical product `G_n` over these zeros, show `G_n` and `a_n` have the
same divisor (use `movingCanonicalProduct_eq_zero_iff` and `centeredMultiplier_eq_zero_iff`), then
the interpolation series.

## PLAN A step 2 BUILT (2026-08-07)

`centeredZero n : {j : ℤ // j ≠ 0} → ℂ` (the zeros of `a_n` on the nonzero integers),
`centeredZero_ne_zero`, `summable_inv_sq_centeredZero` (`Summable.subtype` off the ℤ version),
`centeredCanonicalProduct n := canonicalProductE1Indexed (centeredZero n)`, and
`hasProdLocallyUniformlyOn_centeredCanonicalProduct` — the genus-one Weierstrass product over the
zeros of `a_n` now EXISTS in Lean.

Plan A remaining: (3) show `centeredCanonicalProduct n` and `centeredMultiplier n` have the same
divisor away from 0 (`movingCanonicalProduct_eq_zero_iff`-style + `centeredMultiplier_eq_zero_iff`);
(4) the interpolation series with convergence factors; (5) Wedderburn.

## PLAN A step 3 (partial) BUILT (2026-08-07)

`analyticOnNhd_centeredCanonicalProduct` (entire) and `centeredCanonicalProduct_ne_zero`
(vanishes only on the prescribed set) — both one-liners off
`canonicalProductE1Indexed_analytic` / `canonicalProductE1Indexed_ne_zero`.

So the Weierstrass side of Plan A is COMPLETE: an entire function with exactly the zeros of `a_n`
(as a set) is now available.  What is left of step 3 is the divisor MATCH (same zeros AND same
simple order) against `centeredMultiplier_eq_zero_iff`; then step 4, the interpolation series,
which is the analytic bulk of Plan A.

## PLAN A step 3 COMPLETE (2026-08-07)

`centeredMultiplier_eq_zero_iff_mem_zeros (hn : 2 ≤ n) (hz : z ≠ 0) :`
`centeredMultiplier n z = 0 ↔ ∃ k : {j // j ≠ 0}, z = centeredZero n k`.
So the divisor of `a_n` off the origin is EXACTLY the zero set of the canonical product.

TRAP (already in memory, hit again): `push_cast`/`field_simp` rewrite `((Real.log n : ℝ) : ℂ)`
into `Complex.log ↑n`, which then never matches.  Prove a local `hcast` with
`simp only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_intCast]; norm_num`
and drive the algebra with `eq_div_iff` / `div_mul_cancel₀` instead.

Plan A remaining: (4) the interpolation series (the analytic bulk), (5) Wedderburn.

## PLAN A step 4 — the simplicity sub-lemma has a ready-made tool (2026-08-07)

`AnalyticAt.analyticOrderAt_eq_one_of_zero_deriv_ne_zero`
(`Mathlib/Analysis/Analytic/Order.lean:328`) — if `f x = 0` and `deriv f x ≠ 0` then
`analyticOrderAt f x = 1`.  (Companion: `analyticOrderAt_sub_eq_one_of_deriv_ne_zero`, and
`AnalyticAt.analyticOrderAt_eq_natCast` for the general `(z - z₀)^n • g` characterisation.)

So the simplicity of the zeros of `a_n` needs only:
1. `analyticAt_centeredMultiplier n hz` (BUILT);
2. `centeredMultiplier n w_k = 0` (BUILT, `centeredMultiplier_eq_zero_iff_mem_zeros`);
3. `deriv (centeredMultiplier n) w_k ≠ 0`.
For (3): from `centeredMultiplier_eq_sin` (`a_n z = 2c·sin(z l)/z`, l = log n / 2), the quotient
rule at `w` with `sin(w l) = 0` gives `a_n'(w) = 2c·l·cos(w l)/w`, and `w·l = π k` so
`cos(w l) = (-1)^k ≠ 0`.  `centeredMultiplier_eq_sin` holds only off the origin, so use
`HasDerivAt.congr_of_eventuallyEq` on the open set `{z ≠ 0}`.

That gives the simple-divisor match; then the interpolation series (per-index convergence factors,
`Summable` bookkeeping) is the remaining bulk of Plan A.

## PLAN A: the derivative of a_n is BUILT (2026-08-07)

`hasDerivAt_centeredMultiplier (n) (hw : w ≠ 0)` — quotient rule on
`a_n z = 2c·sin(z l)/z`, transferred to `centeredMultiplier` by
`HasDerivAt.congr_of_eventuallyEq` on the open set `{z ≠ 0}` (`isOpen_ne.mem_nhds hw`).

Trap: `((hasDerivAt_id w).mul_const l).csin` produces `id x * l` and `1 * l` in the statement;
wrap it in `by have h := …; simpa using h`.

Remaining for the simplicity lemma: evaluate that derivative at `w_k`, where `sin(w_k l) = 0` and
`cos(w_k l) = cos(π k) = (-1)^k ≠ 0`, then apply
`AnalyticAt.analyticOrderAt_eq_one_of_zero_deriv_ne_zero`.
Need `w_k * l = π k` — immediate from `centeredZero`/`centeredMultiplierZero` and
`l = log n / 2` (watch the `Real.log` cast trap: never `push_cast` through it).

## PLAN A IS COMPLETE (2026-08-07): card 5's (13)/(14)/(17)-cokernel are proved

Four new modules, all axiom-clean on [propext, Classical.choice, Quot.sound]:

1. `HTGeometry/EntireInterpolation.lean` — `exists_entire_interpolation`.
   **Mittag-Leffler interpolation at simple zeros.**  Series
   `sum_i c_i (z/w_i)^{N_i} * dslope F (w_i) z / deriv F (w_i)`.
   Key mathlib tools: `dslope` + `Complex.differentiableOn_dslope` (entire term, kills the
   removable singularity), `tendstoUniformlyOn_tsum_of_cofinite_eventually` (the M-test only needs
   the bound for COFINITELY many indices — this is what makes the per-disc argument work),
   `TendstoLocallyUniformlyOn.differentiableOn`, `tsum_eq_single`.
   Choice of `N_i`: `exists_pow_lt_of_lt_one` with tolerance `u i / (A i + 1)`.
   Majorant on a general countable index: `exists_injective_nat` then `(1/2)^(e i)`,
   summable by `Summable.comp_injective`.

2. `HTGeometry/EntireBezout.lean` — `exists_entire_quotient`, `exists_entire_bezout`.
   **Analytic division** via the meromorphic normal form:
   `toMeromorphicNFOn (f/g) univ`, `meromorphicNFOn_toMeromorphicNFOn`,
   `MeromorphicOn.divisor_of_toMeromorphicNFOn`, `meromorphicOrderAt_div`,
   `MeromorphicNFOn.divisor_nonneg_iff_analyticOnNhd`, then
   `MeromorphicOn.toMeromorphicNFOn_eq_self_on_nhdsNE` + the identity theorem
   (`AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq`) to get the global factorization.
   **Wedderburn** = interpolate `1/g` at the zeros of `f`, then divide `1 - a g` by `f`.

3. `RHTower/HedenmalmTwoPrimeBezout.lean` — `centeredMultiplierE` (the ENTIRE representative;
   the corpus `centeredMultiplier` has the Lean junk value 0 at the origin, NOT `n^{-1/2} log n`),
   `exists_two_prime_bezout`.

4. `RHTower/HedenmalmTwoPrimeIdeal.lean` — `span_entireCenteredWindow_eq_xiIdeal` (14),
   `range_windowRow`, `twoPrimeCokernelEquiv` (17).  Reuses the corpus `DeningerEntire`
   subalgebra and `deningerEntireXiIdeal` from `DeningerEntireQuotientCohomology.lean`.

TRAPS hit:
- `((hasDerivAt_id w).mul_const l).csin` leaves `id x * l` and `1 * l`; clean with
  `simp only [id_eq, one_mul] at h; exact h`.
- `pow_le_pow_left` is now `pow_le_pow_left₀`.
- `ENat.one_le_iff_ne_zero` deprecated -> `Order.one_le_iff_ne_zero`.
- `ENat.map_eq_top_iff` takes NO argument.
- `Ideal.span_le` will not fire on `deningerEntireXiIdeal ≤ _`; unfold the def first, or use
  `Ideal.span_singleton_le_iff_mem`.
- `rcases hx with rfl | rfl` on `x ∈ ({a, b} : Set _)` needs
  `simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx` first.
- `field_simp at h; rcases h with h|h` on a real equation can make `rcases` attempt dependent
  elimination on `Quot.mk CauSeq.equiv`; multiply through with `congrArg` instead.

## CARD 5 PROMOTED TO STAGE 3 (2026-08-07)

`docs/drafts/pipeline/3-formalized/new_scientific_knowledge/hedenmalm/`
`hedenmalm-two-prime-theta-interval-normal-frame.md` + `-formalized.md` companion.
Last additions: `(8)` evenness/reality (`centeredMultiplierE_neg`, `centeredMultiplierE_conj`),
`(11)` conormal module (`principalCotangentEquiv`, `xiConormalEquiv`),
`(12)` generation (`span_windowCotangent_eq_top`),
`(21)` (`essential_pair_ne_zero`).
**4 of 11 cards now in stage 3.**

## THE FOLDER HAS 11 CARDS, NOT 9

Two more were added to stage 2 since the earlier count:
`theta-compact-boundary-flux-energy.md`, `theta-compact-squared-seam-pencil.md`.
Both already have their Lean targets built
(`HedenmalmThetaCompactFluxEnergy.lean`, `HedenmalmThetaSquaredSeamPencil.lean`).

## CONCURRENCY WARNING — MULTIPLE CLAUDE SESSIONS SHARE THIS TREE

At least five `claude` processes run against `/Users/michael/Documents/code/hgt` simultaneously.
Observed this session:
- `HedenmalmThetaCompactFluxEnergy.lean` grew from 97 to 267 lines WHILE I was writing a module
  proving the same theorem (`Re<R2 v_q,v_q> = 2 M Im(z) E_q`).  I deleted my duplicate
  `HedenmalmThetaCompactBoundaryFlux.lean`; the other session's version is better (it has the
  general-`z` lemma `inner_pinnedBoundaryCLM_thetaDivisorEigenmode`).
- Another session already built `HedenmalmTwoPrimeBezoutGrowthNoGo.lean` on top of my
  `HedenmalmTwoPrimeBezout.lean` within minutes of my creating it.
- Other sessions run `git add`/`git commit`, so my new files appear already tracked.

RULES ADOPTED:
1. NEVER rewrite a whole file with `python3`/`cat >` unless this session created it in this
   session.  Use the `Edit` tool (targeted replacement) for umbrellas and shared modules.
2. Re-read a shared file immediately before editing; `wc -l` it first if it was read long ago.
3. `test -f` before any `cat >` (already a rule; it did not catch this case because the
   collision was in a DIFFERENT file that grew).
4. Before starting a card, check `find GaloisForLFunctions -name '*.lean' -newermt '<1h ago>'`
   to see where other sessions are working.
5. The memory ledger goes stale fast.  Card 9 was recorded as "untouched, one gate"; it is in
   fact ~95 % formalized by other sessions, with only the closability/domain theorem and the
   closed-form Guinand-Weil prime formula open.

## NEW GENERAL ASSETS BUILT THIS SESSION (all axiom-clean)

| module | content |
|---|---|
| `HTGeometry/EntireInterpolation.lean` | `exists_entire_interpolation` — Mittag-Leffler |
| `HTGeometry/EntireBezout.lean` | `exists_entire_quotient` (analytic division), `exists_entire_bezout` (Wedderburn) |
| `HTGeometry/PrincipalConormal.lean` | `principalCotangentEquiv` — `R/(g) ≃ (g)/(g)²` |
| `HTGeometry/UnboundedFredholm.lean` | `LinearPMap.kernel`, `.rangeSubmodule`, `.IsFredholm`, `.index`, `index_eq_neg_one_of_injective_of_range_eq_ker`, `isFredholm_of_injective_of_range_eq_ker` |
| `RHTower/HedenmalmTwoPrimeBezout.lean` | `centeredMultiplierE` + `exists_two_prime_bezout` |
| `RHTower/HedenmalmTwoPrimeIdeal.lean` | `(14)`, `(17)`, `(11)`, `(12)` |

`UnboundedFredholm` is the abstract half of card 6's missing layer.  Card 6's `(4)` now reduces to
two CONCRETE analytic facts at the theta source:
  (a) `ker (A + alpha) = ⊥` on `H_k`;
  (b) `range (A + alpha) = ker φ_alpha` where `φ_alpha f = ∫ f conj(g_alpha)/k`.
The corpus already has `⊆` of (b) (`integral_range_pairing`) and the explicit solution
(`twoEndedSolution_equation`); what is missing is that the solution lies in `H_k`.

Lean traps added: `IsClosed` is SHADOWED inside `namespace LinearPMap` by `LinearPMap.IsClosed`
— write `_root_.IsClosed`.  `LinearPMap.ker`/`LinearPMap.range` DO NOT EXIST in mathlib.

## Card 7 (9): the quantile calibration half is BUILT (2026-08-07)

`RHTower/HedenmalmQuantileSliceMoment.lean` — `abs_pinnedKernelSlice_le_weight`,
`sliceDominant`, `integrable_sliceDominant`,
`integrable_quantileSpeed_mul_pinnedKernelSlice`, `sliceMoment`,
`sliceMoment_sub_of_le`, `sliceMoment_add_quantileFun_eq`.

KEY ANALYTIC POINT: `q` is NOT integrable on `(0,1)` (∫q = ∫dx = ∞), so no naive splitting of
`∫ q(t)(1_{s≤t} − t) dt` is allowed.  The working domination is
  `|1_{s≤t} − t| ≤ t(1−t)/min(s,1−s)`   (proved: `abs_pinnedKernelSlice_le_weight`)
combined with AM-GM `q·w ≤ (q²w + w)/2` for `w = t(1−t) ≥ 0`, so the integrand is dominated by
`(q²t(1−t) + t(1−t))/(2 min(s,1−s))`, integrable by `HasFiniteKernelEnergy` plus a constant.
NO Cauchy-Schwarz needed.

THE REMAINING TWO STEPS OF (9), in order:
1. Pin the constant: `∫₀¹ sliceMoment S s ds = 0`, giving `sliceMoment S s = -Q s`.
   Fubini on `(0,1)²`; the product integrand `q(t)(1_{s≤t}−t)` has
   `∫₀¹|1_{s≤t}−t| ds = 2t(1−t)`, so the iterated absolute integral is `∫ 2q(t)t(1−t) < ∞`.
   WARNING: there is NO uniform-in-`s` dominating function (`t(1−t)/min(s,1−s)` is not
   `s`-integrable, and `|1_{s≤t}−t| ≤ 1` gives the non-integrable `q`), so this must go through
   Tonelli on the iterated integral, not through `Integrable.mono'`.
   Then `∫₀¹Q = 0` (`integral_quantileFun`) fixes the constant to 0.
2. `tr(B²) = ∬ K(t,u)K(u,t)`.  Derivation that AVOIDS constructing the adjoint as a kernel
   operator: `opTrace (B∘B) = ∑_i ⟪e_i, B(B e_i)⟫`; write `B f (t) = ⟪y_t, f⟫`, so
   `⟪e_i,B(Be_i)⟫ = ∬ conj(e_i(t)) conj(y_t(u)) ⟪y_u,e_i⟫ du dt`, and Parseval
   `∑_i ⟪y_u,e_i⟫ conj(e_i(t)) = conj(y_u(t))` collapses the sum.  With `K(t,u) = conj(y_t(u))`
   this is `∬ K(t,u)K(u,t)`.
   Then `K(t,u)K(u,t) = q(t)q(u)(min(t,u) − t u)` (the `-i` squares to `-1` and the sign flips),
   and `min(t,u) − tu = ∫₀¹ (1_{s≤t}−t)(1_{s≤u}−u) ds`, so Fubini gives
   `∫₀¹ (sliceMoment S s)² ds = ∫₀¹ Q² = M⁻¹∫x²k` — which is `integral_sq_quantileFun`.

## Card 7 (9) STEP 1 IS CLOSED — the constant is pinned (2026-08-08)

`sliceMoment_eq_neg_quantileFun : sliceMoment thetaSource s = -Q s` for `s ∈ Ioo 0 1`.

**The Fubini was NOT needed.**  The additive constant is pinned by reflection instead:
- `quantileFun_one_sub : Q (1-s) = -Q s`   (from `cdfFun_neg` + `quantile_cdfFun`)
- `quantileSpeed_one_sub : q (1-t) = q t`  (k even)
- `sliceMoment_one_sub (s) : sliceMoment (1-s) = -sliceMoment s`
  (via `intervalIntegral.integral_comp_sub_left` with `d = 1`, `a = 0`, `b = 1`; the two integrands
  differ only at `t = s`, a null set — filter on `t ≠ s` AND `t ≠ 1`, because `quantileSpeed_one_sub`
  needs `t ∈ Ioo 0 1` and `Ι 0 1 = Ioc 0 1` contains 1)
- combined with `sliceMoment_add_quantileFun_eq` (constancy) at `s` and `1-s`: `2(F+Q) = 0`.

Also banked: `integral_sq_sliceMoment : ∫₀¹ (sliceMoment s)² = M⁻¹∫x²k`.

**(9) IS NOW EXACTLY ONE STATEMENT**: `thetaTraceSq = ∬ K(t,u)K(u,t) dt du`.
Then `K(t,u)K(u,t) = q(t)q(u)(min(t,u) − tu)` and
`min(t,u) − tu = ∫₀¹(1_{s≤t}−t)(1_{s≤u}−u)ds` gives `∫₀¹(sliceMoment s)² ds` by Fubini,
which `integral_sq_sliceMoment` evaluates.

Lean traps added:
- `le_of_not_le` no longer exists; use `not_le.mp h |>.le`.
- `ae_iff.mpr (by simp)` proves `∀ᵐ t, t ≠ c` directly; do not hand-build it from
  `measure_singleton` (the `NullSingletonClass` instance gets stuck on metavariables).
- `continuousOn_quantileSpeed` is AMBIGUOUS (both `HedenmalmHilbertSchmidt` and
  `HedenmalmQuantile` export it); qualify it.

## Card 7 (9): the transposed row is BUILT (2026-08-08)

`RHTower/HedenmalmTransposeKernelField.lean` — `transposeKernelFun`,
`transposeKernelFun_eq_conj`, `norm_transposeKernelFun`, `measurable_transposeKernelFun`,
`memLp_transposeKernelFun`, `transposeKernelVec`, `transposeKernelVec_coeFn`.

Orientation, so nobody re-derives it wrongly:
`pinnedKernelFun S t u = i q(t) (1_{u≤t} − t)` is `K(t,u)`, the row of `B` at `t`.
`(B* g)(t) = ∫ conj(K(u,t)) g(u) du`, so the row of `B*` at `t` is
`transposeKernelFun S t u = conj(K(u,t)) = -i q(u)(1_{t≤u} − u)` — the speed is at `u`, INSIDE the
vector, not an outside scalar.  That is why the corpus template
(`pinnedKernelVec_eq_smul` + `continuous_pinnedSliceVec`) does NOT transfer: `q ∉ L²(0,1)`
(`∫q² = ∫ M/k dx = ∞`), so the row cannot be split into two L² pieces.
The energy is finite only through `abs_pinnedKernelSlice_le_weight` plus `u(1−u) ≤ 1/4`.

REMAINING for (9), in order:
1. `t ↦ transposeKernelVec t` is L²-continuous on `(0,1)`:
   `‖v_t − v_{t'}‖² = ∫_{Ico t' t} q(u)² du`, continuous because `q` is continuous on `(0,1)`
   so `q²` is locally integrable there and its primitive is continuous.
2. hence `AEStronglyMeasurable`, then `MemLp … 2` for the FIELD
   `t ↦ innerSL ℂ (conj-adjusted transposeKernelVec t)` — total energy
   `∫_t ‖v_t‖² dt = ∫_u q(u)² u(1−u) du` (one Fubini, or dominate).
3. `adjoint thetaKernelOperator = kernelOperator μ transposeKernelL2`.
4. `thetaTraceSq = hsInner (adjoint B) B` (BUILT: `thetaTraceSq_eq_hsInner`) and then
   `hsInner_kernelOperator` (BUILT, `RHTower/KernelOperatorPolarization.lean`) gives the double
   integral; `integral_sq_sliceMoment` finishes.

## Card 7 (9): the transposed family is L²-CONTINUOUS (2026-08-08)

Added to `RHTower/HedenmalmTransposeKernelField.lean`:
`norm_sq_transposeKernelFun_sub`, `integral_norm_sq_transposeKernelFun_sub`,
`transposeVec` (TOTAL function, `dif_pos` on `Ioo 0 1`, else 0), `transposeVec_coeFn`,
`norm_sq_transposeVec_sub`, `norm_sq_transposeVec_sub'`,
`setIntegral_quantileSpeed_sq_le`, `continuousOn_transposeVec`.

The mechanism: `‖v_t − v_{t'}‖² = ∫_{Ico t' t} q²`, and on a compact `[a,b] ⊂ (0,1)` the
continuous `q²` is bounded by some `C`, so `‖v_t − v_{t₀}‖² ≤ C|t−t₀|`.  NO primitive/FTC needed —
just `setIntegral_mono_on` against the constant.  Take `a = t₀/2`, `b = (t₀+1)/2`.

REMAINING for (9):
1. `transposeKernelField S hfin t := innerSL ℂ (-(transposeVec S hfin t))`.
   The sign is right because `conj (transposeKernelFun S t u) = -transposeKernelFun S t u`
   (the function is `i` times a real), so the Riesz vector of the functional
   `f ↦ ∫ transposeKernelFun S t u * f u du` is exactly `-transposeVec S hfin t`.
   `ContinuousOn` then `AEStronglyMeasurable` exactly as `aestronglyMeasurable_pinnedKernelField`.
2. `MemLp (transposeKernelField …) 2 μ`: `‖field t‖ = ‖v_t‖`, and
   `∫_t ‖v_t‖² dt = ∫_u q(u)² u(1−u) du` — this DOES need the product measure, but in the order
   with `u` OUTSIDE: `f(u,t) = q(u)² slice(u,t)²` has
   - a.e. `u`: `Integrable (fun t => …)` (bounded × probability measure);
   - `Integrable (fun u => ∫_t f(u,t) dt) = Integrable (fun u => q(u)² u(1−u))` = `HasFiniteKernelEnergy`
     (using `integral_pinnedKernelSlice_sq` in the form `∫_t slice(u,t)² dt = u(1−u)`).
   Then `Integrable.integral_prod_left` gives `Integrable (fun t => ∫_u f(u,t) du)`.
   NOTE: there is NO uniform bound on `‖v_t‖²` — it blows up as `t → 0` or `1` — so the product
   route is unavoidable here.
3. `adjoint thetaKernelOperator = kernelOperator μ transposeKernelL2`.
4. `thetaTraceSq_eq_hsInner` + `hsInner_kernelOperator` + `integral_sq_sliceMoment` finish.

## Card 7 (9): the ADJOINT FIELD IS BUILT (2026-08-08)

`RHTower/HedenmalmTransposeKernelField.lean` now has the full field:
`conj_transposeKernelFun`, `transposeKernelField`, `transposeKernelField_apply`,
`norm_transposeKernelField`, `continuousOn_transposeKernelField`,
`aestronglyMeasurable_transposeKernelField`, `norm_sq_transposeVec`,
`measurable_uncurry_slice_sq`, `memLp_transposeKernelField`, `transposeKernelL2`.

`transposeKernelField S hfin t := innerSL ℂ (-(transposeVec S hfin t))` — the minus sign is forced
by `conj_transposeKernelFun : conj (K*(t,u)) = -K*(t,u)`.

The energy proof: `∫_t ‖v_t‖² dt` is a genuine product-measure statement (no uniform bound; the
energy diverges at both endpoints).  It goes through `integrable_prod_iff` with the FIRST variable
outside — inner integral `q(u)²∫_t slice(u,t)²dt = q(u)²u(1−u)`, outer integrability is exactly
`HasFiniteKernelEnergy` — then `Integrable.integral_prod_right` transposes it.

TRAPS:
- `integrable_prod_iff` DOES cause an isDefEq timeout if the a.e.-slice measurability is supplied by
  `(uncurry-measurable).comp measurable_prodMk_left`.  Prove the slice measurability DIRECTLY for
  fixed `u` (`Measurable.ite measurableSet_Iic …`) and it goes through; `maxHeartbeats 2000000`
  is still needed on the declaration.
- `set_option … in` must come BEFORE the docstring, not between docstring and `theorem`.
- `measurable_prodMk_left` has no argument named `a`.

REMAINING for (9) — ONE STEP:
`adjoint thetaKernelOperator = kernelOperator unitIntervalMeasure (transposeKernelL2 …)`.
Use `ContinuousLinearMap.eq_adjoint_iff`: reduce to
`⟪(kernelOperator T) f, g⟫ = ⟪f, B g⟫`, which is the Fubini
`∬ K(u,t) conj(f u) g(t)` in the two orders.  Integrability of the 2-D integrand:
`memLp_tensor` (in `HedenmalmThetaTrace.lean`) + `integrable_sq_norm_uncurry_pinnedKernelFun`
+ `MemLp.integrable_mul`.
Then `thetaTraceSq_eq_hsInner` + `hsInner_kernelOperator` + `integral_sq_sliceMoment` close (9).

## Card 7 (9): THE ADJOINT IDENTIFICATION IS PROVED (2026-08-08)

`adjoint_kernelOperator_eq (S) (hfin) :`
`  adjoint (kernelOperator μ (pinnedKernelL2 S hfin)) = kernelOperator μ (transposeKernelL2 S hfin)`

This was the structural blocker of (9) since the start.  Proof: `ContinuousLinearMap.eq_adjoint_iff`
then the Fubini `integral_integral_swap` on
`F t u = pinnedKernelFun S u t * conj(f u) * g t`, whose product-integrability is
`(memLp_swap_pinnedKernelFun).integrable_mul (memLp_tensor f g)`.
Support lemmas added: `kernelOperator_ae_of_field` (general coeFn of a kernel operator),
`transposeKernelL2_coeFn`, `pinnedKernelL2_coeFn`, `memLp_swap_pinnedKernelFun`,
`neg_mul_pinnedKernelSlice`.

TRAP: `rw [transposeKernelL2]` / `rw [pinnedKernelL2]` FAIL ("failed to rewrite using equation
theorems") — these are `MemLp.toLp` defs.  Use a `coeFn` lemma (`MemLp.coeFn_toLp` stated ABOUT the
def) and `rw [show … from h]` instead.

REMAINING for (9) — the double-integral evaluation only:
`thetaTraceSq_eq_hsInner` + `hsInner_kernelOperator` give
`tr(B²) = ∫_t ⟪toDual.symm (pinnedKernelL2 t), toDual.symm (transposeKernelL2 t)⟫ dt`.
The Riesz vectors are `-(i q(t)) • pinnedSliceVec t` and `-(transposeVec t)`, so this is
`∫_t (-i q(t)) ∫_u slice(t,u) (-i q(u)) slice(u,t) du dt = -∬ q(t)q(u) slice(t,u)slice(u,t)`.
Then `neg_mul_pinnedKernelSlice` (off-diagonal; the diagonal is null) gives
`∬ q(t)q(u)(min(t,u) − t u)`, and
`min(t,u) − tu = ∫₀¹ pinnedKernelSlice t s * pinnedKernelSlice u s ds`
(check by the four sign cases; each `∫₀¹ 1_{s≤c} ds = c` for `c ∈ [0,1]`)
turns it into `∫₀¹ (sliceMoment s)² ds = integral_sq_sliceMoment`.

## Card 7 (9): the covariance decomposition is PROVED (2026-08-08)

`integral_pinnedKernelSlice_mul (ht) (hu) (hle : t ≤ u) : ∫₀¹ slice(t,s) slice(u,s) ds = t(1-u)`
`integral_pinnedKernelSlice_mul_min (ht) (hu) : ∫₀¹ slice(t,s) slice(u,s) ds = min t u - t u`

Proof is the corpus `integral_pinnedKernelSlice_sq` template with a THREE-way split
`Ioo 0 1 = Ioc 0 t ∪ Ioc t u ∪ Ioo u 1` (do it as two nested two-way splits), the integrand
constant on each piece: `(1-t)(1-u)`, `-t(1-u)`, `t u`, with measures `t`, `u-t`, `1-u`.
`Measure.integrableOn_of_bounded` supplies integrability on each piece.
TRAP: `hint _ measurableSet_Ioc …` cannot infer the set; name it.

EVERY INGREDIENT OF (9) IS NOW FORMALIZED.  What is left is only the two assembly interchanges:
(a) evaluate `hsInner_kernelOperator` at the two Riesz vectors
    (`-(i q(t)) • pinnedSliceVec t` and `-transposeVec t`) to reach
    `-∬ q(t)q(u) slice(t,u) slice(u,t)`;
(b) Fubini the `ds`-decomposition to reach `∫₀¹ (sliceMoment s)² ds`,
    then `integral_sq_sliceMoment`.

## Card 7 (9): FIRST DISPLAYED EQUALITY PROVED (2026-08-08)

`RHTower/HedenmalmThetaTraceKernel.lean`:
`thetaTraceSq_eq_double_integral : thetaTraceSq = ∬ q(t) q(u) (min(t,u) − t u) du dt`
— i.e. `tr(B²) = 2∫_{x<y} p(x)(1−p(y)) dx dy` in quantile coordinates.

Chain: `thetaTraceSq_eq_hsInner` → `adjoint_kernelOperator_eq` → `hsInner_kernelOperator`
→ Riesz vectors (`toDual_symm_innerSL`; `toDual ℂ E v = innerSL ℂ v` is proved by `ext y; rfl`)
→ `inner_riesz_eq` → `neg_mul_pinnedKernelSlice` off the diagonal (`{u = t}` is null under
`unitIntervalMeasure`; get it by `ae_restrict_of_ae (ae_iff.mpr (by simp))`).

TRAP: `rw [transposeKernelFun]` fails ("failed to rewrite using equation theorems") even though it
is a plain def; `simp only [transposeKernelFun]` works.

REMAINING for (9): only the SECOND displayed equality,
`∬ q(t)q(u)(min(t,u) − tu) = M⁻¹∫x²k`.
Substitute `integral_pinnedKernelSlice_mul_min` and interchange twice:
  `∫_u q(u)(min(t,u)−tu) du = ∫_s slice(t,s) · sliceMoment s ds`   (Fubini in (u,s))
  `∫_t q(t) ∫_s slice(t,s) sliceMoment s ds dt = ∫_s (sliceMoment s)² ds`  (Fubini in (t,s))
then `integral_sq_sliceMoment`.
For the product integrability the useful bound is
`∫_u q(u)|slice(u,s)| du ≤ A + |Q(s) − Q(1/2)|` with `A = ∫_u q(u)|slice(u,1/2)| du`,
because `|slice(u,s)| ≤ 1_{[min(s,1/2),max(s,1/2))}(u) + |slice(u,1/2)|` and
`∫ q · 1_{[a,b)} = Q(b) − Q(a)`; `Q ∈ L¹(0,1)` via `integrableOn_comp_quantileFun_iff`
(ALREADY IN THE CORPUS, `HTGeometry/PositiveDensityQuantile.lean`) applied to `g = id`,
whose right-hand side is `integrable_mul_thetaSource`.

## Card 7 (9): two more support lemmas (2026-08-08)

`integral_quantileSpeed_indicator_Ico (S) (ha) (hb) (hab) :`
`  ∫ t, (Ico a b).indicator (quantileSpeed S) t ∂μ = Q b - Q a`
— the FTC on the unit interval, extracted so the endpoint behaviour never appears.

`integrableOn_quantileFun_thetaSource : IntegrableOn Q (Ioo 0 1) volume`
— via the corpus `PositiveDensitySource.integrableOn_comp_quantileFun_iff` (g = id) and
`integrable_mul_thetaSource`.  NOTE: `integral_quantileFun` and `integral_sq_quantileFun` were
proved through `integral_comp_quantile`, which is an equality of integrals and does NOT establish
integrability; that is why this lemma was still needed.

These are the two inputs to the bound
`∫_t q(t)|slice(t,s)| dt ≤ A + |Q s - Q (1/2)|`, `A = ∫_t q(t)|slice(t,1/2)| dt`,
which is the product-integrability hypothesis for the LAST Fubini of (9)
(the one that must be taken with `s` OUTSIDE — with `t` outside the iterated bound diverges).

## Card 7 (9): the majorant of the first interchange (2026-08-08)

`integral_abs_pinnedKernelSlice (hu) : ∫ s in Ioo 0 1, |pinnedKernelSlice u s| = 2 u (1-u)`
(two-way split at `s = u`; the integrand is `1-u` on `Ioc 0 u` and `u` on `Ioo u 1`).

This is what makes the FIRST of the two remaining interchanges work:
`G(u,s) = q(u) slice(t,s) slice(u,s)` is dominated by `q(u)|slice(u,s)|`, whose iterated integral
with `u` OUTSIDE is `∫_u q(u) · 2u(1-u) du`, finite by AM-GM against `HasFiniteKernelEnergy`.

The SECOND interchange (`H(t,s) = q(t) slice(t,s) sliceMoment s`) must be taken with `s` OUTSIDE
and still needs two things NOT yet in the tree:
  (i) `∫_t q(t)|slice(t,s)| dt ≤ A + |Q s - Q(1/2)|`, from
      `|slice(t,s)| ≤ 1_{Ico(min(s,1/2),max(s,1/2))}(t) + |slice(t,1/2)|` and
      `integral_quantileSpeed_indicator_Ico`;
  (ii) `Q ∈ L²(0,1)`, i.e. `Integrable (fun x => x^2 * thetaCuspFullSource x)` — CONFIRMED ABSENT
      from the corpus (only the first-moment `integrable_mul_thetaSource` exists), so it must be
      built on the `thetaBound * exp(-|x|)` envelope like its first-moment sibling.
      Note mathlib has no `integrable_pow_mul_exp_neg_mul_abs`; the corpus's
      `integrable_abs_mul_exp_neg_mul_abs` is the degree-one case only, and
      `integrable_sq_mul_exp_neg_abs` in `MobiusIncidenceClockGiniFisherFourUnit.lean` is `private`.

## Card 7 (9): the "absent" second-moment dependency was NOT absent (2026-08-08)

CORRECTION to the previous note.  `Integrable (fun x => x^2 * thetaCuspFullSource x)` is three
lines, because the source IS Schwartz:
  `thetaCuspSchwartzReal.integrable_pow_mul (volume) 2` gives `Integrable (‖x‖^k * ‖φ x‖)`,
  and `Integrable.mono'` against it closes `integrable_sq_mul_thetaSource`.
No envelope argument, no `integrable_pow_mul_exp_neg_mul_abs` needed.
(The general corpus lemma `integrable_abs_pow_mul_exp_neg_mul_abs (k) (hc)` in
`RHTower/ThetaCuspFourierLaplace.lean` also exists if a non-Schwartz source ever needs it, and
`SuzukiSafeBoundaryThetaCumulantWall.lean` has `integrable_pow_mul_exp_mul_thetaCuspFullSource`.)

Built with it: `integrableOn_sq_quantileFun_thetaSource` (Q ∈ L²(0,1)),
`quantileFun_le_quantileFun` (monotonicity of Q, derived from
`integral_quantileSpeed_indicator_Ico` and `quantileSpeed_pos` — the corpus had NO monotonicity
lemma for `quantileFun`), and `abs_pinnedKernelSlice_sub`
(`|slice(t,s) − slice(t,c)| = 1_{Ico(min s c, max s c)}(t)`).

TRAP: in the two unit branches of `abs_pinnedKernelSlice_sub`, `simp`/`norm_num` do NOT close
`|0 - t - (1 - t)| = 1`; use `abs_of_nonpos (by linarith)` then `ring`.

ALL inputs of the last Fubini of (9) are now in the tree.  What is left is only:
  `absSliceMoment s := ∫_t q(t)|slice(t,s)| dt ≤ absSliceMoment (1/2) + |Q s − Q(1/2)|`
  (immediate from `abs_pinnedKernelSlice_sub` + `integral_quantileSpeed_indicator_Ico`
   + `quantileFun_le_quantileFun`), then the two interchanges.

## Card 7 (9): the last majorant is BUILT (2026-08-08)

`absSliceMoment S s := ∫_t q(t) |slice(t,s)| dt`
`absSliceMoment_le : absSliceMoment S s ≤ absSliceMoment S c + |Q s − Q c|`
plus `integrable_quantileSpeed_mul_abs_pinnedKernelSlice` and `integrableOn_quantileSpeed_Ico`.

Mechanism: `|slice(t,s)| ≤ 1_{Ico(min s c, max s c)}(t) + |slice(t,c)|` (triangle inequality on
`abs_pinnedKernelSlice_sub`), integrate, and `integral_quantileSpeed_indicator_Ico` +
`quantileFun_le_quantileFun` turn the indicator term into `|Q s − Q c|`.

TRAPS: `abs_add` is now `abs_add_le`.  `integral_mono` produces the goal in the Pi-add form
`∫ (f + g) x`; `simp only [Pi.add_apply]` before `rw [integral_add …]`.

EVERY INPUT of card 7 (9) IS NOW IN THE TREE.  The remaining work is exactly two Fubini
interchanges, with their integrability now available:
 (A) `∫_u q(u)(min(t,u)−tu) du = ∫_s slice(t,s) · sliceMoment s ds`
     dominate `q(u)slice(t,s)slice(u,s)` by `q(u)|slice(u,s)|`, whose `u`-outer iterated integral
     is `∫_u q(u)·2u(1−u) du` (`integral_abs_pinnedKernelSlice` + AM-GM against `hfin`).
 (B) `∫_t q(t) ∫_s slice(t,s) sliceMoment s ds dt = ∫_s (sliceMoment s)² ds`
     take `s` OUTSIDE (with `t` outside the iterated bound diverges); the `s`-inner integral is
     `|Q s| · absSliceMoment s ≤ |Q s|(A + |Q s| + |Q(1/2)|)`, integrable by
     `integrableOn_quantileFun_thetaSource` and `integrableOn_sq_quantileFun_thetaSource`.
Then `integral_sq_sliceMoment` gives `M⁻¹∫x²k` and (9) is closed.

## CARD 7 STATEMENT (9) IS CLOSED (2026-08-08)

`thetaTraceSq_eq_source_variance : thetaTraceSq = ((M⁻¹ ∫ x² k(x) dx : ℝ) : ℂ)`
in `RHTower/HedenmalmThetaTraceKernel.lean`, together with
`thetaTraceSq_eq_double_integral` (the first displayed equality) and the two interchanges
`integral_quantileSpeed_min_sub`, `integral_double_min_sub_eq` with their product integrability
`integrable_uncurry_abs_slice`, `integrable_uncurry_slice_quantile`.

The two interchanges, and why the ORDER matters:
- FIRST (`u` outside): dominate `q(u) slice(t,s) slice(u,s)` by `q(u)|slice(u,s)|`; the inner
  integral is `∫_s |slice(u,s)| ds = 2u(1−u)` (`integral_abs_pinnedKernelSlice`), so the outer is
  `∫ q(u)·2u(1−u) du`, finite by AM-GM against `HasFiniteKernelEnergy`.
- SECOND (`s` outside — with `t` outside the iterated bound DIVERGES since `∫q = ∞`): majorant
  `|Q s|(A + |Q s − Q(1/2)|)` from `absSliceMoment_le`, integrable because `Q ∈ L¹ ∩ L²`
  (`integrableOn_quantileFun_thetaSource`, `integrableOn_sq_quantileFun_thetaSource`).
  Stated with `-Q` in place of `sliceMoment` so the integrand is manifestly measurable.

TRAPS: after `rw [integrable_prod_iff …]` the goals carry `Function.uncurry` beta-redexes —
`simp only [Function.uncurry]` before any `rw`/`exact`.  `AEStronglyMeasurable.integral_prod_right'`
supplies the measurability of `fun x => ∫ y, ‖f (x,y)‖`.

CARD 7 NOW NEEDS ONLY `(6)`-multiplicity and `(8)`.  Card 4's sole blocker is `(6)`-multiplicity.

## CORRECTION (2026-08-08): the corpus `fredholmDet` is DISC-LOCAL and NOWHERE ZERO

`HilbertSchmidt.fredholmDet K z := Complex.exp (-fredholmExp K z)` where
`fredholmExp K z = ∑_{n≥2} zⁿ/n · tr(Kⁿ)` converges ONLY for `‖z‖ · hsNorm K < 1`.
Hence `fredholmDet_ne_zero` is literally `Complex.exp_ne_zero`, and
`fredholmDet_weld` concludes only `∀ z ∈ ball 0 r, fredholmDet K z = c * L z`.

**Card 7 `(8)` (`det₂(I+zB) = Ξ_C(z)/Ξ_C(0)`) therefore CANNOT be proved with it** — the right-hand
side vanishes at every Xi zero, the left-hand side never vanishes.  My earlier ledger entry
"(8) is reduced to one identification; `fredholmDet_weld` finishes it" was WRONG, and the card said
the same; both are now corrected.

What IS reachable with the corpus objects: the disc-local identity
`fredholmDet thetaKernelMatrix z = c · Ξ_C(z)/Ξ_C(0)` for `|z| < 1/‖B‖_HS`, still requiring
`resolventTrace thetaKernelMatrix = −Ξ_C'/Ξ_C` there.

The GLOBAL `(8)` needs the ENTIRE Hilbert–Carleman determinant (exterior-power series
`∑ zⁿ tr(Λⁿ K)`, order-2 entire, zeros = reciprocal eigenvalues).  Absent from corpus AND mathlib.
It is ALSO what `(6)`-multiplicity needs, since algebraic multiplicity = order of vanishing of that
determinant.  So cards 4, 7, 8 all sit behind ONE missing layer: the entire regularized determinant.

Process lesson (again): a corpus `def` whose name matches the mathematics is not the mathematics.
`fredholmDet` is named for `det₂` but is only its local exponential representative.  READ THE DEF.

## The missing layer now has its own card (2026-08-08)

`docs/drafts/pipeline/1-in-progress/entire-regularized-fredholm-determinant.md`
— the entire Hilbert–Carleman determinant, with the exact obstruction, the classification of the
corpus object, the blocked-clause table for cards 4/7/8, and the two routes
(Plemelj–Smithies recursion + Carleman bound; exterior powers + Hadamard).
Cards 4 and 8 now carry a pointer to it.

STATE OF THE FOLDER (11 cards):
  stage 3 (4): quantile-volterra, reflection-folded-dirac, theta-flat-borel-holonomy,
               two-prime-theta-interval-normal-frame
  stage 2 (7): prime-translation-rank-one-anomaly      — blocked on the entire det₂ (via card 7)
               supersymmetric-fredholm-range-divisor   — needs the weighted unbounded Fredholm theorem
               theta-source-compressed-inverse-determinant — (6)-mult + (8), both = entire det₂
               essential-inverse-flow-prime-tomography — all inherited from card 7
               pair-weil-polarization-law              — closability/domain + closed-form Guinand–Weil
               theta-compact-boundary-flux-energy      — worked by ANOTHER SESSION; looked complete
               theta-compact-squared-seam-pencil       — worked by ANOTHER SESSION; looked complete

So the 7 remaining cards reduce to THREE research-level layers:
  (I)   the entire regularized determinant   → cards 4, 7, 8
  (II)  unbounded weighted Fredholm theory   → card 6   (abstract half BUILT: HTGeometry/UnboundedFredholm.lean)
  (III) closability + closed-form Guinand–Weil → card 9
plus promotion of the two theta-compact cards, which another session appears to have finished.

## 2026-08-08 — session 3

### Promotions (stage 2 -> stage 3)

Three cards were already fully formalized by a concurrent session and were verified and promoted:

* `theta-compact-boundary-flux-energy` (`HedenmalmThetaCompactFluxEnergy.lean`)
* `theta-compact-squared-seam-pencil` (`HedenmalmThetaSquaredSeamPencil.lean`)
* `theta-compact-source-entropy-boundary-weld` (`HedenmalmThetaSourceEntropyBoundaryWeld.lean`)

Each got a `-formalized.md` certificate.  All declarations `#print axioms`-clean.
Folder state is now **7 of 12 in stage 3**; the five still in stage 2 are

| card | what is missing |
|---|---|
| `prime-translation-rank-one-anomaly` | Jordan length of `(16)` = algebraic multiplicity |
| `supersymmetric-fredholm-range-divisor` | the operator-level weighted Fredholm theorem |
| `theta-source-compressed-inverse-determinant` | multiplicity clause of `(6)`, and `(8)` |
| `essential-inverse-flow-prime-tomography` | everything inherited from the card above |
| `pair-weil-polarization-law` | closed-form Guinand--Weil extension; closability/domain |

### New infrastructure: the entire regularized determinant, route C

Route C is **finite sections + Cauchy's estimate**.  It gives the Carleman coefficient bound for
free and needs neither Hadamard's inequality nor exterior powers.  Steps 1--3 are formalized:

* `HTGeometry/SchurTriangulation.lean` — `exists_eigenpair`, `exists_unitary_col_zero`,
  `embedSucc`, **`exists_schur_triangulation`**.  Mathlib has **no** Schur decomposition (verified
  by grep over the whole tree); this is new corpus infrastructure and reusable far beyond this card.
* `HTGeometry/FiniteRegularizedDeterminant.lean` — `matHSNormSq` and its unitary invariance,
  `diag_pow_of_blockTriangular`, `det_one_add_smul_eq_prod`, `trace_eq_sum_diag`,
  `trace_pow_eq_sum_diag`, **Schur's inequality** `sum_diag_normSq_le_matHSNormSq`, the scalar
  inequality **`norm_one_add_mul_exp_neg_le`** (`|(1+w)e^{-w}| <= exp(|w|^2/2)`, which is just
  `log u <= u - 1` for `u = |1+w|^2`), `finiteDet2`, `differentiable_finiteDet2`,
  `finiteDet2_eq_prod`, and **`norm_finiteDet2_le`** (the Carleman growth bound).
* `HTGeometry/EntireOrderTwoSeries.lean` — `taylorCoeff`, `hasSum_taylorCoeff`,
  **`norm_taylorCoeff_le`** (Cauchy's estimate in coefficient form, from mathlib's
  `Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le`), `summable_of_orderTwo_bound`,
  `entireOfCoeffs`, `differentiable_entireOfCoeffs`, `norm_taylorCoeff_finiteDet2_le`.
* `HTGeometry/RegularizedDeterminantEntire.lean` — **`IsRegularizedDet`**, `.unique`,
  `.eq_one_at_zero`, `isRegularizedDet_of_logDeriv_eq`.

Two facts worth remembering:

1. **No optimisation of `R` is needed.**  For a coefficient bound `|a_n| <= exp(R^2 c/2)/R^n` valid
   for every `R > 0`, the single choice `R = 2|z|` turns `sum |a_n||z|^n` into
   `exp(2|z|^2 c) sum 2^-n`.  Carleman's `(e/n)^(n/2)` is never needed.
2. **The general existence theorem is not needed for card `theta-source-compressed-inverse-determinant`.**
   `IsRegularizedDet K D` is *defined* by "entire and equal to `fredholmDet K` on a disc"; it is
   unique by the identity theorem, and for the theta kernel the witness is `Xi_C(z)/Xi_C(0)` itself
   (entire, and nonvanishing on `|z| ‖B‖_HS < 1` because a zero forces `|1/z| <= ‖B‖_op`).  So `(8)`
   reduces, via `isRegularizedDet_of_logDeriv_eq`, to the **single trace formula**

   ```text
   Xi_C'(z)/Xi_C(z) = - resolventTrace (-B) z = sum_{n>=1} (-1)^n z^n tr(B^{n+1}).
   ```

   That trace formula is the remaining hard core of `(8)`.  The general `det_2` construction is what
   the *multiplicity* clause of `(6)` needs, and that is a separate obligation.

### Still to build for route C

* truncation of a Hilbert--Schmidt kernel: `‖K_s‖_HS <= ‖K‖_HS` and `tr(K_s^m) -> tr(K^m)`
  (best done through `hsTrace_hsPow_succ` + submultiplicativity, i.e. continuity of the trace in
  HS norm, not by a multi-index limit);
* the matrix/kernel bridge identifying `finiteDet2` of the truncation with `fredholmDet` of the
  truncated kernel on the disc;
* zeros = reciprocal eigenvalues, and order of vanishing = algebraic multiplicity.

Card: `docs/drafts/pipeline/1-in-progress/entire-regularized-fredholm-determinant.md`.

### 2026-08-08, later — step 4 of route C

`HTGeometry/HilbertSchmidtContinuity.lean` and `HTGeometry/HilbertSchmidtTruncation.lean`:

* the kernel-level Hilbert--Schmidt layer had **no** additivity at all (only the operator-level
  `E →L[k] F` layer did) — `isHS_add`, `isHS_sub`, `hsNorm_add_le`, `hsNorm_neg`, `hsNorm_sub_le`,
  `hsComp_sub_left/right`, `hsNorm_hsComp_le`, `hsInner_sub_left/right` are new;
* `hsNorm_hsPow_sub_le` — powers are Lipschitz on a norm ball, from
  `A^{m+1} - B^{m+1} = A(A^m - B^m) + (A - B)B^m`;
* `hsTrace_hsPow_sub_norm_le` — **the power traces are Lipschitz**, via `hsTrace_hsPow_succ`
  (`tr(K^{n+1}) = <K^H, K^n>_HS`) and Cauchy--Schwarz;
* `truncKernel`, `tendsto_hsNorm_sub_truncKernel`, `tendsto_hsTrace_hsPow_truncKernel`.

Two Lean traps recorded:

* `tsum_subtype` will **not** unify `{x // x ∉ s ×ˢ s}` with `↥{x | x ∉ s ×ˢ s}` (the
  `SummationFilter.unconditional` argument blocks it).  Avoid subtype tails entirely: write the
  truncation energy as `hsNormSq K - ∑ p ∈ s ×ˢ s, ‖K p‖^2` and use `Summable.hasSum` directly as a
  `Tendsto ... atTop`, composed with cofinality of square blocks.
* `tsum_le_tsum` no longer exists as a root name; it is `Summable.tsum_le_tsum`.

Also: the lint gate flagged `HedenmalmThetaSourceEntropyBoundaryWeld` as unreachable from the
`RHTower` umbrella — a concurrent session had created the module without wiring it.  Wired.  The
other ~24 unreachable-module lint errors belong to other sessions' in-flight work, not to this one.

### 2026-08-08, step 4 closed except the limit assembly

* `HTGeometry/HilbertSchmidtBlockMatrix.lean` — `ofBlock` (zero-extension of a matrix on `↥s`),
  `blockMatrix`, `truncKernel_eq_ofBlock`, `hsComp_ofBlock`, `hsPow_ofBlock`,
  **`hsTrace_hsPow_truncKernel`** (kernel power traces = matrix power traces),
  `matHSNormSq_blockMatrix`, `matHSNormSq_blockMatrix_le`.
* `HTGeometry/FiniteDeterminantLogSeries.lean` — `tsum_pow_div_add_two`
  (`sum_k w^(k+2)/(k+2) = -log(1-w) - w`), `exp_neg_tsum_pow_div_add_two`,
  `norm_diag_le_of_schur`, **`exp_neg_traceSeries_eq_finiteDet2_neg`** and
  **`fredholmDet_truncKernel_eq`**.
* `FiniteRegularizedDeterminant.lean` and the Carleman coefficient bound now hold for a matrix over
  **any** finite index type, by reindexing to `Fin (card m)` (`finiteDet2_submatrix`,
  `matHSNormSq_submatrix`, `trace_submatrix_equiv`, `trace_pow_submatrix`).

The remaining assembly, with its estimate already worked out on paper:

```text
|fredholmExp K_s z - fredholmExp K z|
  <= sum_k r^(k+2)/(k+2) * (k+2) M^(k+1) ‖K_s - K‖_HS
   = ‖K_s - K‖_HS * r^2 M / (1 - rM)     on |z| <= r,  rM < 1, M = ‖K‖_HS.
```

The `(k+2)` of `hsTrace_hsPow_sub_norm_le` **cancels** the `1/(k+2)` of `fredholmExp`, so the
convergence is uniform on the closed disc with an explicit constant.  Then `exp` is uniformly
continuous on the bounded set the exponents live in, Cauchy's estimate applied to the *difference*
gives convergence of the Taylor coefficients, those inherit
`‖a_n‖ <= exp(R^2 ‖K‖_HS^2/2)/R^n` for every `R > 0`, and `entireOfCoeffs` of the limit is the
entire `det_2`.

Lean names to reuse: `norm_taylorCoeff_le` (Cauchy), `summable_of_orderTwo_bound`,
`differentiable_entireOfCoeffs`, `Complex.hasSum_taylorSeries_on_ball`, `fredholmDet_differentiableOn`.

### 2026-08-08 — THE ENTIRE REGULARIZED DETERMINANT EXISTS IN LEAN

`HTGeometry/RegularizedDeterminantExists.lean` and `HTGeometry/RegularizedDeterminantLimit.lean`
close route C:

```text
exists_isRegularizedDet : IsHS K -> ∃ D, IsRegularizedDet K D
```

for a kernel over any index type with `DecidableEq`.  With `IsRegularizedDet.unique` (identity
theorem) the entire Hilbert--Carleman determinant is now a well-posed Lean object.  Every
declaration is `#print axioms`-clean.

The proof, in the exact form that worked:

* `M := ‖K‖_HS + 1`, `r := 1/(2M)`, so `rM = 1/2` — no case split on `K = 0` is needed.
* `norm_fredholmExp_le` and **`norm_fredholmExp_sub_le`**: on `|z| <= r`,
  `|fredholmExp A z - fredholmExp B z| <= ‖A - B‖_HS * r^2 M/(1 - rM)`.  The `(k+2)` of
  `hsTrace_hsPow_sub_norm_le` cancels the `1/(k+2)` of the series; that cancellation is the whole
  reason the estimate is clean.
* `norm_fredholmDet_sub_le`: factor `e^{-E_A} - e^{-E_B} = e^{-E_B}(e^{E_B - E_A} - 1)` and use
  `Complex.norm_exp_sub_one_le` (valid for `‖w‖ <= 1`, which holds eventually).
* `norm_taylorCoeff_le'` — Cauchy's estimate for a function merely `DiffContOnCl` on a ball
  (mathlib's `Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le`), applied to the
  *difference*; `iteratedDeriv_sub` needs `ContDiffAt`, obtained from
  `DifferentiableOn.analyticAt` + `AnalyticAt.contDiffAt`.
* the limit coefficients inherit `‖a_n‖ <= exp(R^2 ‖K‖_HS^2/2)/R^n` by `le_of_tendsto`, and
  `differentiable_entireOfCoeffs` makes `entireOfCoeffs a` entire; it equals `fredholmDet K` on
  `ball 0 r` by `Complex.hasSum_taylorSeries_on_ball`.

What is still open on that card: **the zeros**.  `det_2(1 - zK) = 0` iff `1/z` is an eigenvalue,
order of vanishing = algebraic multiplicity, and the Plemelj identity on the full resolvent set.

For `hedenmalm-theta-source-compressed-inverse-determinant` statement `(8)` the route is now
completely mechanical *given* the trace formula: `isRegularizedDet_of_logDeriv_eq` turns `(8)` into

```text
Xi_C'(z)/Xi_C(z) = - resolventTrace (-B) z    on |z| ‖B‖_HS < 1,
```

and `IsRegularizedDet.unique` makes "the regularized determinant" unambiguous.  That trace formula
is the remaining hard core of the card.

### 2026-08-08 — the determinant is a named function; finite zero theory complete

`entireDet2 K` (in `HTGeometry/RegularizedDeterminantLimit.lean`) is now a **definition**, not an
existential, with `isRegularizedDet_entireDet2`, `differentiable_entireDet2`, and

```text
tendsto_finiteDet2_entireDet2 : Tendsto (fun s => finiteDet2 (-(blockMatrix K s)) z) atTop
    (nhds (entireDet2 K z))
```

(pointwise; via `tendsto_tsum_of_dominated_convergence`, mathlib's Tannery theorem).  Supporting
API: `detRadius` (= `1/(2(‖K‖_HS + 1))`, so `r·(‖K‖_HS+1) = 1/2` and no `K = 0` case split is
needed), `detCoeff`, `detCoeff_truncKernel`, `norm_detCoeff_truncKernel_le`,
`tendsto_detCoeff_truncKernel`, `norm_detCoeff_le`.

`HTGeometry/FiniteDeterminantZeros.lean` finishes the finite-dimensional zero theory:
`finiteDet2_eq_zero_iff_det`, `finiteDet2_eq_zero_iff_exists_eigenvector`, and

```text
finiteDet2_factor : ∃ G entire, G z_0 ≠ 0 ∧ ∀ z, finiteDet2 M z = (z - z_0)^d * G z,
   d = #{i | T i i = -z_0⁻¹}
```

i.e. the order of vanishing **is** the eigenvalue multiplicity, by grouping the Schur product.

**The next obstruction is named: Hurwitz's theorem.**  Mathlib has Weierstrass
(`TendstoLocallyUniformlyOn.differentiableOn`) but no Hurwitz and no Montel.  To carry the finite
zero/multiplicity statements to `entireDet2` one needs (a) to upgrade
`tendsto_finiteDet2_entireDet2` from pointwise to locally uniform — which the existing coefficient
bound already gives, by the same `2^-n` majorant argument applied uniformly on a disc — and (b)
Hurwitz, provable from the argument principle (`Complex.circleIntegral` + `logDeriv`), which mathlib
does have the ingredients for.

### 2026-08-08 — Hurwitz's theorem, built from the maximum modulus principle

`HTGeometry/HurwitzZeroLimit.lean`:

```text
eventually_exists_zero_of_tendstoUniformlyOn :
  0 < r -> (∀ a, DiffContOnCl ℂ (F a) (ball c r)) -> ContinuousOn f (sphere c r) ->
  TendstoUniformlyOn F f p (closedBall c r) -> f c = 0 -> (∀ z ∈ sphere c r, f z ≠ 0) ->
  ∀ᶠ a in p, ∃ z ∈ ball c r, F a z = 0
```

**No argument principle and no Rouche are needed** — apply the maximum modulus principle
(`Complex.norm_le_of_forall_mem_frontier_norm_le`) to `1/F a`: if `F a` had no zero in the closed
disc then `‖1/F a (c)‖ <= 2/mn`, i.e. `‖F a c‖ >= mn/2`, contradicting `‖F a c - f c‖ < mn/2`.
Mathlib has neither Hurwitz nor Montel; this is new corpus infrastructure.

Also: `tendstoUniformlyOn_finiteDet2_entireDet2` upgrades the block-determinant convergence from
pointwise to **uniform on every closed disc**.  The trick is that the estimate is *scalar*: bound
`‖∑ (a_s n - a n) z^n‖` by `∑ ‖a_s n - a n‖ ρ^n`, which is independent of `z`, and send that to
zero by Tannery with majorant `2E·2^-n`.

Combining them, `HTGeometry/RegularizedDeterminantEigenvalues.lean`:

```text
eventually_exists_blockEigenvalue_near : a zero z_0 of entireDet2 K, isolated on a circle of radius
  r < ‖z_0‖, is a limit of reciprocal eigenvalues of the finite blocks blockMatrix K s.
```

Next obstruction: passing block eigenvectors to the limit, i.e. **upper semicontinuity of the
spectrum of compact operators under norm convergence** — also absent from mathlib.

### 2026-08-08 — the l2 lift and the compact-operator spectral limit

`HTGeometry/HilbertSchmidtBlockEigenvector.lean`: `liftBlock` / `liftBlockLp` (zero extension of a
block vector), `liftBlockLp_ne_zero`, **`toOperator_truncKernel_liftBlockLp`** (a block eigenvector
is an `l^2` eigenvector of the truncated operator with the same eigenvalue), `toOperator_sub`,
`norm_toOperator_sub_le`, **`tendsto_norm_toOperator_truncKernel_sub`** (the represented operators
converge in *operator* norm, not just Hilbert--Schmidt norm).

`HTGeometry/CompactOperatorSpectrumLimit.lean`: **`exists_eigenvector_of_tendsto_of_isCompactOperator`** —
if `‖S_a - T‖ -> 0`, `T` compact, `S_a v_a = lam_a v_a` with `‖v_a‖ = 1`, and `lam_a -> l != 0`,
then `l` is an eigenvalue of `T`.  Mathlib has no spectral semicontinuity for compact operators.

Lean idiom worth remembering: to work "along a subsequence" for a general filter, do **not** try to
extract one.  Take the cluster point `w` from `IsCompact.exists_mapClusterPt`, then use the finer
filter `q := p ⊓ comap u (nhds w)`; its non-triviality is exactly
`Filter.push_pull` + `Filter.map_neBot_iff` + `inf_comm`, `q ≤ p` is `inf_le_left`, and
`Tendsto u q (nhds w)` is `Filter.map_mono inf_le_right` composed with `Filter.map_comap_le`.
Also proved: `mapClusterPt_of_tendsto_dist_zero`.

**The one remaining step** for "zeros of `entireDet2 K` = reciprocal eigenvalues of `K`": Hurwitz
gives, for *each* radius `r`, an eventual block eigenvalue in `ball z_0 r`; the spectral limit
theorem consumes a *single* family `lam s -> z_0⁻¹`.  Producing that family is a diagonal argument
over the filter, needing `atTop` on `Finset ι` countably generated — true for `ι = ℕ`, which is the
theta case.

### 2026-08-08 — zeros of the entire determinant ARE reciprocal eigenvalues

`HTGeometry/RegularizedDeterminantEigenvalueLimit.lean`:

```text
exists_eigenvector_of_entireDet2_eq_zero :
  IsHS K -> z_0 ≠ 0 -> entireDet2 K z_0 = 0 -> ∃ w ≠ 0, toOperator hK w = z_0⁻¹ • w
```

**No diagonal argument was needed.**  The obstacle recorded last round — Hurwitz gives a witness
per radius, the spectral limit theorem wants one convergent family — dissolves by taking, for each
block, the point of `blockSpectrum K s` **nearest** to `1/z_0`: the block spectrum is closed (zero
set of `charpoly.eval`), `ℂ` is proper, so `IsClosed.exists_infDist_eq_dist` supplies the minimiser,
and Hurwitz says `infDist -> 0`.

Supporting: `blockSpectrum`, `isClosed_blockSpectrum`, `mem_blockSpectrum_iff`,
`eventually_entireDet2_ne_zero` (zeros isolated, because `entireDet2 K 0 = 1` rules out the
identically-zero branch of `AnalyticAt.eventually_eq_zero_or_eventually_ne_zero`),
`exists_radius_isolating`, `tendsto_infDist_blockSpectrum`, `eventually_blockSpectrum_nonempty`.
`exists_eigenvector_of_tendsto_of_isCompactOperator` was weakened to **eventual** hypotheses.

Next: the converse (an eigenvalue is a zero), then order of vanishing = algebraic multiplicity.

### 2026-08-08 — the entire determinant, instantiated at the theta source

`RHTower/HedenmalmThetaEntireDeterminant.lean`: **`thetaEntireDet2 := entireDet2 thetaKernelMatrix`**,
with `differentiable_thetaEntireDet2`, `isRegularizedDet_thetaEntireDet2`, `thetaEntireDet2_zero`
(= 1), `eq_thetaEntireDet2_of_isRegularizedDet` (uniqueness), `thetaEntireDet2_eq_thetaFredholmDet`
(agreement with the corpus disc-local object near the origin), and

```text
exists_eigenvector_of_thetaEntireDet2_eq_zero :
  z_0 ≠ 0 -> thetaEntireDet2 z_0 = 0 -> ∃ f ≠ 0, thetaKernelOperator f = z_0⁻¹ • f
```

transported through `thetaCoord` using `toOperator_matrixOf`.  The card
`hedenmalm-theta-source-compressed-inverse-determinant` was updated: its `(8)` no longer waits on a
missing object, only on the **trace formula** `Xi_C'/Xi_C = -resolventTrace(-B)` on the disc, after
which `isRegularizedDet_of_logDeriv_eq` + `eq_thetaEntireDet2_of_isRegularizedDet` close it.

### 2026-08-08 — the computational core of the argument principle

`HTGeometry/ArgumentPrincipleSingleZero.lean`:

```text
circleIntegral_logDeriv_of_factor :
  (∀ z ∈ ball c R, f z = (z - c)^d * g z) -> g analytic and nonvanishing on ball c R ->
  0 < r < R -> ∮ z in C(c,r), deriv f z / f z = 2 pi I d
```

Mathlib has **no argument principle, no Rouche, no Montel** (verified by grep).  This is the piece
that the multiplicity-counting form of Hurwitz needs.  Ingredients used:
`circleIntegral.integral_sub_inv_of_mem_ball`, `circleIntegral_eq_zero_of_differentiable_on_off_countable`,
`circleIntegral.integral_add`, `ContinuousOn.circleIntegrable`.

Trap: `circleIntegrable_sub_inv_iff.mpr (Or.inl rfl)` sends the elaborator into a whnf blow-up
(1M heartbeats not enough).  Prove circle integrability of `(z - c)⁻¹` on the sphere through
`ContinuousOn.circleIntegrable` instead — instant.

Still missing for "order of vanishing = algebraic multiplicity": the *global* factorization of an
analytic function with finitely many zeros in a disc, and the passage `∮ f_n'/f_n -> ∮ f'/f`.

### 2026-08-08 — the single-zero argument principle is complete

`HTGeometry/EntireZeroFactorization.lean`:

```text
exists_entire_factor_of_analyticOrderAt :
  Differentiable ℂ f -> analyticOrderAt f c = d -> (∀ z ≠ c, f z ≠ 0) ->
  ∃ g entire, (∀ z, g z ≠ 0) ∧ ∀ z, f z = (z - c)^d * g z

circleIntegral_logDeriv_eq_analyticOrder :  ∮ z in C(c,r), deriv f z / f z = 2 pi I d
```

The factorization is **the corpus's own `exists_entire_quotient`** (analytic division, built for the
two-prime frame card) applied to the divisor of `(z - c)^d` — `d` at `c` and `0` elsewhere
(`analyticOrderAt_sub_pow_self`, `analyticOrderAt_sub_pow_of_ne`).  No new division theory needed.

Left for the counting Hurwitz: the several-zero case (for the block determinants, whose Schur
product factors explicitly) and `∮ f_n'/f_n -> ∮ f'/f`, needing uniform convergence of `f_n` *and*
`f_n'` on the circle plus `f != 0` there.

### 2026-08-08 — the block determinant's logarithmic derivative

`HTGeometry/FiniteDeterminantArgumentPrinciple.lean`: `logDeriv_schurFactor`
(`logDeriv ((1 + w t) e^(-w t)) = t/(1 + z t) - t`), **`logDeriv_finiteDet2`** (the sum over the
Schur diagonal), `circleIntegral_const_eq_zero`, and **`circleIntegral_schurFactor_inside`** /
**`circleIntegral_schurFactor_outside`**: each factor contributes `2 pi I` exactly when `-1/t_i`
lies inside the circle, and `0` otherwise, because `t/(1 + z t) = (z - (-1/t))⁻¹`.

Lean traps recorded: `logDeriv_mul` and `logDeriv_prod` both mis-unify unless `f`, `g`, `x` are
given by name; and `logDeriv_prod`'s left side elaborates to the **beta-reduced**
`logDeriv (fun x => prod ... x)`, so a calc step must be written in that form, not as
`logDeriv (prod of lambdas)`.

### 2026-08-08 — the argument principle for a matrix determinant

`circleIntegral_logDeriv_finiteDet2`:

```text
∮ z in C(c,r), logDeriv (finiteDet2 M) z
  = 2 pi I * #{i | T i i ≠ 0 ∧ -(T i i)⁻¹ ∈ ball c r}
```

i.e. the contour integral counts the Schur eigenvalues whose negative reciprocal is inside — the
eigenvalue count with algebraic multiplicity.  Assembled from `logDeriv_finiteDet2`,
`circleIntegral.integral_fun_sum`, `circleIntegral_schurFactor_inside/_outside` and
`circleIntegrable_schurFactor`; the tail is `← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul`.
The statement needs `open scoped Classical in` for the filter's `DecidablePred`.

**Only the limit passage now separates this from "order of vanishing = algebraic multiplicity":**
`∮ f_n'/f_n -> ∮ f'/f`, needing uniform convergence of `f_n` (proved:
`tendstoUniformlyOn_finiteDet2_entireDet2`) and of `f_n'` (follows by Cauchy's estimate on the
difference), plus `f != 0` on the circle (proved: `exists_radius_isolating`).

Note: a concurrent session's blanket `git add -A` commit swept this file in; verified with
`git show HEAD:<path>` that the content is the one built here.
