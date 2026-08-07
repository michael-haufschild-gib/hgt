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
