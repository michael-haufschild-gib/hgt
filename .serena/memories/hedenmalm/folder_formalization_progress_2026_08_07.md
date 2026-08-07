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
