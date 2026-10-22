# Six NSK cards → stage 3: formalization ledger

Working ledger for the goal "formalize unconditionally in Lean every proven theorem of the six
`2-fully-proven/not_new_scientific_knowledge` cards listed below, then promote them to stage 3".

## Cards in scope

| # | Card | Lean state at ledger open (2026-08-19) |
|---|---|---|
| C1 | `hardy-critical-line-moment-anchor` | VanDerCorput, DigammaSeries/Uniform, HardyZ*, SmoothAFEGaussian* done; smooth AFE keystone, moments C/F, mean E, assembly open |
| C2 | `hardy-cyclicity-maximal-ht-field-blindness` | only `HTGeometry/CayleySchur.lean`; H²(D)/inner-outer/Beurling/model space/DA-independence missing |
| C3 | `f1-inversion-single-prime-stieltjes-collapse` | `HTGeometry/SymmetricBlockAlgebraicIndependence.lean` has `beurlingBlock`, esymm generation, esymm alg-independence |
| C4 | `faithful-krein-index-escape-stratification` | finite Krein inertia + measured-index blindness exist; analytic canonical product, N_κ topology, Fredholm families missing |
| C5 | `dyadic-squarefree-euler-fock-source-factorization` | one-prime factor formalized; global unitary + rank-two connection identity open |
| C6 | `horizontal-singleton-zero-fibers` | pointwise theorems in `RHTower/HorizontalSingletonZeroFiber.lean`; finite charging law + liminf passage open |

## Log

- 2026-08-19 — ledger opened; corpus reconnaissance done.

## 2026-08-19 session 1

### C6 `horizontal-singleton-zero-fibers` — card content DONE
New: `formal/GaloisForLFunctions/RHTower/HorizontalSingletonFiberCharging.lean` (wired into
`RHTower.lean`, olean built, axioms clean).  Contains `xiZeroCount`/`xiCriticalZeroCount`/
`xiOffLineZeroCount`/`xiSimpleCriticalZeroCount`/`xiSingletonFiberCount`,
`two_mul_xiSimpleCriticalZeroCount_le` (inequality (1)),
`xiSimpleCriticalRatio_sub_le_xiSingletonFiberRatio` (normalized form),
`le_liminf_xiSingletonFiberRatio` (inequality (2)),
`prattRoblesZaharescuZeindler_singleton_density` (the 0.116158438 corollary as an implication).
REMAINING: unconditional Lean providers for the two cited PRZZ proportions — external literature,
same lane as C1.

### C5 `dyadic-squarefree-euler-fock-source-factorization` — card content DONE
Seven new modules (all wired, oleans built, axioms clean):
`EulerSquarefreeDyadicStateFactorization`, `...LogTransport`, `...LogMoments`,
`...FisherTangent`, `...FisherDefect`, `...Tower`, `...AnalyticTelescope`.
Covers (1)-(35) of the card.  The card's three unchecked gates (prime-Gamma completion,
Sonin graph convergence, RH) are the declared successor programme, not theorems of the card.

### C4 `faithful-krein-index-escape-stratification` — substrate located (card Lean section is STALE)
Existing and directly reusable:
- `HTGeometry/MovingCanonicalSurgery.lean` — `movingCanonicalSurgeryProduct`,
  `movingCanonicalSurgeryCarrier_exact_negativeSquares`, `movingCanonicalSurgeryProduct_exactOrderOneDivisor`
- `HTGeometry/MovingEvenCanonicalSurgery.lean` — the functional-equation-even version
- `HTGeometry/MovingCanonicalSurgeryFieldInvariance.lean` — differential-field invariance under the
  rational surgery gauge, and `no_movingCanonicalSurgeryCount_selector_of_differentialAdjoin`
- `HTGeometry/MovingCanonicalFullTranslationFreeness.lean`, `FamilyPowerGauge.lean`
  (`not_familyDifferentiallyAlgebraicOn_translates_pow`), `MovingDivisorEntireFreeness.lean`
- `HTGeometry/HerglotzFiniteAtomicExactNegativeSquares.lean` — `CarrierHasExactlyNegativeSquares`
- `RHTower/CompactOpenKolchinWardChargeEscape.lean` — the Xi-side analogue of the escape family with
  full compact-open + all-jets convergence (`escapingQuartetGaugedXi_iteratedDeriv_tendstoLocallyUniformly`)
STILL TO BUILD for C4: (a) the normalized remote-pair gauge `A_(r,T)` and its all-derivative
compact-open convergence to 1; (b) exact index `k+r` for the multiplied carrier; (c) `P_N` equality
at every power level; (d) lower semicontinuity of the negative-square index; (e) the
continuous-Fredholm impossibility theorem.

### C1/C2/C3 — not started this session
- C1 `hardy-critical-line-moment-anchor`: substrate VanDerCorput/HardyZ*/SmoothAFEGaussian* present.
- C2 `hardy-cyclicity-maximal-ht-field-blindness`: needs analytic `H^2(D)`, inner-outer, Beurling.
- C3 `f1-inversion-single-prime-stieltjes-collapse`: `HTGeometry/SymmetricBlockAlgebraicIndependence.lean`
  has `beurlingBlock` + esymm generation; the corank-2 floor needs Gelfond--Schneider (not in mathlib).

### C4 progress (2026-08-19, same session)
New modules (all compile clean, wired into `HTGeometry.lean`):
- `HTGeometry/FaithfulIndexFredholmObstruction.lean` — `NegIndexAtMost`, `HasCoerciveComplement`
  (the gap form of "self-adjoint Fredholm at 0 with finite negative spectral subspace"),
  `finrank_le_of_trivial_meet_of_sup_eq_top`, `negIndexAtMost_of_coerciveComplement` (index
  stability), `no_faithful_continuous_index_of_unbounded_witness` (the obstruction).
- `HTGeometry/RemotePairEscapeGauge.lean` — `remotePairFactor`, `remotePairGauge` = `A_(r,T)`,
  explicit quadratic form, Schwarz reality, zeros, `neg_logDeriv_remotePairGauge = multiPairCarrier`,
  `tendstoLocallyUniformly_finset_prod`, `remotePairGauge_tendstoLocallyUniformly`,
  `remotePairGauge_mul_iteratedDeriv_tendstoLocallyUniformly` (all-derivative escape).
- `HTGeometry/KreinIndexEscapeStratification.lean` — `differentialAdjoin_range_pow_baseGauge_eq`
  (equation (4) at EVERY power level, fully general — also serves card C2 item 3),
  `multiPairCarrier_append`, `escapeCarrier`, `escapeCarrier_exact_negativeSquares` (index k+r),
  `exists_coercive_bound_on_subspace`, `eventually_negOn_subspace_of_entrywise_tendsto` and
  `eventually_carrier_negativeSquares_witness` (lower semicontinuity (12)),
  `no_continuous_faithful_krein_index` (the card's continuous-Fredholm obstruction).
- `HTGeometry/KreinEscapeAnalyticFamily.lean` — `kreinEscapeCarrier`,
  `kreinEscapeCarrier_exact_negativeSquares`, `kreinEscapeProduct = A_(r,T)·F_(θ,k)`,
  `neg_logDeriv_kreinEscapeProduct_eq`, `kreinEscapeProduct_iteratedDeriv_tendstoLocallyUniformly`.

STILL OPEN for C4: (i) exact order one and Schwarz reality of the gauged product; (ii) the
translation-orbit differential independence and the concrete `P_N` equality — needs the gauge
realized in `RatFunc ℂ` / `upperEndMeroField` like `movingCanonicalSurgeryGaugeRatFunc`;
(iii) the functional-equation-even version (10)–(11).

### C4 COMPLETE (2026-08-19)
All of statements 1–5, (6), the FE-even strengthening (10)–(11), the lower semicontinuity law (12)
and the continuous-Fredholm obstruction (13) are formalized unconditionally; see the card's
"Lean status update (2026-08-19)" section for the exact declaration list.  Six modules:
`RemotePairEscapeGauge`, `FaithfulIndexFredholmObstruction`, `KreinIndexEscapeStratification`,
`KreinEscapeAnalyticFamily`, `KreinEscapePowerFieldInvariance` (+ the pre-existing
`MovingCanonicalSurgery` stack).  All axioms clean.

### Next: C2 `hardy-cyclicity-maximal-ht-field-blindness`
Item 3 (`P_N(G_B) = P_N(O)` at every power level) is already covered by
`differentialAdjoin_range_pow_baseGauge_eq`.
Item 4 needs an analytic `H²(D)`: coefficient model `ℓ²(ℕ)`, polynomial density, multiplication by
a bounded analytic function, multiplication by a finite Blaschke product as an isometry with closed
range `B·H²`, and `dim(H² ⊖ B·H²) = deg B`.  NOTE: `[O] = H²(D)` does NOT need Beurling — `O` and
`O⁻¹` bounded analytic makes multiplication by `O` a bounded operator with bounded inverse, so it
carries the dense set of polynomials to a dense set.
Item 1 needs `|σ| < 1` from the Herglotz/Cayley construction (corpus `CayleySchur.lean`).
Item 2 needs the parent Herglotz full-translation freeness (corpus
`HerglotzFullTranslationFreeness.lean`) transported through the rational substitution `φ`, the
Cayley map and `exp`.

### C2 progress (2026-08-19, session 1 continued) — the analytic `H²(D)` layer is built
Six new modules, all wired into `GaloisForLFunctions.HTGeometry`, oleans built, axioms clean:

- `HTGeometry/HardyDiskGutzmer.lean` — `hasSum_circleAverage_normSq`: **Gutzmer's identity**
  `(2π)⁻¹∫‖f(re^{iθ})‖² dθ = ∑ ‖aₖ‖² r^{2k}` for any power series on a ball, via uniform convergence
  of the partial sums (builds on the corpus's `circleAverage_normSq_partialSum`).
- `HTGeometry/HardyDiskSpace.lean` — `diskCoeff` (canonical Taylor coefficients),
  `coeff_eq_diskCoeff`, `hasSum_circleAverage_normSq_diskCoeffOn`,
  `summable_diskCoeff_sq_of_circleAverage_le` (the `H²` criterion, from a left neighbourhood of
  `r = 1`); the coefficient model `HardyDisk = lp (fun _ : ℕ => ℂ) 2`, `hardyFun`, `hardySeries`,
  `diskCoeff_hardyFun`, `differentiableOn_hardyFun`, `circleAverage_hardyFun_le`.
- `HTGeometry/HardyDiskMultiplier.lean` — `diskCoeff_congr` (locality), `hardyDisk_ext`,
  `DiskMultiplier`, `circleAverage_mul_le`, `hardyMul` (**the bounded multiplication operator**,
  norm ≤ sup bound), `hardyFun_hardyMul`, `DiskMultiplier.mul/one`, `diskShift`, `hardyMul_mul`,
  `hardyMul_one`, `hardyMul_comm`, `hardyMul_congr`.
- `HTGeometry/HardyDiskCyclic.lean` — `hardyOne`, `hardyOf`, `polyMultiples`, `cyclicSubspace`,
  `shift_pow_hardyOne`, `cyclicSubspace_hardyOne = ⊤`, `hardyMul_surjective`,
  `topologicalClosure_map_eq_top`, `polyMultiples_map`, and
  **`cyclicSubspace_hardyOf_eq_top`: an invertible bounded analytic function is a cyclic vector**
  (this is `[O] = H²(D)`; no Beurling needed).
- `HTGeometry/HardyDiskBlaschke.lean` — `blaschkeFactor`, `blaschkeProd`, `FiniteBlaschke`
  (analytic on a ball of radius `2 − bound > 1`), `norm_fn_le_one` (via the corpus's
  `finite_blaschke_schur`), `norm_fn_eq_one` (unimodular on the circle), `toMultiplier`,
  `polyExtend`, and **`norm_hardyMul_blaschke`: multiplication by a finite Blaschke product is an
  isometry of `H²(D)`** (Gutzmer at `r = 1` on polynomials, then continuity).
- `HTGeometry/HardyDiskModelSpace.lean` — `hardyKernel` (Szegő kernel) with the reproducing
  property, `singleBlaschke`, **`range_hardyMul_singleBlaschke`: `range M_{b_a} = (ℂ ∙ k_a)ᗮ`**
  (the hard `⊇` direction via `dslope` + the `H²` criterion), and
  **`finrank_orthogonal_range_singleBlaschke = 1`**, plus
  **`cyclicSubspace_blaschke_mul`: `[B·O] = B·H²(D)`** for a cyclic `O`.

REMAINING for C2:
1. `dim (H² ⊖ B·H²) = deg B` for `deg > 1` — induction peeling one Blaschke factor, needing the
   orthogonal splitting `(T V)ᗮ = (range T)ᗮ ⊕ T(Vᗮ)` for an isometry `T`.
2. Item 1 of the card: the concrete carrier `O = exp(σ)` with `|σ| < 1` from the Herglotz/Cayley
   construction (`CayleySchur.lean`), giving `O, O⁻¹ ∈ H^∞` and hence a `DiskMultiplier` pair.
3. Item 2: differential algebraic independence of `{O ∘ τ_t}` — transport of the corpus's
   `HerglotzFullTranslationFreeness` through the rational substitution `φ`, the Cayley map and
   `exp`.
4. Item 3: instantiate `differentialAdjoin_range_pow_baseGauge_eq` (already proved, in
   `KreinIndexEscapeStratification.lean`) for the disk translates.

### C2 statements 1 and 4 COMPLETE (2026-08-19)
`HardyDiskModelDimension.lean` (orthogonal splitting for an isometry, `finrank_orthogonal_map_add`,
`finrank_orthogonal_range_blaschkeOf : dim (H² ⊖ B·H²) = deg B`) and
`HardyCyclicityGaugeBlindness.lean` (`expMultiplier`, `cyclicSubspace_expCarrier`,
capstone `hardyCyclicityDefect`) close statements 1 and 4 = equations (16) and (7).
All wired, oleans built, axioms clean.

REMAINING for C2: statements 2 and 3.
- The corpus's Herglotz freeness is
  `herglotz_fullTranslationCauchyFamilyFreeness_denseResidual` in
  `HTGeometry/HerglotzFullTranslationFreeness.lean`, stated in the **analytic**
  `FamilyDifferentiallyAlgebraicOn` language on `commonUpperTranslationDomain` — the convenient
  form for transport.
- Statement 2 needs three transport lemmas: (a) rational substitution `z = φ(w)`;
  (b) post-composition with the Cayley map `c` (rational invertible); (c) `exp` (via the
  logarithmic derivative and a differential-transcendence-degree count).
- Statement 3 then follows from `differentialAdjoin_range_pow_baseGauge_eq` once the orbit and the
  rational gauge `B ∘ τ_t` are realized in a differential field (do it in the `z`-coordinate, where
  `τ_t` is `z ↦ z + t` and `B ∘ τ_t` is a rational function of `z`).

### C3 started (2026-08-19) — and a PROOF ERROR found in the card's §2′
New module `HTGeometry/StieltjesCorankTrdeg.lean` (wired, olean built, axioms clean):
`blockCoeffVal`, `stieltjesVal`, `logField`, `stieltjesField`, `stieltjesField_le_logField`,
`beurlingBlock_one_coeff`, `stieltjesVal_single` (the exact `γ_k = B⁺_k L^{k−1}/k!` of §2),
`stieltjesField_single_eq` and `trdeg_stieltjesField_single` (the corank-one collapse, exact).

**Finding.**  §2′ claims the Laurent coefficients `a_k` recover `e_1,…,e_r`.  False for `r ≥ 3`:
`h(x)/h(−x) = e^x` makes `log h(x) − x/2` even, so
`ℚ(a_1,a_2,…) = ℚ(p_1, p_2, p_4, p_6, …)` — no odd power sums.  Concretely
`a_3 = e_1 e_2 / 24` (the `e_3` terms cancel exactly).
**Repair (verified, recorded on the card):** the even power sums are the power sums of the squares
`L_i²`, so Newton's identities give every `e_j(L²)`; hence each `L_i²`, and therefore each `L_i`,
is algebraic over the Laurent-coefficient field.  With `stieltjesField_le_logField` this gives the
§2′ transcendence-degree identity, with no positivity and without needing `1/e_r`.

Remaining C3 work: (1) formalize the repaired §2′ (`PowerSeries.log`, evenness, `B_{2k} ≠ 0`, then
mathlib's `MvPolynomial.mul_esymm_eq_sum`); (2) Hermite–Lindemann for `trdeg = 1`;
(3) Gelfond–Schneider for §2″; (4) Hölder/D-finite for §4.  mathlib has `PowerSeries.log`,
`MvPolynomial.psum`, Newton's identities; it does NOT have Lindemann, Gelfond–Schneider, or
`B_{2k} ≠ 0`.

### C1 started (2026-08-19) — Lemma F and the assembly step CLOSED
New module `RHTower/HardyFourthMomentSignChange.lean` (wired, olean built, axioms clean):
`cube_integral_sq_le` (the interpolation inequality `(∫f²)³ ≤ (∫|f|)²(∫f⁴)`),
`exists_sign_bracket_of_fourth_moment_gap`,
`exists_riemannZeta_line_zero_of_hardyZ_fourth_moment_gap` (the card's assembly),
`exists_integral_hardyZ_pow_four_dyadic_le_polylog` (**Lemma F**, from the corpus's already-proved
`exists_integral_Icc_norm_riemannZeta_line_pow_four_le_polylog`).
NOTE: the corpus turned out to contain ~60 `SmoothAFEZeta*` modules and a full `Sieve/Ingham*`
lane, so C1 is far ahead of what its own Gate-5 log said.  Remaining: Lemma C (second-moment lower
bound) and Lemma E (the `O(T^{3/4})` first moment of `Z`), then the dyadic `N₀(T) ≥ c log T`.

### C2 COMPLETE (2026-08-19) — statements 1, 2, 3, 4 all formalized

Three new modules (all wired into `GaloisForLFunctions.HTGeometry`, oleans built, axioms clean:
`propext, Classical.choice, Quot.sound`).

`HTGeometry/HardyCyclicityOrbitFreeness.lean` — **statement 2**.
- `realShiftConfiguration`, `mem_commonUpperTranslationDomain_of_im_pos` (for real translations the
  common upper domain is the whole open upper half plane);
- `cayleyToUpper_eq_mobius` (`φ` in Mobius normal form with `(a,b,c,d) = (i,i,−1,1)`, det `2i`);
- `not_familyDifferentiallyAlgebraicOn_parabolicOrbit` — transport of translation freeness through
  the change of variable `z = φ(w)` by `not_familyDifferentiallyAlgebraicOn_comp_mobius`;
- `outerCarrier_parabolicOrbitFreeness_denseResidual` — the residual capstone: every finite family
  of distinct real parabolic translates of the bounded outer carrier is differentially
  algebraically independent over the rational functions.
The Cayley-exponential half of the transport was ALREADY in the corpus
(`not_familyDifferentiallyAlgebraicOn_cayleyOuter`, `..._outerCauchyTranslates` in
`CayleyOuterFamilyGauge.lean`), as were `cayleyToUpper`/`cayleyToDisc`/`parabolicAut`/`outerCarrier`
(`ParabolicOuterOrbitLimit.lean`, `ParabolicCayleyAutomorphism.lean`).

`HTGeometry/HardyCyclicityPowerFieldInvariance.lean` — **statement 3**.
- the disc chart: `isPreconnected_openDisc`, `openDisc_nonempty`, `openDisc_infinite`;
- `analyticMero` (an analytic function as an element of `Bottcher.meroField openDisc`),
  `analyticMero_mul`, and `analyticMero_eq_ratfuncToMero` (**rational realization**: an analytic
  `f` with `Q·f = P` on the chart is the image of `P/Q` under `ℂ(w) ↪ M`);
- `parabolicNumPoly`/`parabolicDenPoly` and `parabolicAut_eq_div`: `τ_t(w) = ((2i−t)w+t)/(−tw+2i+t)`;
- `blaschkeFactorNumPoly`/`blaschkeFactorDenPoly`, `eval_blaschkeFactorDenPoly_mul`,
  `blaschkeFactorNumPoly_ne_zero`, and the products `blaschkeOrbitNumPoly`/`blaschkeOrbitDenPoly`,
  `eval_blaschkeOrbit_mul`, `blaschkeOrbitRat`, `blaschkeOrbitRat_ne_zero`;
- analyticity of both orbits on the disc, `carrierOrbitMero`, `gaugedOrbitMero`,
  `blaschkeOrbitMero_eq_ratfunc`;
- **`gaugedOrbit_differentialAdjoin_pow_eq`** — equation (6): `P_N(G_B) = P_N(O)` for every finite
  Blaschke product and every `N`, and **`gaugedOrbit_differentialIndependent_iff`**.

`HTGeometry/HardyCyclicityCarrierCapstone.lean` — the four statements for ONE object.
- `carrierExponent`, `differentiableOn_carrierExponent`, `norm_carrierExponent_lt_one`,
  `carrierMultiplier` (the carrier `O = exp σ` as a `DiskMultiplier`, `‖σ‖ < 1`);
- `expWeightedMeasure_ne_zero`;
- **`hardyCyclicityGaugeBlindness_carrier`**: for a dense residual set of exponential parameters the
  single carrier `O` satisfies statement 1 (`[O] = H²(D)`), statement 2 (maximal parabolic
  differential freeness), statement 3 (`P_N(B·O) = P_N(O)` for every `B`, `N`) and statement 4
  (`[B·O] = B·H²(D)` with defect exactly `deg B`).

C2 is ready for stage 3.

### C1 — Lemma C CLOSED (2026-08-19)

New module `formal/GaloisForLFunctions/RHTower/ZetaLineFirstMoment.lean` (wired into
`RHTower.lean`, olean built, axioms clean).  It proves the second-moment lower bound by a *first
moment* route, which is far cheaper than the card's sketched diagonal computation and gives the
same assembly input:

- `norm_exp_neg_I_mul_ofReal_mul`, `continuous_cpow_neg_linePt`, `integral_cpow_neg_linePt`,
  `norm_integral_cpow_neg_linePt_le` — each Dirichlet monomial `n^{-1/2-it}` integrates to
  `O(n^{-1/2}/log n)` over any window (built on the corpus's `natCast_cpow_neg_linePt` from
  `RHTower/FirstMoment.lean`);
- `rpow_neg_half_eq`, `sum_rpow_neg_half_le` (`Σ_{n≤K} n^{-1/2} ≤ 2√K`),
  `norm_sum_integral_osc_le` — the split-at-`M` bound
  `‖Σ_{1<n≤N} ∫ n^{-s}‖ ≤ 4√M/log 2 + 4√N/log M`;
- `continuous_emTail_line`, `norm_integral_linePt_mul_emTail_le` — the Euler–Maclaurin remainder
  contributes at most `(1+4T)T/√N` (corpus `norm_emTail_le`);
- `cpow_one_sub_linePt`, `emPoleAmp`, `hasDerivAt_emPoleAmp`, `norm_integral_emPole_line_le` —
  the explicit continuation term `N^{1-s}/(s-1)` contributes at most `3√N/(T log N)`, via the
  corpus's oscillation bound `RHTower.norm_integral_mul_exp_le` (`FirstMoment.lean`);
- **`norm_integral_riemannZeta_line_sub_le`** — `‖∫_T^{2T} ζ(1/2+it) dt − T‖` is bounded by the
  sum of those three errors, for every `2 ≤ M ≤ N`;
- `sq_norm_integral_riemannZeta_line_le` — Cauchy–Schwarz against the constant one
  (corpus `HTGeometry.sq_integral_le_length_mul`);
- **`exists_le_integral_norm_riemannZeta_line_sq`** and **`exists_le_integral_hardyZ_sq`** —
  taking `M = ⌈T⌉₊`, `N = ⌈65536 T²⌉₊`: for all large `T`,
  `∫_T^{2T} ‖ζ(1/2+it)‖² dt ≥ T/4` and `∫_T^{2T} Z(t)² dt ≥ T/4`, unconditionally.

Note on the route: the card's Lemma C asks for `≥ ½ T log T`.  The assembly only needs
`(∫Z)²·F < S³`; with `F = O(T log⁴T)` and the target `|∫Z| = O(T^{3/4})`, `S = T/4` is already
more than sufficient (`T³/64` versus `T^{3/2}·CT log⁴T`).  The first-moment route avoids the
diagonal/off-diagonal analysis entirely.

REMAINING for C1: Lemma E, `|∫_T^{2T} Z| = o(T/log²T)`.  Sharp-cutoff Euler–Maclaurin provably
cannot give it (the tail `Σ_{n≤N} n^{-1/2}` and the remainder `T²/√N` cannot both be small), so it
must be built on the corpus's exact Gaussian smooth AFE for `Z`
(`RHTower/HardyZSmoothAFEReal.lean`, `hardyZ_eq_two_tsum_smoothAFE_real`) together with the
`SmoothAFECutoffBounds` / `SmoothAFEZetaDualWeight*` decay and height-derivative estimates and the
van der Corput tests in `RHTower/VanDerCorput*.lean`.

### C3 — the two transcendence inputs are ALREADY IN THE CORPUS (2026-08-19)

Corpus search (`formal_tools.py research`) found both classical inputs the earlier plan listed as
"not in mathlib", already proved unconditionally here (`#print axioms` = the three standard ones):

- **Hermite–Lindemann**: `GaloisForLFunctions.RHTower.exp_algebraic_transcendental`
  (`RHTower/ExpAlgebraicTranscendental.lean`) — `exp β` is transcendental for every nonzero
  algebraic `β`.  Hence `log q` is transcendental for every rational `q ≥ 2`, which is exactly
  §2's `trdeg = 1`.  Also `RHTower.transcendental_algebraicClosure_of_exp_isAlgebraic` and
  `HTGeometry/HermiteLindemann.lean`.
- **Gelfond–Schneider**: `GaloisForLFunctions.RHTower.gelfondSchneider_holds` and
  `gelfondSchneiderReal_holds` (`RHTower/GelfondSchneider.lean`, full Schneider auxiliary-function
  proof in `RHTower/GelfondSchneiderProof/`) — exactly §2″'s floor input.

So C3's remaining work is (1) the repaired §2′ in general and (4) the §4 no-P-recurrence.

**Plan for the repaired §2′ (verified on paper, formalizable without `PowerSeries.log`).**
Let `g = bernoulli'PowerSeries ℚ`, `f_i = rescale L_i g`, `h = ∏_i f_i = beurlingBlock`.

1. `X · D g = g · (1 + X − g)`.  From mathlib's `bernoulli'PowerSeries_mul_exp_sub_one`
   (`g·(exp − 1) = X·exp`): differentiate, multiply by `X`, substitute `X·exp = g·(exp−1)`, and
   cancel the non-zero-divisor `exp − 1` in the domain `ℚ[[X]]`.
2. `X · D (rescale a g) = (rescale a g)·(1 + a·X − rescale a g)`, since `rescale a` is a ring
   homomorphism, `rescale a X = a·X`, and `X · D (rescale a f) = rescale a (X · D f)`
   (both have `n·aⁿ·fₙ` as `n`-th coefficient).
3. Product rule: `X · D h = h · (r + e₁·X − ∑_i f_i)`, and `∑_i f_i = ∑_k c_k p_k X^k` with
   `c_k = B⁺_k/k!` and `p_k` the `k`-th power sum, `p_0 = r`.  Hence
   **`X · D h = h · (∑_{j≥1} q_j X^j)`** with `q_1 = p_1/2` and `q_j = −c_j p_j` for `j ≥ 2`.
4. Coefficients: `k·a_k = ∑_{j=1}^{k} q_j a_{k−j}` with `a_0 = 1`, so every `q_j` is a rational
   polynomial in `a_1,…,a_j`; hence `q_j ∈ stieltjesField`.
5. `B⁺_k = B_k` for `k ≠ 1` and `B_k = 0` for odd `k ≥ 3`, so the surviving `q` are
   `q_{2m} = −B_{2m} p_{2m}/(2m)!` with `B_{2m} ≠ 0`; therefore every even power sum
   `p_{2m} ∈ stieltjesField`.
6. `p_{2m}(L) = p_m(L²)`, so Newton's identities (`MvPolynomial.mul_esymm_eq_sum`) put every
   `e_j(L₁²,…,L_r²)` in the field; each `L_i²` is then a root of a monic polynomial over it, and
   each `L_i` a root of `X² − L_i²`.  With `stieltjesField_le_logField` this gives the §2′
   transcendence-degree identity.

### C3 — §2′ CLOSED (2026-08-19)

New module `formal/GaloisForLFunctions/HTGeometry/StieltjesPowerSumRecovery.lean` (wired into the
`HTGeometry` umbrella, olean built, axioms clean).  The repaired §2′ is now an unconditional Lean
theorem.  Contents, in proof order:

- `bernoulliSeries_deriv_id` — `X·g′ = g·(1 + X − g)` for `g = bernoulli'PowerSeries A` over any
  ℚ-algebra domain, from mathlib's `bernoulli'PowerSeries_mul_exp_sub_one` by differentiating,
  multiplying by `X`, and cancelling the non-zero-divisor `exp − 1`;
- `X_mul_deriv_rescale`, `rescale_bernoulliSeries_deriv_id`, `X_mul_deriv_prod` — the rescaled and
  product forms (`X·(∏f)′ = (∏f)·(∑u)` when each `X·f_i′ = f_i·u_i`);
- `blockGen`, `coeff_blockGen`, `scaledFactor_eq_rescale`, `beurlingBlock_eq_prod`, `blockQ`,
  **`X_mul_deriv_beurlingBlock`** — the Laurent block satisfies `X·h′ = h·Q`;
- `coeff_blockQ`, `coeff_blockQ_zero`, `coeff_blockQ_of_two_le` — `Q` has zero constant term and
  `Q_m = −(B⁺_m/m!)·p_m` for `m ≥ 2`;
- `coeff_zero_beurlingBlock`, `beurlingBlock_recursion` — the coefficient recursion
  `k·a_k = ∑_{j<k} a_j q_{k−j}`;
- `qVal`, `blockCoeffVal_recursion`, `prod_mem_stieltjesField`,
  `blockCoeffVal_mem_stieltjesField`, **`qVal_mem_stieltjesField`** — every `q_m` is a rational
  polynomial in the Laurent coefficients, hence lies in the Laurent-coefficient field;
- `bernoulli_two_mul_ne_zero` (from mathlib's `hasSum_zeta_nat`: the positive sum forces
  `B_{2k} ≠ 0`), `qVal_of_two_le`, **`sum_pow_even_mem_stieltjesField`** — every *even* power sum
  `∑_i L_i^{2m}` lies in the Laurent-coefficient field;
- `negSq`, `aeval_psum_negSq`, `aeval_psum_negSq_mem`, **`aeval_esymm_negSq_mem`** — Newton's
  identities (`MvPolynomial.mul_esymm_eq_sum`) applied to the family `−L_i²`, whose power sums are
  exactly the even power sums up to sign;
- `vieta_negSq` (`Multiset.prod_X_add_C_eq_sum_esymm`), **`isAlgebraic_sq_over_stieltjesField`**,
  **`isAlgebraic_log_over_stieltjesField`** — each `L_i` is algebraic over the Laurent-coefficient
  field;
- **`trdeg_stieltjesField_eq_logField`** — §2′:
  `trdeg_ℚ {Laurent coefficients of ζ_S} = trdeg_ℚ ℚ(L₁,…,L_r)`, for every multiplier system with
  `∏ L_i ≠ 0`.

REMAINING for C3: §2 `trdeg = 1` (instantiate the corpus's Hermite–Lindemann), §2″ (instantiate
the corpus's Gelfond–Schneider), §4 (no P-recurrence).

### C3 — §2 and §2″ CLOSED (2026-08-19)

New module `formal/GaloisForLFunctions/HTGeometry/StieltjesCorankApplications.lean` (wired, olean
built, axioms clean):

- `transcendental_log_nat` — `Real.log n` is transcendental for `n ≥ 2`, from the corpus's
  Hermite–Lindemann `RHTower.exp_algebraic_transcendental`;
- **`trdeg_stieltjesField_single_eq_one`** — §2: with one multiplier whose logarithm is
  transcendental the Laurent-coefficient field has transcendence degree exactly `1`
  (`stieltjesField_single_eq` plus the corpus's
  `trdeg_intermediateFieldAdjoin_range_eq_cardinalMk_of_algebraicIndependent`);
- `coeff_two_beurlingBlock_pair`, `blockCoeffVal_two_pair`, `stieltjesVal_two_pair` — the exact
  corank-two value `γ = (L_p² + L_q²)/(12 L_p L_q) + 1/4`;
- `isAlgebraic_of_quadratic_over_algebraic` — a real root of `w² − s w + 1` with `s` algebraic is
  algebraic (via `algebraicClosure ℚ ℝ` and `IsAlgebraic.restrictScalars`);
- **`transcendental_stieltjesVal_pair`** — §2″: for two distinct primes that Laurent coefficient is
  transcendental, since otherwise `L_p/L_q` would satisfy a quadratic over the algebraic numbers,
  contradicting the corpus's `RHTower.log_ratio_transcendental` (Gelfond–Schneider).

REMAINING for C3: §4 only — `{γ_n}` is not P-recursive, i.e. `ζ` is not D-finite.

### C3 — §4 half CLOSED (2026-08-19)

Appended to `StieltjesCorankApplications.lean`:

- `DFinite` — a function satisfies a nontrivial linear differential equation with polynomial
  coefficients;
- `eval_aeval_X_zero`, **`differentiallyAlgebraic_of_dFinite`** — D-finite implies differentially
  algebraic (the linear ODE is an algebraic differential equation; nonvanishing of the transported
  multivariate polynomial is checked by evaluating at a point where one coefficient polynomial does
  not vanish);
- **`not_dFinite_riemannZeta`** — `ζ` is not D-finite, from the corpus's unconditional Hölder /
  Hilbert theorem `GaloisForLFunctions.hypertranscendental_riemannZeta`
  (`RHTower/ZetaHypertranscendental.lean`, axioms clean).

REMAINING for C3 (the only item): the classical dictionary **P-recursive ⟹ D-finite**, i.e. that a
sequence obeying a linear recurrence with polynomial coefficients has a D-finite generating
function.  With that bridge, `{γ_n}` not P-recursive follows from `not_dFinite_riemannZeta` exactly
as the card states.  The formalization route is the Weyl-algebra translation
`n ↦ θ = z·d/dz`, `shift ↦ multiplication by z^{-1}`: the recurrence becomes an inhomogeneous
operator identity `L F = R` with `R` polynomial, and differentiating `deg R + 1` times clears `R`.

## Stage-3 promotions (2026-08-19)

Moved to `docs/drafts/pipeline/3-formalized/not_new_scientific_knowledge/` after re-auditing their
capstones (`#print axioms` = `propext, Classical.choice, Quot.sound` in every case):

| Card | Capstones re-audited |
|---|---|
| C2 `hardy-cyclicity-maximal-ht-field-blindness` | `hardyCyclicityGaugeBlindness_carrier`, `outerCarrier_parabolicOrbitFreeness_denseResidual`, `gaugedOrbit_differentialAdjoin_pow_eq` |
| C4 `faithful-krein-index-escape-stratification` | `no_continuous_faithful_krein_index`, `escapeCarrier_exact_negativeSquares`, `kreinEscapeTranslateFamily_differentialAdjoin_pow_eq`, `kreinEscapeTranslateFamily_differentialIndependent_iff` |
| C5 `dyadic-squarefree-euler-fock-source-factorization` | `riemannZeta_dyadic_telescope`, `hsNormSq_fisherConnection_defect` |

Still at stage 2:

| Card | The single remaining item |
|---|---|
| C1 `hardy-critical-line-moment-anchor` | Lemma E, `\|∫_T^{2T} Z\| = o(T/log²T)`; needs the smooth-AFE split plus `θ''(t) ≍ 1/(2t)` (trigamma asymptotics), the only genuinely missing analytic input |
| C3 `f1-inversion-single-prime-stieltjes-collapse` | the dictionary P-recursive ⟹ D-finite |
| C6 `horizontal-singleton-zero-fibers` | unconditional Lean providers for the PRZZ proportions `κ ≥ 0.417293962`, `κ_* ≥ 0.407511457` |

### C3 — the P-recursive ⟹ D-finite dictionary is PROVED (2026-08-19)

New module `formal/GaloisForLFunctions/HTGeometry/PRecursiveDFinite.lean` (wired into the
`HTGeometry` umbrella, olean built, axioms clean).  It proves the classical dictionary
unconditionally, by a route that avoids the Weyl algebra entirely.

**The mechanism.**  Applying `X^m·(d/dX)^{m+j}` to a power series multiplies its `(n+j)`-th
coefficient by the falling-times-rising product

```text
(n − m + 1)⋯(n + j) = risingPoly j (n) · fallingPoly m (n)     (`coeff_shiftOp`)
```

so the coefficient patterns realizable at shift `j` are `risingPoly j` times the span of the
falling factorials — and the falling factorials span all of `ℂ[X]`
(`fallingPoly_span`, `exists_fallingPoly_finsupp`).  Multiplying a recurrence of order `d` by
`risingPoly d` therefore makes *every* coefficient polynomial realizable at once
(`risingPoly_mul_cofactor`), which is `exists_opApply_eventually_zero`:

```text
P-recursive coefficients  ⟹  ∑_{j,m} α_{j,m} X^m (d/dX)^{m+j} F  has all coefficients 0 from N on.
```

**The analytic transfer.**  `taylorSeries`, `taylorSeries_id_mul`, `taylorSeries_deriv`,
`taylorSeries_pow_mul`, `taylorSeries_iteratedDeriv`, `taylorSeries_add`,
`taylorSeries_const_mul`, `taylorSeries_finsetSum` carry the power-series identity to the entire
function; `entire_eq_zero_of_iteratedDeriv_zero` (via `analyticOrderAt_eq_top` and the identity
theorem) and `exists_poly_of_taylorSeries_eventually_zero` turn "coefficients vanish from `N` on"
into "the function is a polynomial".  Hence `exists_opFun_eq_polyEval`:

```text
∀ z,  ∑_{j,m} α_{j,m} z^m G^{(m+j)}(z) = P(z)   for a polynomial P.
```

**The conclusion.**  `differentiallyAlgebraic_of_opFun` packages that as an algebraic differential
equation; the witnessing multivariate polynomial is nonzero because the monomial
`X₀^{m₀}·X_{m₀+j₀+1}` occurs in it with coefficient `α_{j₀,m₀} ≠ 0` (`mvCoeff_term`,
`mvCoeff_aeval_X_zero`).  Capstones:

- **`differentiallyAlgebraic_of_pRecursive`** — an entire function whose Taylor coefficients at
  the origin are P-recursive is differentially algebraic;
- **`not_pRecursive_taylorSeries_of_hypertranscendental`** — contrapositive.

REMAINING for C3: instantiate this at `G(z) = z·ζ(1+z)`, whose Taylor coefficients are the
Stieltjes constants up to the factor `(−1)^n/n!`.  Two steps: (i) that `G` is entire (the simple
pole of `ζ` at `1`); (ii) that `G` is hypertranscendental — from
`hypertranscendental_riemannZeta`, using `iteratedDeriv_id_mul` (already proved in the new module)
to convert a relation for `G` into one for `ζ(1+z)` off `z = 0`, and multiplying the witnessing
polynomial by `(X₀ − 1)` to cover the pole.

### C3 COMPLETE and PROMOTED (2026-08-19)

`StieltjesNoPRecurrence.lean` closes §4:

- `zetaPoleCompletion` (`z·ζ(1+z)` completed at the origin), `differentiable_zetaPoleCompletion`
  (entire, from `riemannZeta_residue_one` and the removable-singularity criterion);
- **`hypertranscendental_zetaPoleCompletion`** — via `differentiallyAlgebraicOn_div`,
  `DifferentiallyAlgebraicOn.comp_add_const` and the corpus's
  `differentiallyAlgebraic_of_on_compl_singleton`, contradicting `hypertranscendental_riemannZeta`;
- `stieltjesGamma`, `pRecursive_coeff_of_pRecursive_stieltjes`, and
  **`not_pRecursive_stieltjesGamma`**.

The card is now at `3-formalized/not_new_scientific_knowledge/`.  Four of six promoted.

Remaining: C1 (`hardy-critical-line-moment-anchor`, Lemma E) and C6
(`horizontal-singleton-zero-fibers`, the PRZZ proportions).

### C1 — the missing analytic input for Lemma E is now PROVED (2026-08-19)

Corpus search first: `RHTower/TrigammaVertical.lean` already owns the trigamma series
(`deriv_digamma_partialSum_tendsto`) and the *qualitative* sign `deriv_digamma_vertical_im_neg`,
and `RHTower/HardyZPhaseAsymptotic.lean` owns the exact second-jet law
`deriv_gammaHardyPhaseRate t = −(ψ′(linePt t/2)).im/4` together with `θ″(t) > 0`.  What was missing
was the *quantitative* `θ″(t) ≳ 1/t` needed by the second-derivative test.

New module `formal/GaloisForLFunctions/RHTower/TrigammaVerticalLowerBound.lean` (wired into
`RHTower.lean`, olean built, axioms clean, no warnings):

- `trigammaVerticalTerm`, `trigammaVerticalTerm_nonneg`, `im_inv_sq_eq` — the explicit terms
  `2(σ+n)t/((σ+n)²+t²)²` of `−Im ψ′(σ+it)`;
- `partialSum_le_neg_im_deriv_digamma` — every partial sum is a lower bound (all terms are
  nonnegative, so the partial sums are monotone and bounded by their limit);
- **`neg_im_deriv_digamma_lower_bound`** — `−Im ψ′(σ+it) ≥ 1/(50 t)` for `0 < σ ≤ 1`, `t ≥ 2`,
  by summing the first `⌈t⌉` terms, each of which is at least `2(σ+n)/(25 t³)`;
- **`deriv_gammaHardyPhaseRate_lower_bound`** — `θ″(t) ≥ 1/(100 t)` for `t ≥ 4`.

The van der Corput second-derivative test with amplitude is already in the corpus
(`RHTower/VanDerCorput.lean`, `secondDerivTest`: `φ″ ≥ μ > 0 ⟹ ‖∫ A e^{iφ}‖ ≤ 8·budget/√μ`), as is
the first-derivative test.  What remains for Lemma E is the split of the corpus's exact Gaussian
smooth AFE for `Z` (`hardyZ_eq_two_tsum_smoothAFE_real`) into the three ranges and the summation.

### C1 — Lemma E: a much cheaper route than the card's (2026-08-19)

The card aims for the sharp `|∫_T^{2T} Z| = O(T^{3/4})`, which needs the three-range split
(first-derivative test away from the saddle, second-derivative test at it).  **The assembly does
not need the sharp exponent**: with `S = T/4` (Lemma C) and `F = O(T log⁴T)` (Lemma F), the Hölder
chain closes as soon as `|∫_T^{2T} Z| = o(T/log²T)`.  That allows applying the **second-derivative
test uniformly to every term**, with no range decomposition at all:

* `φ_n(τ) = θ(τ) − τ·log(n+1)` has `φ_n″ = θ″` for *every* `n`, and
  `θ″(τ) ≥ 1/(100τ) ≥ 1/(200T)` on `[T,2T]` (`deriv_gammaHardyPhaseRate_lower_bound`), so the
  corpus's `secondDerivTest` gives `‖∫_T^{2T} A e^{iφ_n}‖ ≤ 8·budget_n·√(200T)` for every `n`;
* direct terms have constant amplitude `V_n = smoothAFECutoff((n+1)/x)`, so `budget_n = 2‖V_n‖` and
  `∑_n (n+1)^{-1/2}‖V_n‖ = O(√x)` (bounded for `n ≲ x` by
  `exists_norm_smoothAFECutoff_sub_one_le_rpow`, and by `exists_norm_smoothAFECutoff_le_neg_rpow`
  with `A = 2` beyond);
* dual terms have `budget_n = ‖W_n(T)‖ + ‖W_n(2T)‖ + ∫_T^{2T}‖∂_τW_n‖`, with
  `∫_T^{2T}‖∂_τW_n‖ ≤ A·T/((n+1)x)` (`exists_norm_deriv_smoothAFEZetaDualWeight_le_invScale`).

Totals: direct `O(√x·√T)`, dual-derivative `O((T/x)·√T)`, dual-size `O(√(T/x)·√T)`.  Balancing
`√x = T/x` gives `x = T^{2/3}` and

```text
|∫_T^{2T} Z| = O(T^{5/6}) = o(T/log²T).      ✓
```

The one input still missing from the corpus is the **large-scale decay of the dual weight**,
`‖smoothAFEZetaDualWeight τ Y‖ ≤ K (Y/max(1,|τ|))^{-A}` for some `A > 1/2` — the positive-contour
analogue of the existing small-scale bound
`exists_norm_smoothAFEZetaDualWeight_sub_one_le_conductor` (which uses the contour `Re w = −δ`).
The machinery is present: `smoothAFEZetaDualWeightAt`, `smoothAFEZetaDualWeight_finite_contour`,
and `exists_norm_smoothAFEZetaChiShiftRatio_pos_le`; what is needed is the same argument on the
contour `Re w = +A`, where `smoothAFEMellinIntegrand Y` contributes `Y^{-A}`.

Also needed, and routine: the interchange `∫_T^{2T} ∑_n = ∑_n ∫_T^{2T}` for the two AFE series.
