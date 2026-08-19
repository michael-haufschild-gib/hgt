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
