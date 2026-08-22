# Ledger: stage-3 sweep of `09-mobius-prime-sums` (13 cards)

- **Opened:** 2026-08-22
- **Goal:** every card in
  `docs/drafts/pipeline/2-fully-proven/not_new_scientific_knowledge/09-mobius-prime-sums/`
  carries an unconditional Lean certificate of its proved content, then moves to
  `docs/drafts/pipeline/3-formalized/`.
- **Rules:** unconditional Lean only (no hypotheses, no axioms, no sorry). Search corpus before
  building. `lake env lean <file>` for iteration; `lake build <module>` only for the final audit.

## Card status

| # | Card | Lean target | State |
|---|---|---|---|
| 1 | prime-square-mobius-fourier-complementary-record-law | §2–§6 finite Fourier / CRT | **DONE — promoted to 3-formalized** |
| 2 | localized-half-density-mobius-curvature-semiprime-fibre-law | §1,(10),(11),(23) DONE; §3 fibre law + (14)–(16) OPEN | IN PROGRESS |
| 3 | shifted-euler-error-floor-mobius-tail-coupling | Thm A (3), Thm B (8)–(9) | **DONE — promoted** |
| 4 | friable-moment-ladder-finite-dim | Thm A, Thm B | TODO |
| 5 | coupled-floor-mobius-complementary-shift-incidence-law | (8), (15), (18) | **DONE — promoted** |
| 6 | mertens-corona-shift-conormal | (5),(9),(10),(13),(15),(19) | **DONE — promoted** |
| 7 | baez-duarte-critical-mobius-beta-wavelet-law | (1)–(2),(5),(8)–(10),(7c)–(7f),(14c) | TODO |
| 8 | mertens-logarithmic-corona-differential-tower | §1–§4,§6 DONE; §5 polar tower OPEN | IN PROGRESS |
| 9 | kubalalika-unweighted-near-diagonal-tail | (1)–(5) incl. van der Corput | TODO |
| 10 | square-aperture-von-mangoldt-correlation-energy | reverse implication (Schoenfeld) | TODO |
| 11 | regular-variation-weighted-steinhaus-ldp | Gärtner–Ellis LDP + endpoints | TODO |
| 12 | kubalalika-parity-weighted-near-diagonal-tail | phase stability + parity reduction + tail | TODO |
| 13 | halasz-ghs-adaptive-coarea-completion | (H1)–(H2), Lemmas A–F, (MR1) | TODO |

## Corpus assets located (do not rebuild)

- `RHTower/PrimeSquareFourierStrata.lean` — `ZMod (p^2)` additive Fourier, valuation strata
  indicators, unnormalized compression entries, deformed occupation Gram.
- `HTGeometry/PrimeCollisionConvolution.lean` — two-prime collision orientation.
- `RHTower/SuzukiCoupledErrorCriticalDerivative.lean` — `suzukiShiftedCoefficient`, first jet.
- `RHTower/WeightedEulerCoefficientSpaces.lean`, `RHTower/MertensPrimeMeanReader.lean` —
  logarithmic Marcinkiewicz layer `M_log`, vanishing-tail layer `M_0`, Mertens mean coordinate.
- `RHTower/MertensPrimeWindowWeakConvergence.lean` — Mertens first theorem in prime form.
- `RHTower/MertensThirdTheorem.lean`, `RHTower/MertensSecondPrimeRecipSum.lean`.
- `RHTower/Sieve/SquarefreeDyadicDensity.lean` — squarefree dyadic density.
- `HTGeometry/SteinhausLaplaceProduct.lean` — Haar circle Laplace product.
- `RHTower/SqrtCarrierCertificate.lean` — `ζ(2z)⁻¹` square-dilated Möbius carrier.
- `RHTower/BaezDuarte*.lean` — BD distance / Gram / least squares (dilation form).

## Log

- 2026-08-22 — ledger opened; all 13 cards read; corpus audit started.

## Card 1 progress (2026-08-22)

Landed Lean modules (both wired into `GaloisForLFunctions.RHTower`, both `lake build`-green,
axiom audit = `[propext, Classical.choice, Quot.sound]` only):

- `RHTower/PrimeSquareMobiusComplementaryRecord.lean` — §2–§5 of the card:
  `countInner_strataVec` (strata Gram), `primeSquareFourier_unitVec` /
  `primeSquareFourier_valOneVec'` (eq. 7), `compression_*` (eq. 8),
  `primeSquareFourier_fourierFixedVec` / `countInner_recordVec_fourier_recordVec` /
  `countInner_recordLeak_self` (eq. 9–11), `primeSquareOccupationVec_eq_recordVec` (14),
  `primeSquareSourceInvolution_occupationVec` (16),
  `primeSquareSourceInvolution_fourierFixedVec` / `_recordVec` (17),
  `primeSquareMobiusVec_eq` + `primeRecordSigma_sq_add_tau_sq` (18),
  `primeRecordSigma_eq_sech` / `primeRecordTau_eq_tanh` (19–21),
  `primeSquareMobiusDFT_strata` + case values (22–24), `countInner_mobiusDFT_self` (25),
  `primeSquare_zeroFrequency_factorization` (26), `primeSquare_zeroFrequency_share` (38),
  `countInner_deformedMobius` / `countInner_deformedLine` (27–29),
  capstone `primeSquare_complementary_record_law` (stated for `p.Prime`).
- `RHTower/PrimeSquareMobiusSectorFracture.lean` — §6 profinite half:
  `eulerClockNat_eq_moebius` (4), `sum_primeSquareLocalMobius(_sq)` (39),
  `eulerClockCRT` (31), `sum_eulerClockProd_mul` / `eulerClockProd_gram` /
  `eulerClockProd_gram_univ` (40), `eulerClockProd_normSq` (32),
  `eulerClockProd_dist_sq` + `tendsto_sectorFracture` + `tendsto_sectorFracture_iterated` (41),
  `tendsto_squarefreeSafeProduct` (42), `tendsto_primeRecordProduct_zero`.

Card 1 is COMPLETE (3 modules, promoted 2026-08-22).  The density half used this route:

1. `μ(n)·m_P(n) = μ(a)²·μ(b)` for `n = a·b`, `a` the `P`-part; so
   `∑_{n≤X} μ(n) m_P(n) = ∑_{a ∣ R} N_R(X/a)` with `N_R(Y) = ∑_{b≤Y,(b,R)=1} μ(b)`.
2. `N_R(Y) = ∑_{a R-smooth} M(Y/a)`; `∑_{a R-smooth} 1/a = ∏_{p∈P}(1-1/p)^{-1} < ∞`.
3. `M(Y) = o(Y)` is **already owned**: `RHTower.Sieve.tendsto_abs_mertensM_div`
   (and the sup form `RHTower.Sieve.tendsto_mertensSup_div`), in
   `RHTower/Sieve/MoebiusMaximalWindow.lean`.
4. `∑_{n≤X} μ(n)²/X → 6/π²`: see `RHTower/Sieve/SquarefreeWindowCount.lean`,
   `RHTower/Sieve/SquarefreeDyadicDensity.lean` (`squarefreeDensity`).
5. `∑_{n≤X} m_P(n)²/X → ∏(1-p^{-2})`: mean of a periodic function.

## Key corpus assets found (reusable across the folder)

- **`RHTower.Sieve.tendsto_abs_mertensM_div` — `M(N) = o(N)` (PNT in Mertens form).**
- `RHTower.Sieve.tendsto_mertensSup_div` — the sup version.
- `RHTower.tendsto_chebyshevPsiReal_div` — `ψ(x)/x → 1`.
- `RHTower.tendsto_mertensPrimeProduct_mul_log` — Mertens' third theorem.
- `RHTower.Sieve.tendsto_window_squarefree_density`, `squarefreeDensity`.
- `RHTower.Sieve.SmoothRough` — `smoothPart_mul_roughPart` etc.
- `GaloisForLFunctions/PNTPlus/` — vendored PNT (`WeakPNT'`, `chebyshev_asymptotic`,
  `MediumPNT`, Wiener–Ikehara), `PNTPlus/BrunTitchmarsh.lean`.
- mathlib: `EulerProduct.eulerProduct_completely_multiplicative`, `hasSum_zeta_two`,
  `ZMod.prodEquivPi`, `Finset.prod_univ_sum`.

- `RHTower/PrimeSquareMobiusDensityFracture.lean` (card 1, §6 density half) — landed.
  Reusable bricks it leaves behind: `localMobiusNat`/`eulerClockNat` (the finite Euler clock as an
  arithmetic function), `sum_Icc_dvd_reindex` (reindexing a sum over the multiples of `d`),
  and `tendsto_mobiusClockDvdSum` — a **one-prime geometric transfer**: if `A(X)/X → 0` and
  `|A(X)| ≤ X` and `B(X) = -A(X/p) + B(X/p)` with `|B(X)| ≤ X`, then `B(X)/X → 0`.

## Landed modules (running list)

0. STATUS 2026-08-22: cards 1, 3, 5, 6 promoted to `3-formalized`; 9 remain.

1. `RHTower/PrimeSquareMobiusComplementaryRecord.lean` (card 1 §2–§5)
2. `RHTower/PrimeSquareMobiusSectorFracture.lean` (card 1 §6 profinite)
3. `RHTower/PrimeSquareMobiusDensityFracture.lean` (card 1 §6 density)
4. `RHTower/ShiftedEulerFloorMobiusTailCoupling.lean` (card 3)
5. `RHTower/CoupledFloorMobiusShiftIncidence.lean` (card 5)
6. `RHTower/MertensCoronaShiftConormal.lean` (card 6 core)
7. `RHTower/MertensCoronaTimeOneResidue.lean` (card 6 residue + transgression)

Additional reusable bricks:
- `RHTower.primeUnitTranslation` + `memCriticalSummableLayer_primeUnitTranslation` — **every
  positive Euler translation of a logarithmic Marcinkiewicz field is absolutely summable**
  (dyadic-block proof; generalizes verbatim to the graded spaces of card 8).
- `RHTower.timeOneCorrection`, `abelShapeFactor`, `abelWeighted`, `abs_timeOne_sub_abel_le`.
- `RHTower.coronaPolarGermJet` + `hasDerivAt_coronaPolarGermJet`.
- corpus: `RHTower.GammaMeixnerAbelCoronaProbe` (the whole Abel probe),
  `HTGeometry.gammaClockCurvature_eq_outerProduct`.

8. `RHTower/MertensGradedCoronaTower.lean` (card 8 §1–§4, §6)

**Card 8's single open Lean item** (deliberately sequenced, not abandoned): the graded prime-zeta
Abel pole `lim_{s↓0} s^{k+1} ∑_p (log p)^{k+1} p^{-1-s} = k!`.  Needs (i) the general-`k` Abel
representation (generalize `RHTower.primeLogZeta_eq_abel_integral`), (ii)
`∫_1^∞ t^{-s-1}(log t)^m dt = m!/s^{m+1}` (generalize `RHTower.integral_rpow_mul_log_Ioi_one`),
(iii) uniform boundedness of the higher-Mertens error.  `k = 0` is already closed
(`RHTower.tendsto_timeOnePrimeLaplace`).

9. `RHTower/LocalizedHalfDensityCurvature.lean` (card 2 §1, eq. (10), (11), (22)–(23))

Card 2 landed so far: `logDerivation` + Leibniz rule, `logDerivation_moebius_mul_zeta` (2),
`logDerivation_sq_moebius_mul_zeta` (2), `sum_divisors_moebius_twisted_sq` (3),
`twisted_second_jet_eq_selfConv_iff` (4), `sum_divisors_moebius_half(_sq)` (7),
`fibre_second_jet` (10), `triangularKernel` / `centredTriangularKernel` (11),
`centredTriangularKernel_pos_iff` / `_eq_zero_iff` / `_neg_iff` (23).

Card 2 remaining: §2's endpoint deletion `(14)`–`(15)` and the semiprime counterterm `(16)`
(needs the complex germ `e_{iτ}` and the inverse law `(6)`), and §3's product-fibre
classification `(17)`–`(21)` (use `HTGeometry.PrimeCollisionConvolution`:
`primePower_pair_orientation`, `equalPrimePower_pair_unordered`,
`arithmeticOfPrimePowerColumn_mul_apply_distinct_*`).

Next after card 2: card 7 `baez-duarte-critical-mobius-beta-wavelet-law` (check
`RHTower.MobiusCenteredMertensLimit` for the critical boundary `L²` input), then card 4, then the
big analytic cards (9, 10, 11, 12, 13) and card 8 §5.

More reusable bricks now available:
- `RHTower.suzukiCoupledErrorReal_eq` — Theorem A at a real argument.
- `RHTower.rightShift` / `lowerIncidence` / `upperIncidence` — half-line shift/projection calculus.
- `RHTower.measurable_powerSumRemainder`, `RHTower.abs_floorIncidenceVector_le`.
- `RHTower.sum_Icc_rpow_eq_remainder` — power sum ↔ `powerSumRemainder`.

## Card 2 — localized-half-density-mobius-curvature-semiprime-fibre-law — PROMOTED (stage 3)

Landed modules (both `lake build`-green, wired into `RHTower.lean`, axiom-clean):

- `RHTower/LocalizedHalfDensityCurvature.lean` (1068 lines) — `(1)`–`(4)` jets, `(9)` pair sum,
  `(10)` coefficient curvature `fibre_second_jet`, `(11)` + `(23)` kernel chambers,
  `(17)`–`(20)` complete twisted product-fibre classification (three-prime vanishing, two-prime
  cosine mode, prime-power Chebyshev `U_{k-2}`), `(22)` two-prime kernel value, `(24)` injectivity.
- `RHTower/LocalizedHalfDensityGerm.lean` (779 lines) — `(5)` Euler product + link to
  `suzukiCoeffAF`, `(6)` inverse law, `(7)` genuine boundary jets, `expModeSum` analytic layer,
  `(8)` fibre, `(10)` as a genuine second derivative, `(12)`–`(15)` endpoint deletion, `(16)`
  semiprime counterterm, `(21)` spectral reading.

Reusable assets this card left behind:

- `expModeSum` / `hasDerivAt_expModeSum` / `deriv_expModeSum` / `iteratedDeriv_two_expModeSum` /
  `expModeSum_add_const_mul` / `iteratedDeriv_two_expModeSum_add_const_mul` — the finite
  exponential mode jet: any finite `∑ a_j e^{i τ c_j}` has second derivative `-∑ a_j c_j²` at 0.
- `primePow_pair_of_semiprimePower`, `sum_antidiagonal_two_prime` — the two-prime orientation
  core of the divisor antidiagonal.
- `symmetricExpSum` + `symmetricExpSum_recurrence` + `symmetricExpSum_eq_chebyshevU` — the
  Chebyshev-`U` three-term recurrence for symmetric exponential sums.
- `sum_divisors_moebius_cpow` — complex Euler product `∑_{d∣n} μ(d) d^{-σ} = ∏_{p∣n}(1-p^{-σ})`.
- `natCast_cpow_eq_cexp`, `dirichletShift_zero`.

Remaining cards in this folder: 8 (`mertens-logarithmic-corona-differential-tower` §5, and the
seven not yet opened).

## Card 8 — mertens-logarithmic-corona-differential-tower — PROMOTED (stage 3)

§5 closed.  New modules (both wired into `RHTower.lean`, `lake build`-green, axiom-clean):

- `RHTower/PrimeLogPowZetaAbelPole.lean` (579 lines) — the elementary log-power integral
  `∫_1^∞ t^{-δ-1}(log t)^m dt = m!/δ^{m+1}`, the graded Abel decomposition, and the capstone
  `tendsto_gradedPrimeLogZeta : δ^{k+1} ∑_p (log p)^{k+1} p^{-1-δ} → k!`.
- `RHTower/MertensGradedCoronaPolarTower.lean` — `(23)`–`(29)`: the time-one polar tower
  `s^{k+1} F_k(s) → √2 k!`, the clock/derivative and translation/shift intertwiners, the
  reflection parity.

Also generalized in place (no duplication): `RHTower/PrimeLogZetaAbelPole.lean` now carries
`isBigO_logAffine_pow_rpow`, `tendsto_rpow_neg_mul_logAffine_pow` and
`weightedDirichlet_eq_abel_integral_pow` (partial sums may grow like any fixed power of `log`);
the old `weightedDirichlet_eq_abel_integral` is now a one-line corollary at `m = 1`.

Reusable: the log-power integral, the power-bounded Abel representation, and
`measurable_weightPartialSum_floor`.

Remaining cards in this folder: 7 (4, 7, 9, 10, 11, 12, 13).
