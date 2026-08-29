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

## Card 4 — friable-moment-ladder-finite-dim — IN PROGRESS

**Theorem B** (function-transcendence ⇏ value-transcendence): witness `log` transcendental over the
rational-function field yet `log 1 = 0 ∈ ℚ`.  Elementary.

**Theorem A** (`M_j^{(T)} ∈ V_T`).  Reduction actually to be built:

```
M_j^{(T)} = Σ_{t≤T} C(T,t) (-1)^{T-t} · (G_t(j)/j!) · (A_{T-t}(j+1)/ζ_S(j+1))
G_t(j)   := ∫_0^∞ u^j (log u)^t e^{-u} du            (= Γ^{(t)}(j+1))
A_m(σ)   := Σ_{n S-smooth} (log n)^m n^{-σ}          (= (-1)^m ζ_S^{(m)}(σ))
```

Analytic inputs:
- (N1) change of variables `u = n x` in `∫_0^∞ x^j (log x)^T e^{-nx} dx`.
- (N2) binomial expansion of `(log u - log n)^T` under the integral.
- (N3) `∫ Σ_n = Σ_n ∫` over the S-smooth numbers (`MeasureTheory.integral_tsum`).
- (N4) **the bridge** `∫_0^∞ (log u)^t e^{-u} du = iteratedDeriv t Γ 1`, plus the IBP recursion
  `G_t(j) = j G_t(j-1) + t G_{t-1}(j-1)` (j ≥ 1) reducing every `G_t(j)` to it.
- (N5) `A_m(j+1)/ζ_S(j+1) ∈ ℚ-span{(log p)-monomials of degree ≤ m}` from
  `log ζ_S(s) = -Σ_{p∈S} log(1-p^{-s})` and `p^{-(j+1)}/(1-p^{-(j+1)}) = 1/(p^{j+1}-1) ∈ ℚ`.

Corpus assets found (do not rebuild):
- `HTGeometry.GammaProjectiveBoundary.gammaBell` + `gamma_iteratedDeriv_eq_gamma_mul_eval_gammaBell`
  — canonical Bell recursion `Γ^{(n)} = Γ · eval (ψ-jet) (gammaBell n)`; also
  `HTGeometry.GammaDifferentialFE.exists_gamma_bell` / `gamma_iteratedDeriv_div_eq_bell`.
  Still needed: `gammaBell n` has ℤ/ℚ coefficients and is weighted-homogeneous of weighted degree
  `n` for `wt(X j) = j+1`.
- Mathlib `Complex.digamma = logDeriv Gamma`, `Complex.digamma_one = -γ`,
  `Complex.digamma_apply_add_one`, `Complex.hasDerivAt_GammaIntegral`,
  `mellin_hasDerivAt_of_isBigO_rpow`.
- `Hurwitz.PolygammaHurwitzValue.polygamma_one_eq_riemannZeta`:
  `ψ^{(m+1)}(1) = (-1)^{m+2}(m+1)! ζ(m+2)`.
- `HTGeometry.SmoothNumbers` (S-smooth numbers), `RHTower.FriableAuxiliary` (a *different* card's
  finite friable Dirichlet derivative anchor, same log-monomial shape).

### Card 4 progress

LANDED: `formal/GaloisForLFunctions/RHTower/FriableMomentGammaDerivative.lean` (wired into
`RHTower.lean`, `lake build`-green) — the (N4) bridge:

- `gammaLogIntegrandReal` / `gammaLogIntegrand` `(log x)^t e^{-x}`, its continuity, local
  integrability, and both decay bounds (`isBigO_gammaLogIntegrand_atTop` for every exponent,
  `isBigO_gammaLogIntegrand_nhdsGT_zero` for every positive exponent, by the halving induction
  through Mathlib's `isBigO_rpow_zero_log_smul`).
- `hasDerivAt_mellin_gammaLogIntegrand` — differentiating the Mellin transform raises the log
  weight by one.
- `iteratedDeriv_Gamma_eq_mellin` / `iteratedDeriv_Gamma_eq_integral` — `Γ^{(t)}(s)` is the
  log-weighted Gamma integral on `0 < Re s`.
- `gammaLogMoment t j := ∫_0^∞ x^j (log x)^t e^{-x} dx` and
  `iteratedDeriv_Gamma_natSucc : Γ^{(t)}(j+1) = ↑(gammaLogMoment t j)`.

NEXT for card 4:
1. `gammaBell n` (in `HTGeometry/GammaProjectiveBoundary.lean`) has ℚ coefficients and is
   weighted-homogeneous of weighted degree `n` for `wt (X i) = i+1`
   (`MvPolynomial.IsWeightedHomogeneous`; the recursion is `X 0 * rename castSucc B_n +
   Σ_j rename castSucc (pderiv j B_n) * X j.succ`).
2. The ψ-jet at `j+1`: combine `HTGeometry.GammaDifferentialFE.polygamma_telescope` (with `s = 1`)
   with Mathlib `Complex.digamma_one = -γ` and
   `Hurwitz.PolygammaHurwitzValue.polygamma_one_eq_riemannZeta`, giving
   `ψ(j+1) = H_j - γ` and `ψ^{(m)}(j+1) = (-1)^{m+1} m! (ζ(m+1) - H_j^{(m+1)})`.
3. (N5) the S-part: `A_m(j+1)/ζ_S(j+1) ∈ ℚ-span{(log p)-monomials of degree ≤ m}`.
4. (N1)-(N3) and the assembly.

LANDED (card 4, batch 2), both wired and `lake build`-green:
- `RHTower/FriableMomentPolygammaJet.lean` — `harmonicQ`, `digamma_natSucc : ψ(j+1) = H_j - γ`,
  `iteratedDeriv_digamma_natSucc_succ : ψ^{(m+1)}(j+1) = (-1)^{m+2}(m+1)!(ζ(m+2) - H_j^{(m+2)})`,
  from `GammaDifferentialFE.polygamma_telescope` + `Complex.digamma_one` +
  `Hurwitz.polygamma_one_eq_riemannZeta`.
- `RHTower/PeriodWeightFiltration.lean` — `periodGen` / `periodProducts` / `periodFilt S T`
  (`ℚ`-span of products of weighted generators of total weight ≤ T), monotone, closed under
  multiplication with weights adding (`periodFilt_mul`), contains `1`, every rational, `γ` (weight
  1), `ζ(k)` (weight k), `log p` (weight 1), and `Module.Finite ℚ (periodFilt S T)`.

Corpus assets confirmed for the Bell step (do not rebuild):
- `HTGeometry.GammaBellSubstitution.bellCore` — the universal Bell recursion (same definition as
  `gammaBell`).
- `HTGeometry.GammaPoleReciprocalBellGrading.bellJetWeight` (`wt i = i+1`) and
  `bellCore_isWeightedHomogeneous : (bellCore k).IsWeightedHomogeneous (bellJetWeight k) k`.
- `HTGeometry.LogDerivBellTransfer.iteratedDeriv_eq_bellCore_generic` — the Bell identity for ANY
  analytic nonvanishing `f` (serves both `Γ` and `ζ_S`).
- `HTGeometry.MvPolynomialHomogeneousDehomogenization.rename_isWeightedHomogeneous`.
Still to build: `bellCore` has ℚ coefficients; `eval`-in-filtration lemma; the two applications.

LANDED (card 4, batch 3): `RHTower/FriableMomentBellEvaluation.lean` (wired, green)
- `bellCoreQ` + `map_bellCoreQ : map (algebraMap ℚ ℂ) (bellCoreQ k) = bellCore k` — the universal
  Bell polynomials have rational coefficients.
- `isWeightedHomogeneous_bellCoreQ` — transported from the corpus's
  `bellCore_isWeightedHomogeneous` through injectivity of `algebraMap ℚ ℂ`.
- `pow_mem_periodFilt`, `prod_pow_mem_periodFilt`, `weight_eq_sum`, `eval_mem_periodFilt` — a
  weight-homogeneous rational polynomial evaluated on a jet whose `i`-th coordinate lies in
  `periodFilt S (i+1)` lands in `periodFilt S d`.
- `iteratedDeriv_digamma_mem_periodFilt : ψ^{(i)}(j+1) ∈ periodFilt S (i+1)`.
- **`gammaJet_mem_periodFilt : Γ^{(t)}(j+1)/j! ∈ periodFilt S t`** — the Γ half of Theorem A.

REMAINING for card 4:
- ζ_S half: with `ζ_S(s) = ∏_{p∈S}(1-p^{-s})^{-1}` (analytic, nonvanishing on `Re s > 0`),
  `u = ζ_S'/ζ_S = -Σ_{p∈S}(log p)·y_p`, `y_p(s) = 1/(p^s-1)` satisfies the ODE
  `y_p' = -(log p)(y_p + y_p²)`, so `y_p^{(i)} = (log p)^i · aeval (y_p) (Q i)` for the ℤ-polynomial
  recursion `Q 0 = X`, `Q (i+1) = -(X + X²)·(Q i)'`; at `s = j+1`, `y_p(j+1) = 1/(p^{j+1}-1) ∈ ℚ`,
  hence `u^{(i)}(j+1) ∈ periodFilt S (i+1)` and (via `iteratedDeriv_eq_bellCore_generic` +
  `eval_mem_periodFilt`) `ζ_S^{(m)}(j+1)/ζ_S(j+1) ∈ periodFilt S m`.
- The Dirichlet-series bridge `Σ_{n S-smooth}(log n)^m n^{-σ} = (-1)^m ζ_S^{(m)}(σ)` (termwise
  differentiation, same `hasDerivAt_tsum_of_isPreconnected` pattern as
  `RHTower.MertensGradedCoronaPolarTower`) and the Euler product for a general finite prime set.
- (N1)–(N3) and the final assembly `M_j^{(T)} ∈ periodFilt S T`.
- Theorem B.

LANDED (card 4, batch 4): `RHTower/FriableMomentEulerFlux.lean` (wired, green)
- `eulerJetPolyQ` + `map_eulerJetPolyQ` — the corpus's Eulerian-type jet polynomials
  (`RHTower.EulerSourceJetOpenness.eulerJetPoly`) have rational coefficients.
- `cpow_neg_natSucc`, `eval_map_ratCast_poly`, `localFluxJet_one_natSucc` — the local Euler flux
  jet at a positive integer is `(log p)^{i+1}` times an explicit rational.
- `localFluxJet_one_natSucc_mem_periodFilt : localFluxJet p 1 i (j+1) ∈ periodFilt S (i+1)`.

NOTE: an earlier draft module `FriableMomentEulerFactorJet.lean` was DELETED — the corpus already
owns the local-flux jet in closed form (`EulerSourceJetOpenness.iteratedDeriv_localFluxJet`,
`iteratedDeriv_eulerFlux`, `eulerFlux_eq_neg_logDeriv`), so only the rationality layer was needed.

NEXT: `ζ_S = eulerProductL p 1`, `-ζ_S'/ζ_S = eulerFlux p 1` (corpus), then
`ζ_S^{(m)}(j+1)/ζ_S(j+1) ∈ periodFilt S m` via `iteratedDeriv_eq_bellCore_generic` +
`eval_mem_periodFilt`; then the Dirichlet-series bridge and the assembly; then Theorem B (the
exponential-polynomial argument: `Σ_i e^{-iu} Q_i(u) = 0` forces every `Q_i = 0`, whence `log` is
transcendental over the rational functions, while `log 1 = 0 ∈ ℚ`).

LANDED (card 4, batch 5), both wired and green:
- `RHTower/FriableMomentZetaJet.lean` — `eulerProductL_ne_zero`, `analyticAt_eulerProductL`,
  `iteratedDeriv_logDeriv_eulerProductL` (the log-derivative jet of the finite Euler product is
  minus the corpus Euler-flux jet), and
  **`friableZetaJet_mem_periodFilt : ζ_S^{(m)}(j+1)/ζ_S(j+1) ∈ periodFilt S m`**.
- `RHTower/MellinIteratedDerivative.lean` — `MellinRapid` (rapid decay at both ends),
  `logWeighted`, `MellinRapid.logWeighted`, and
  **`iteratedDeriv_mellin : iteratedDeriv t (mellin f) s = mellin (logWeighted f t) s`** for
  `0 < Re s` — the reusable form of the Γ bridge.

ASSEMBLY PLAN (simplified — no Leibniz needed): put `F s = Γ s * eulerProductL p 1 s`.  Then
`logDeriv F = digamma + logDeriv ζ_S`, so every jet `iteratedDeriv i (logDeriv F) (j+1)` is a sum
of two members of `periodFilt S (i+1)`; the Bell transfer gives
`F^{(T)}(j+1)/F(j+1) ∈ periodFilt S T`; and `F(j+1) = j! · ζ_S(j+1)`.  It remains to identify
`F^{(T)}(j+1)` with the card's integral: `mellin (friableDensity) = Γ · ζ_S` on `0 < Re s`
(Tonelli/`integral_tsum` termwise, using `∫_0^∞ x^{s-1}e^{-nx}dx = Γ(s)n^{-s}`), plus
`MellinRapid friableDensity` (at 0 use `e^{-u} ≤ C_σ u^{-σ}` so
`friableDensity x ≤ C_σ ζ_S(σ) x^{-σ}` for every `σ > 0`; at ∞ use `≤ 1/(e^x-1)`), and then
`iteratedDeriv_mellin`.  The one remaining combinatorial input is the Euler product for a general
finite prime set `S`: `∑'_{n S-smooth} n^{-s} = ∏_{p∈S}(1-p^{-s})^{-1}`.

LANDED (card 4, batch 6): `RHTower/FriableMomentDensity.lean` (wired, green)
- `smoothNat p ν = ∏ i (p i)^(ν i)`, `smoothNat_rpow_eq_nomeMonomial`,
  `summable_smoothNat_rpow` (from the corpus's
  `HTGeometry.summable_nomeMonomial_pow_iff`).
- `exp_neg_le_rpow_neg` — every negative real power dominates `e^{-u}` (reusing the corpus's
  `RHTower.pow_le_factorial_mul_exp` from `ThetaHalfPlaneBound.lean`; an earlier duplicate of that
  lemma was removed).
- `friableDensity p x = Σ'_ν e^{-n_ν x}`, `friableDirichlet`, `summable_friableTerm`,
  **`norm_friableDensity_le : ‖friableDensity p x‖ ≤ C · ζ_S(σ) · x^{-σ}` for every `σ > 0`**,
  `continuousOn_friableDensity`, `continuousOn_friableDensity_Ioi_zero`,
  `locallyIntegrableOn_friableDensity`.

NEXT (card 4, final steps):
1. `MellinRapid (friableDensity p)` — both `isBigO`s follow from `norm_friableDensity_le`
   (`top a`: use `σ = max a 1` and `x ≥ 1`; `bot b`: use `σ = b`).
2. `mellin (friableDensity p) s = Γ(s) · eulerProductL p 1 s` on `0 < Re s`, by
   `MeasureTheory.integral_tsum_of_summable_integral_norm` + `mellin_comp_mul_left` +
   `RHTower.tsum_nomeMonomial_eq_fintype_eulerProduct` (with `u i = (p i)^{-s}`).
3. Assembly: `F = Γ · eulerProductL p 1`; `logDeriv F = digamma + logDeriv ζ_S`, so every jet is in
   `periodFilt S (i+1)`; the Bell transfer gives `F^{(T)}(j+1)/F(j+1) ∈ periodFilt S T`; combine
   with `iteratedDeriv_mellin` and `F(j+1) = j!·ζ_S(j+1)` to conclude
   `M_j^{(T)} ∈ periodFilt S T`.
4. Theorem B.

## Card 4 — friable-moment-ladder-finite-dim — PROMOTED (stage 3)

Final batch: `RHTower/FriableMomentMellin.lean` (`mellinRapid_friableDensity`,
`mellinRapid_expScaled`, `mellin_expScaled`, `integral_norm_mellinExpScaled`,
**`mellin_friableDensity : mellin (friableDensity p) s = Γ(s)·ζ_S(s)`**),
`RHTower/FriableMomentLadder.lean` (`friableMellinDatum`, `logDeriv_friableMellinDatum`,
`iteratedDeriv_logDeriv_friableMellinDatum_mem`, `friableJet_mem_periodFilt`,
`friableLogMomentIntegral_eq_jet`, **`friableLogMoment_mem_periodFilt`** = Theorem A), and
`RHTower/FriableMomentValueLift.lean` (Theorem B).

Reusable assets this card left behind:
- `periodFilt` — a weighted ℚ-filtration of ℂ by period monomials, multiplicative in the weight
  and finite-dimensional in each layer.
- `MellinRapid` + `iteratedDeriv_mellin` — iterated derivatives of any rapidly-decaying Mellin
  transform are the log-weighted transforms.
- `eval_mem_periodFilt` — weighted evaluation of a rational weight-homogeneous polynomial.
- `map_bellCoreQ` / `isWeightedHomogeneous_bellCoreQ` — rationality of the universal Bell
  polynomials; `map_eulerJetPolyQ` — rationality of the Eulerian-type jet polynomials.
- `smoothNat`, `friableDensity`, `summable_smoothNat_rpow`, `exp_neg_le_rpow_neg`.

Remaining cards in this folder: 6 (7, 9, 10, 11, 12, 13).

## Card 9 — kubalalika-unweighted-near-diagonal-tail — STARTED

Theorem to formalize: `E_0(T) = O(T^{7/8} + T^{3/8} log T) = o(T)` where

```
E_0(T) = Σ_{V ≤ m ≤ T(1+ε)} Σ_{R ≤ r ≤ mε} exp(i T log(1+r/m))/r ,
ε = T^{-1/4},  V = T/((1+ε)(log T)^2),  R = T^{1/4}.
```

**KEY FINDING — the hard analytic tool is already owned.**
`RHTower.Sieve.SecondDerivativeTest.second_derivative_test (g g' g'' x₀ N) (hN : 1 ≤ N)
 (hlam0 : 0 < lam) (hlam1 : lam ≤ 1) (hd1) (hd2) (hlo : lam ≤ g'') (hhi : g'' ≤ hgrow*lam) :
 ‖Σ_{n<N} e(g (x₀+n))‖ ≤ (2 N hgrow lam + 3)(3/√lam + 1)`
is exactly van der Corput's second-derivative test for a *general* phase, and
`RHTower.Sieve.KthDerivativeTest.kth_derivative_test` is its order-`k` extension.  Also owned:
`RHTower.Sieve.KuzminLandauInterval.kuzminLandau_interval` (first-derivative test).
Do NOT rebuild any of these.

Remaining work for card 9:
1. `F_r(u) = (T/2π) log(1 + r/u)`; derivative chain and
   `F_r''(u) = T r (2u+r) / (2π u²(u+r)²) > 0`, with the two-sided dyadic bound
   `F_r'' ≍ T r / M³` on `M ≤ u ≤ 2M` when `r ≤ ε m`, `ε < 1/2`.
2. Apply `second_derivative_test` per dyadic block, then sum the blocks:
   `|Σ_m e(F_r(m))| ≪ √(T r / V) + T/√r`.
3. Sum over `r`: `Σ_r (1/r)(√r log T + T/√r) ≪ T^{3/8} log T + T^{7/8}`.

## Other remaining cards — gap survey
- **10 square-aperture**: forward implication + the exact identity are ALREADY formalized
  (`RHTower.CCMSharpPrimeWindowSquareCorrelationEnergy`:
  `squareWindowCorrelationEnergy`, `..._eq_centeredDeviation_square_sum`,
  `riemannHypothesis_of_squarePrimeWindowCorrelationEnergySubpower`).  The open gate is the
  REVERSE implication, which needs `RH ⟹ ψ(x) − x ≪ √x (log x)²` (von Koch).  Not in the corpus;
  this is the one genuinely large classical input left in the folder.
- **7 baez-duarte**, **11 regular-variation-steinhaus-ldp**, **12 kubalalika-parity**,
  **13 halasz-ghs**: not yet surveyed in this session.

LANDED (card 9, batch 1): `RHTower/NearDiagonalPhaseCurvature.lean` (wired, green)
- `nearDiagonalPhase T r u = (T/2π) log(1 + r/u)`, `nearDiagonalPhaseD1`, `nearDiagonalPhaseD2`,
  with `hasDerivAt_nearDiagonalPhase` and `hasDerivAt_nearDiagonalPhaseD1` — equation (1) of the
  card, differentiated in the actual summation variable.
- `nearDiagonalLambda T r M = T r/(36 π M³)`, with the two-sided dyadic pinning
  `nearDiagonalLambda_le_D2` and `D2_le_nearDiagonalLambda` (ratio 90) for `r ≤ M ≤ u ≤ 2M`.
- **`norm_nearDiagonalBlock_le`** — equation (3): van der Corput's second-derivative test
  (`RHTower.Sieve.second_derivative_test`) applied on one dyadic block.

NEXT for card 9: sum the block bounds across dyadic blocks covering
`[max(V, r/ε), T(1+ε)]` to get equation (4), then sum over `r` for equation (5).

LANDED (card 9, batch 2): `RHTower/NearDiagonalBlockBound.lean` (wired, green)
- `nearDiagonalBlockBound T r M = 720 √(T r/(36 π M)) + 12 √(36 π M³/(T r))`,
  `mul_sqrt_nearDiagonalLambda`, `inv_sqrt_nearDiagonalLambda`, `block_algebra`,
  **`norm_nearDiagonalBlock_le_bound`** — the raw test output collapses (using `λ ≤ 1`, `N ≤ M`)
  to `720 M√λ + 12/√λ`, the two-term shape of equation (3).

DYADIC INDUCTION DESIGN (card 9, next batch).  Peel the *bottom* block and keep the increasing
term symbolic, otherwise the induction cannot close:

```
Target(A, B, J) :=  c₁ · √(T r/(36 π A))  +  12 · √(36 π/(T r)) · S(A, J)
S(A, J)        :=  Σ_{j < J} (A·2^j)^{3/2}   (kept symbolic!)
```
- `J = 0`: `B ≤ A`, the `Ico A B` sum is empty.
- step: `Ico A B = Ico A (min B (2A)) ∪ Ico (min B (2A)) B`; the first is one block at scale `A`
  (`norm_nearDiagonalBlock_le_bound`), the second is the IH at `2A` with `J-1`
  (uses `λ(2A) ≤ λ(A) ≤ 1`).  The increasing terms add exactly:
  `A^{3/2} + S(2A, J-1) = S(A, J)`.  The decreasing terms need `720 + c₁/√2 ≤ c₁`, i.e.
  `c₁ ≥ 720/(1 - 2^{-1/2}) ≈ 2458`; take `c₁ = 2500`.
- Separately: `S(A, J) = A^{3/2}((2√2)^J − 1)/(2√2 − 1) ≤ 1.6 · (A·2^{J-1})^{3/2}`
  (`geom_sum_eq`), which converts the symbolic sum into the card's `B^{3/2}` term.

LANDED (card 9, batch 3), both wired and green:
- `RHTower/NearDiagonalDyadicSum.lean` — `nearDiagonalSum`, `nearDiagonalTopSum`,
  `nearDiagonalTopSum_succ`, `nearDiagonalLambda_anti`, `sqrt_block_split`, `sqrt_half_scale`,
  `const_recursion` (720 + 2500/√2 ≤ 2500), and **`norm_nearDiagonalSum_le`** — the dyadic
  induction: for `B ≤ A·2^J`,
  `‖Σ_{m ∈ [A,B)} e(F_r m)‖ ≤ 2500 √(T r/(36π A)) + 12 √(36π/(T r))·Σ_{j<J} √((A2^j)³)`.
- `RHTower/NearDiagonalGeometricCollapse.lean` — `sqrt_dyadic_cube`, `two_sqrt_two_lower`,
  **`nearDiagonalTopSum_le : Σ_{j<J} √((A2^j)³) ≤ (3/5)√((A2^J)³)`**, the geometric collapse
  (ratio `2√2`) that turns the symbolic sum into the card's `B^{3/2}` term.

NEXT for card 9 (equation 5): instantiate `J` minimal with `B ≤ A·2^J` (so `A·2^J ≤ 2B`), giving
equation (4) `≪ √(T r/A) + B^{3/2}/√(T r)`; then define `E₀(T)` with `ε = T^{-1/4}`,
`V = T/((1+ε)(log T)²)`, `R = T^{1/4}`, and sum over `r` using
`Σ_{r ≤ T^{3/4}} r^{-1/2} ≪ T^{3/8}` and `Σ_{r ≥ T^{1/4}} r^{-3/2} ≪ T^{-1/8}`.

LANDED (card 9, batch 4), both wired and green:
- `RHTower/NearDiagonalInnerSum.lean` — `exists_dyadic_cover_nat` and **equation (4)**
  `norm_nearDiagonalSum_le_final`: for `1 ≤ A`, `r ≤ A`, `λ(A) ≤ 1`,
  `‖Σ_{m∈[A,B)} e(F_r m)‖ ≤ 2500√(T r/(36π A)) + 22 √(36π/(T r))·√(B³)`
  (minimal `J` with `B ≤ A2^J`, so `A2^J ≤ 2B`).
- `RHTower/SqrtTelescopeSums.lean` — `sum_inv_sqrt_le : Σ_{r≤N} 1/√r ≤ 2√N` and
  `sum_inv_sqrt_cube_le : Σ_{R ≤ r ≤ N} 1/√(r³) ≤ 2/√(R−1)`, both by telescoping.

NEXT (card 9, last step — equation (5)): define `E₀(T)` as the double sum over
`{(m,r) : ⌈V⌉ ≤ m ≤ ⌊T(1+ε)⌋, ⌈R⌉ ≤ r ≤ ⌊mε⌋}`, swap the order with `Finset.sum_comm'`
(the constraint `r ≤ mε ⟺ m ≥ ⌈r/ε⌉`), apply equation (4) for each `r`, and finish with the two
telescoping sums.

NOTE (namespaces): this corpus has BOTH `RHTower` and `GaloisForLFunctions.RHTower` as namespaces.
A bare `grep` for a declaration name therefore over-reports collisions.  `inv_sqrt_le_telescope`
already exists as `GaloisForLFunctions.RHTower.inv_sqrt_le_telescope`
(`RHTower/CCMNonSchattenBirmanSchwinger.lean`, imports only Mathlib) and is now REUSED by
`SqrtTelescopeSums.lean` rather than duplicated.

EQUATION (5) DESIGN (card 9, final step).

Definitions (natural-number ranges, floors/ceils of the card's real endpoints):
```
ε T = T^(-1/4),  V T = T/((1+ε)(log T)^2),  R T = T^(1/4)
mLo = ⌈V⌉₊,  mHi = ⌊T(1+ε)⌋₊,  rLo = ⌈R⌉₊,  rHi m = ⌊m·ε⌋₊,  rMax = rHi mHi
kubalalikaTail T = Σ_{m ∈ Icc mLo mHi} Σ_{r ∈ Icc rLo (rHi m)} e(F_r m)/r
```

Swap: `Σ_m Σ_{r ≤ rHi m} = Σ_{r ∈ Icc rLo rMax} Σ_{m ∈ (Icc mLo mHi).filter (r ≤ rHi ·)}`.
Because `rHi` is monotone in `m`, the filtered set is an interval `Icc (mStart r) mHi`, where
`mStart r` is the least `m ≥ mLo` with `r ≤ ⌊mε⌋₊` (via `Nat.find`).  Note `mStart r ≥ r` because
`r ≤ ⌊mε⌋₊ ≤ mε ≤ m` for `ε ≤ 1` — this is what feeds `r ≤ A` in equation (4).

Then per `r`, equation (4) with `A = mStart r ≥ mLo ≥ V`, `B = mHi + 1 ≤ 2T`:
```
‖inner‖ ≤ 2500 √(T r/(36π V)) + 22 √(36π/(T r))·√((2T)³)
```
and the `1/r`-weighted `r`-sum finishes with the two telescoping bounds:
```
Σ_r r^{-1/2} ≤ 2√(rMax) ≈ 2√(εT) ≈ 2 T^{3/8},   √(T/V) ≈ log T   ⟹  ≈ T^{3/8} log T
Σ_r r^{-3/2} ≤ 2/√(rLo−1) ≈ 2 T^{-1/8},        T^{3/2}·T^{-1/2} = T  ⟹  ≈ T^{7/8}
```
Side condition to discharge: `λ(mLo) = T r/(36π mLo³) ≤ 1`, which holds for large `T` since
`r ≤ εT ≈ T^{3/4}` and `mLo ≈ T/(log T)²`.

CARD 9 CLOSED (2026-08-23) — `kubalalika-unweighted-near-diagonal-tail` promoted to stage 3.
Final module: `RHTower/NearDiagonalTailBound.lean` (swap, filter=interval, per-shift equation (4),
`shift_weight_identity`, `norm_nearDiagonalTail_le`, and the `T = u^8` specialization
`norm_kubalalikaTailSum_le_pow` / `norm_kubalalikaTailSum_le`).
Technique worth reusing: substituting `T = u^8` turns every exponent (`T^{1/4}`, `T^{3/8}`,
`T^{7/8}`, `sqrt T`) into a natural power of `u`, so the whole asymptotic assembly is polynomial
arithmetic plus `Real.sqrt_sq`; `Real.pi_gt_three` and `Real.pi_le_four` are the only pi bounds
needed (`Real.pi_gt_314`/`pi_lt_315`/`pi_gt_3141592` do NOT exist in this toolchain).
`clear_value` after `set` is essential: without it `positivity`/`nlinarith` unfold the ceil/floor
let-bodies and the declaration blows past the heartbeat limit.

REMAINING (5): baez-duarte-critical-mobius-beta-wavelet-law,
square-aperture-von-mangoldt-correlation-energy, regular-variation-weighted-steinhaus-ldp,
kubalalika-parity-weighted-near-diagonal-tail, halasz-ghs-adaptive-coarea-completion.

CARD 7 `baez-duarte-critical-mobius-beta-wavelet-law` — IN PROGRESS.

Corpus assets found (do not rebuild):
- `RHTower.LSeries_moebius_eq_inv_riemannZeta` (`RHTower/SquarefreeMoebiusNormalization.lean`).
- **`RHTower.criticalMertensVector`** (`RHTower/MobiusWeightedMertensVector.lean:191`) is exactly the
  card's `m_0`: `1_{t>0}(t) · Σ_{n ≤ e^t} μ(n)/n`, and
  **`RHTower.memLp_criticalMertensVector : MemLp criticalMertensVector 2 volume`**
  (`RHTower/MobiusCenteredMertensLimit.lean:295`) is the unconditional critical-boundary `L²`
  theorem the card's gate was waiting on.  The gate "formalize after the critical Möbius
  boundary/Stieltjes API enters Lean" is therefore UNBLOCKED.
- Nyman–Beurling: `RHTower/NymanBeurlingCriterion.lean`, `BaezDuarteDistance.lean`,
  `BaezDuarteL2Carrier.lean` own the *distance* criterion (`d_N → 0 ⟹ RH`), NOT the sequential
  coefficient criterion `(15)`.
- `Complex.betaIntegral_eval_nat_add_one_right` gives `B(u, n+1) = n!/∏_{j≤n}(u+j)` for `0 < u.re`.

LANDED (card 7), all wired and green:
- `RHTower/BaezDuarteMobiusSeries.lean` — **(1)–(2)**: `bdCoeff k = Σ_{j≤k}(-1)^j C(k,j)/ζ(2j+2)`
  and `hasSum_bdMobiusTerm : HasSum (fun n => μ(n) n^{-2}(1-n^{-2})^k) (bdCoeff k)`.
- `RHTower/BaezDuarteBetaWavelet.lean` — **(3)–(4), (7)**: `bdWavelet k t = e^{-t}(1-e^{-2t})^k`,
  `bdKernel k = -(w_{k+1})'` (INDEX SHIFT: `bdKernel k` is the card's `K_{k+1}`), `bdSeam k =
  ½log(2k+3)`, and the two strict sign chambers.
- `RHTower/BaezDuarteWaveletNorm.lean` — **(8)–(9)**: `y = e^{-2t}` substitution via
  `MeasureTheory.integral_image_eq_integral_abs_deriv_smul`, and
  `integral_bdKernel_weighted_sq_eq : ∫_0^∞ (e^{-αt}K)² = ½[B(α,2k) − 2(2k+3)B(α+1,2k)
  + (2k+3)²B(α+2,2k)]` with `bdBeta a n = ∫_0^1 y^a(1-y)^n` and `bdBeta_eq`.

EXACT ALGEBRA FOR (10) (verified by hand, still to formalize).  With `m = 2k+3`,
`A = (2k)!/∏_{j=0}^{2k}(α+1+j)`, the shift identities `bdBeta (α+1) (2k) = A(α+1)/(α+m-1)` and
`bdBeta (α+2) (2k) = A(α+1)(α+2)/((α+m-1)(α+m))` give the CLOSED FORM
```
‖e^{-αt}K_{k+1}‖² = (A/2) · [(α²+α+1)m² − (2α²+1)m + (α²−α)] / ((α+m-1)(α+m))
```
whose leading coefficient is exactly the card's `(α²+α+1)`.  For the order bound use
`1/A = (α+1)∏_{j=1}^{2k}(1+(α+1)/j)` and `log(1+x) ≥ x − x²/2`, giving
`A ≤ exp((α+1)²)/((α+1)(2k)^{α+1})` from `Σ_{j≤N}1/j ≥ log N` and `Σ 1/j² ≤ 2`.

NEXT for card 7 — **(5)**, and the route that avoids Stieltjes integration by parts entirely:
```
∫_0^T m_0 K_k dt = Σ_{n ≤ e^T} (μ(n)/n)(w_{k+1}(log n) − w_{k+1}(T))
                 = Σ_{n ≤ e^T} μ(n) n^{-2}(1-n^{-2})^{k+1} − w_{k+1}(T) m_0(T)
```
(finite sum, FTC on each `[log n, T]`), and `w_{k+1}(T)|m_0(T)| ≤ e^{-T}(1+T) → 0` because
`|m_0(T)| ≤ Σ_{n≤e^T} 1/n ≤ 1+T`.  Integrability of `m_0 K_k` on `(0,∞)` is Cauchy–Schwarz from
`memLp_criticalMertensVector` and `K_k ∈ L²`.  Conclusion: `∫_0^∞ m_0 K_k = bdCoeff (k+1)`.

LANDED (card 7, batch 2): `RHTower/BaezDuarteWaveletPairing.lean` — **equation (5)**,
```lean
theorem integral_criticalMertens_bdKernel (k : ℕ) :
    (∫ t in Set.Ioi (0 : ℝ), mobiusWeightedPartial 1 t * ((bdKernel k t : ℝ) : ℂ))
      = bdCoeff (k + 1)
```
proved WITHOUT any Stieltjes-integral API: FTC on `[log n, T]` per jump, a finite-sum swap, and the
boundary estimate `|m_0(T)| ≤ Σ_{n≤e^T} 1/n ≤ Σ 1/√n ≤ 2√(e^T)` (reusing `sum_inv_sqrt_le` from
`SqrtTelescopeSums.lean`, built for card 9), against `|w_{k+1}(T)| ≤ e^{-T}`.
Also landed: `bdKernelVector` and `memLp_bdKernelVector` (kernel is causal `L²`, dominated by
`(2k+4)·causalPoleVector`), and `integrableOn_criticalMertens_bdKernel` via
`MemLp.integrable_mul`.

REMAINING for card 7: (10) the closed form + gamma asymptotic, (12)–(13) Cauchy–Schwarz,
(14a)–(14c) Plancherel, (7c)–(7j) the Gibbs-channel form, and the imported endpoint (15).

LANDED (card 7, batch 3): `RHTower/BaezDuarteScaleLaw.lean`.
- `bdBeta_succ : bdBeta (a+1) n = bdBeta a n * (a+1)/(a+n+2)` (the beta shift), `bdBeta_zero`,
  `bdBeta_one`, `bdBeta_two`.
- **(10)** `integral_bdKernel_weighted_sq_closed`: the closed form with numerator
  `(α²+α+1)m² − (2α²+1)m + (α²−α)`, `m = 2k+3`, over `(α+2k+2)(α+2k+3)`.
- **(10) at α = 0**: `integral_bdKernel_sq : ∫_0^∞ K_{k+1}² = 1/(2(2k+1))` — everything cancels.
- **(11)–(12)** `norm_bdCoeff_le_weighted` (Cauchy–Schwarz, hypothesis is the CORPUS-OWNED
  `RHTower.WeightedMertensMoment α` from `MobiusWeightedMomentZeroFree.lean`, which is exactly the
  card's `(11)`), and **(13)** `norm_bdCoeff_le_unconditional`.
REUSED, not rebuilt: `RHTower.weightedMertensVector`, `weightedMertensVector_zero`,
`WeightedMertensMoment`, `weightedMertensMoment_zero` (all in `MobiusWeightedMomentZeroFree.lean`).

NEXT for card 7: `bdBeta α n ≤ Γ(α+1) n^{-(α+1)}` (route: `(1-y)^n ≤ e^{-ny}`, then
`∫_0^∞ y^α e^{-ny} dy = Γ(α+1)/n^{α+1}`) to turn (12) into the card's `O_α(k^{-(1+α)/2})`;
then (14a)–(14c) Plancherel and (7c)–(7j) the Gibbs channel.

LANDED (card 7, batch 4): `RHTower/BaezDuarteGammaMajorant.lean`.
- `bdBeta_le_gamma : bdBeta α n ≤ (1/n)^{α+1} Γ(α+1)` via `(1-y)^n ≤ e^{-ny}` and a rescaling of
  the TRUNCATED gamma integral (`integral_image_eq_integral_abs_deriv_smul` on `Ioo 0 1 → Ioo 0 n`,
  then `setIntegral_mono_set` up to `Ioi 0`).  NOTE: Mathlib has NO integrability lemma for
  `t^(a-1) e^{-rt}` on `Ioi 0` at general `r`; only `Real.GammaIntegral_convergent` at `r = 1`.
- `bdBracket_le`, `integral_bdKernel_weighted_sq_le`, and the card's **(12)**
  `norm_bdCoeff_le_scaleLaw : ∃ C ≥ 0, ∀ k ≥ 1, ‖c_{k+1}‖ ≤ C k^{-(1+α)/2}` under
  `WeightedMertensMoment α`.

REMAINING for card 7:
- **(7c)**: `c_k = Z_* Σ_n P_*(n) μ(n) X(n)^k` with `P_*(n) = μ(n)²/(Z_* n²)`, `X(n) = 1-n^{-2}`.
  The proof is (2) plus `μ(n)³ = μ(n)`.  Self-contained.
- **(7f)** `|c_k| = Z_*‖Π_* Y_k‖` — needs the parent card's signed coisometry; check the corpus.
- **(7i)–(7j)** `Σ_{n≤x} μ(n)² = x/ζ(2) + O(√x)` (NOT in mathlib; standard proof
  `μ² = Σ_{d²|n} μ(d)` + hyperbola) and the resulting `‖Y_k‖² ~ c k^{-1/2}`.
- **(14a)–(14c)** the Plancherel / zero-free-line beta integral.
- **(15)–(17)** the imported Báez--Duarte sequential endpoint (classical; corpus owns only the
  Nyman–Beurling *distance* criterion).

LANDED (card 7, batch 5): `RHTower/BaezDuarteGibbsChannel.lean` — **(7a)–(7f)**.
The corpus already owned the whole channel: `RHTower/InfiniteMobiusSignedChannel.lean` has
`squarefreeMobiusMass σ n = 1_{Squarefree n} n^{-σ}`, `squarefreeMobiusTotal` (= `Z_*`, with
`squarefreeMobiusTotal_eq_zetaRatio_re : = ζ(σ)/ζ(2σ)`), `squarefreeMobiusProbability` (= `P_*`),
`infiniteMobiusSignedWeightLp` (= `w_*`, a unit vector), and the synthesis / analysis / projection
operators with the coisometry.  New here at `σ = 2`:
- `bdSpectralValue n = 1 - n^{-2}` (= `X(n)`), `bdFeatureLp k` (= `Y_k`),
- `bdCoeff_eq_channel : c_k = Z_* ⟪w_*, Y_k⟫`  — the proof needs only `μ(n)·1_{Squarefree n} = μ(n)`,
  NOT `μ³ = μ`,
- `projection_bdFeature : Π_* Y_k = (c_k/Z_*) • w_*` and
  `norm_bdCoeff_eq_channel : ‖c_k‖ = Z_* ‖Π_* Y_k‖`.

STILL OPEN on card 7 (each needs new mathematics):
1. `(7i)` `Σ_{n≤x} μ(n)² = x/ζ(2) + O(√x)` — NOT in mathlib, NOT in the corpus.  Standard proof:
   `μ(n)² = Σ_{d² | n} μ(d)`, then a hyperbola/Dirichlet split.  Needed for `(7j)`
   `‖Y_k‖² ~ (ζ(4)/ζ(2)²)√π/(2√(2k))` and hence for the angle law `(7l)–(7m)`.
2. `(14a)–(14c)` the one-sided Fourier transform of `m_0` and the Plancherel beta identity.
3. `(15)` the Báez--Duarte SEQUENTIAL criterion `RH ⟺ c_k = O_ε(k^{-3/4+ε})`.  The corpus owns only
   the Nyman–Beurling *distance* criterion (`riemannHypothesis_of_tendsto_bdDistDiscrete`), which is
   a different statement.

LANDED (card 7, batch 6): `RHTower/SquarefreeCounting.lean` — the first half of `(7i)`.
- `sum_moebius_sq_dvd_Icc : Σ_{d ∈ [1,n], d² ∣ n} μ(d) = μ(n)²` (reindexing the corpus's
  `RHTower.sqrtPart_moebius_mul_zeta`).  NOTE: `GaloisForLFunctions.HTGeometry.sum_moebius_sq_dvd`
  (`HTGeometry/SquarefreeClockLaw.lean:321`) is the SAME identity indexed by `n.divisors`; that file
  also has `sqrtMoebius`.  Search BOTH namespaces before adding anything Möbius-square-flavoured.
- `sum_moebius_sq_Icc : Σ_{n ≤ N} μ(n)² = Σ_{d ≤ N} μ(d)·⌊N/(d·d)⌋`, using the corpus's
  `RHTower.Sieve.card_Icc_filter_dvd` (`Sieve/RamarePhaseError.lean:51`).

NEXT (finishing `(7i)`): the estimate `|Σ_{n≤N} μ(n)² − N/ζ(2)| ≤ 3√N`.  Route, all pieces
elementary: only `d ≤ ⌊√N⌋ =: D` contributes; write `⌊N/d²⌋ = N/d² − {N/d²}`; the fractional part
sum is `≤ D ≤ √N`; `|Σ_{d>D} μ(d)/d²| ≤ Σ_{d>D} 1/d² ≤ 1/D`; and `D ≥ √N/2` for `N ≥ 1` gives
`N/D ≤ 2√N`.  Needs `Σ_{d≥1} μ(d)/d² = 1/ζ(2)` (real form of `LSeries_moebius_eq_inv_riemannZeta`
at `s = 2`) and `riemannZeta_two`.

LANDED (card 7, batch 7): `RHTower/SquarefreeCountingAsymptotic.lean` — **(7i) COMPLETE**:
```lean
theorem abs_sum_moebius_sq_sub_le {N : ℕ} (hN : 1 ≤ N) :
    |(∑ n ∈ Finset.Icc 1 N, ((μ n : ℤ) : ℝ) ^ 2) - (6 / Real.pi ^ 2) * (N : ℝ)|
      ≤ 3 * Real.sqrt (N : ℝ)
```
with `sum_inv_sq_tail_le`, `hasSum_moebius_div_sq : HasSum (fun n => μ(n)/n²) (6/π²)`,
`abs_sum_moebius_div_sq_sub_le`, and `natDiv_frac_mem`.

TRAPS RECORDED
- macOS `sed` does NOT support `\b`; a rename that "succeeds" can silently do nothing.  Use python.
- `RHTower.sum_inv_sq_Icc_le` already existed in `RHTower/SquarefreeLowerDensity.lean` (a DIFFERENT
  statement, `Icc 2 N ≤ 3/4 − 1/N`).  Same namespace ⇒ the umbrella breaks even though the single
  module builds.  Always elaborate a scratch file importing BOTH the new module and the colliding
  one; `lake build <module>` alone will not catch it.
- `intervalIntegral.integral_congr_ae` takes `∀ᵐ x ∂μ, x ∈ uIoc a b → f x = g x` (ambient measure
  plus an implication), NOT an a.e. statement w.r.t. the restricted measure.
- `Complex.hasSum_re`, `Summable.tsum_le_of_sum_le`, `Summable.tsum_subtype_le` are the right names
  (`tsum_le_of_sum_le` and `tsum_subtype_le` do not exist).
- `simp only [h] at hC` fails when `hC`'s function is eta-contracted (`LSeries.term f s` rather than
  `fun n => LSeries.term f s n`); use `rw [funext h] at hC`.

LANDED (card 7, batch 8):
- `RHTower/BaezDuarteWaveletCriterion.lean` — **(16)** `bdWaveletPairing_decay_iff` and
  **(17), first arrow** `bdCoeff_decay_of_weightedMoments` (the complete weighted tower gives
  `c_k = O_ε(k^{-3/4+ε})`; at `ε ≥ 1/4` use `α = 0`, else `α = 1/2 − 2ε`, which makes
  `-(1+α)/2 = -3/4+ε` exactly).
- `RHTower/BaezDuarteFeatureNorm.lean` — **(7h), (7j)**: `bdFeatureEnergy`,
  `bdFeatureEnergy_le : ≤ 5/(2√k)` (k ≥ 1) and `le_bdFeatureEnergy : 1/(500√k) ≤ ·` (k ≥ 7),
  hence `norm_bdFeatureLp_sq` and the two-sided `‖Y_k‖² ≍ k^{-1/2}`.
  The UPPER bound is fully elementary — `(1-n^{-2})^{2k} ≤ e^{-2k/n²} ≤ n⁴/(2k²)` for the head and
  `Σ_{n>√k} n^{-2} ≤ 1/⌊√k⌋` for the tail — and needs NO squarefree counting.  The LOWER bound
  restricts to squarefree `n` with `4k < n² ≤ 100k` (Bernoulli gives `(1-n^{-2})^{2k} ≥ 1/2`) and
  counts them with the corpus's `RHTower.quarter_le_card_squarefree`, NOT with `(7i)` — this avoids
  all `k^{1/4}` error bookkeeping.
- `RHTower/BaezDuarteSourceAngle.lean` — **(7l), (7m) unconditional half**: `bdAngle`,
  `norm_bdCoeff_eq_angle`, and `bdAngle_decay_iff : (c_k = O(k^{-3/4+ε})) ↔ (angle_k = O(k^{-1/2+ε}))`.

CARD 7 STATUS: (1)–(13), (7a)–(7m), (16), (17)-first-arrow are all Lean-closed and axiom-clean.
REMAINING: **(14a)–(14c)** only — the one-sided Fourier transform of `m_0`, the beta transform of
the wavelet, and the Plancherel identity on the zero-free line.  ((15), the Báez--Duarte sequential
criterion, is an IMPORTED classical theorem, not proved in the card; (18) and RH are the card's
declared OPEN research problem.)

LANDED (card 7, batch 9): `RHTower/BaezDuarteWaveletLaplace.lean` — **(14b)**
```lean
theorem laplace_bdKernel (k : ℕ) {z : ℂ} (hz : -1 < z.re) :
    (∫ t in Set.Ioi (0:ℝ), ((bdKernel k t : ℝ) : ℂ) * Complex.exp (-(z * (t:ℂ))))
      = (1/2) * (Complex.betaIntegral ((1+z)/2) ((k:ℂ)+1)
          - (2*(k:ℂ)+3) * Complex.betaIntegral ((1+z)/2 + 1) ((k:ℂ)+1))
```
The hypothesis is `Re z > -1`, NOT `Re z > 0`, so it already covers the imaginary axis — which is
exactly what `(14c)` needs.  (The `-z/2·B((1+z)/2, k+2)` form of the card follows from
`Complex.betaIntegral_recurrence` plus `Complex.Gamma_add_one`; the two-beta form above is the same
statement unsimplified.)
`(14a)` is CORPUS-OWNED: `RHTower.causalTransform_criticalMertensVector`
(`RHTower/MobiusCriticalLaplaceIdentity.lean:197`) gives `∫_0^∞ m_0(t)e^{-wt}dt = 1/(w ζ(1+w))` for
`Re w > 0`.

**(14c) IS REACHABLE — full route identified.**  Mathlib DOES have the `L²` Fourier–Plancherel
isometry; the corpus already uses it in `RHTower/MobiusLaplaceMellinPlancherelBridge.lean:145`
via `Lp.norm_fourier_eq`, `Real.fourierTransform_toLp` and
`l2_fourier_coeFn_eq_l1_fourier_of_integrable`.  Steps:
  (A) polarize the isometry to `⟪𝓕 f, 𝓕 g⟫ = ⟪f, g⟫` on `Lp ℂ 2 volume`;
  (B) `𝓕 (bdKernelVector k)` pointwise: `K_k ∈ L¹ ∩ L²`, so
      `l2_fourier_coeFn_eq_l1_fourier_of_integrable` + `laplace_bdKernel` at `z = 2πiξ`;
  (C) `𝓕 criticalMertensVector` — THE CRUX.  `m_0 ∈ L² \ L¹`, so the transform is only an `L²`
      limit.  Route: for `σ > 0` the damped vector `m_0 e^{-σt}` IS `L¹`, and
      `causalTransform_criticalMertensVector` gives its transform as `1/((σ+2πiξ)ζ(1+σ+2πiξ))`;
      `m_0 e^{-σt} → m_0` in `L²` by dominated convergence, so the transforms converge in `L²`;
      pointwise for `ξ ≠ 0` the symbols converge to `1/(2πiξ ζ(1+2πiξ))` using the classical
      zero-free line `ζ(1+it) ≠ 0`; an a.e.-convergent subsequence identifies the two limits.
  (D) assemble; the `iτ` factors cancel and give `c_{k+1} = (1/4π)∫_ℝ B((1-2πiξ)/2, k+2)/ζ(1+2πiξ)`.
Mathlib normalization: `𝓕 f (ξ) = ∫ f(x) e^{-2πixξ} dx`, so the card's `τ` is `2πξ`.

LANDED (card 7, batch 10): `RHTower/BaezDuarteWaveletFourier.lean` — step (B) of the (14c) route:
`integrable_bdKernelVector` (the wavelet is `L¹`, dominated by `(2k+4)·causalPoleVector`) and
`fourierIntegral_bdKernelVector : 𝓕 (bdKernelVector k) ξ = (1/2)(B((1+2πiξ)/2, k+1)
 − (2k+3) B((1+2πiξ)/2+1, k+1))`.
MATHLIB NAMES CONFIRMED for the Plancherel step:
- `Lp.inner_fourier_eq (f g : Lp ℂ 2 volume) : ⟪𝓕 f, 𝓕 g⟫ = ⟪f, g⟫`  ← step (A), free.
- `Lp.norm_fourier_eq`, `Real.fourier_real_eq f w : 𝓕 f w = ∫ v, 𝐞 (-(v*w)) • f v`,
  `Real.fourierChar_apply x : ↑(𝐞 x) = exp (↑(2π x) * I)`.
- `RHTower.l2_fourier_coeFn_eq_l1_fourier_of_integrable` (`RHTower/L2FourierIntegralBridge.lean`)
  identifies the unitary `L²` transform with the classical `L¹` integral.
TRAP: for `c : Circle` and `w : ℂ`, `c • w` is NOT rewritable by `smul_eq_mul` or `Circle.smul_def`;
use `show ((c : ℂ) * w) = _`, which is defeq.

MAJOR CORPUS FIND for (14c) — DO NOT REBUILD:
`GaloisForLFunctions/HTGeometry/HalfLineLaplaceFourier.lean` is the Paley–Wiener / vertical-line
Plancherel layer already:
- `rayLine σ ξ = σ + 2πξ i`, `rayDamp φ σ = 1_{x>0} φ(x) e^{-σx}`,
- `memLp_two_rayDamp`, `integrable_rayDamp`,
- `fourierIntegral_rayDamp : 𝓕 (rayDamp φ σ) ξ = laplaceRay φ (rayLine σ ξ)`,
- `coeFn_fourierTransform_rayDamp` (the `L²` transform, a.e.),
- `memLp_two_laplaceRay_line`, `integral_norm_sq_laplaceRay_line` (**Plancherel on a vertical line**).
Companions: `HTGeometry/HardyDatum.lean` (`hardyPreimage`, `hardyPreimage_weight_ae_eq`),
`HTGeometry/LaplaceRayInjective.lean`, `HTGeometry/HalfLineLaplaceL2.lean`.
Mathlib also has `Lp.inner_fourier_eq : ⟪𝓕 f, 𝓕 g⟫ = ⟪f, g⟫`.
My `dampedMertens` scratch DUPLICATED `rayDamp` — discarded, not installed.

REVISED (14c) PLAN — the σ→0 boundary limit of `ζ` is NOT needed:
```
⟪rayDamp m_0 σ, K_k⟫ = ⟪𝓕(rayDamp m_0 σ), 𝓕 K_k⟫
                     = ∫_ℝ conj(centeredSchurLimit (rayLine σ ξ)) · 𝓕(bdKernelVector k) ξ dξ
```
is EXPLICIT for every `σ > 0` (`centeredSchurLimit z = 1/(z ζ(1+z))` is the corpus symbol, and
`𝓕(bdKernelVector k)` is the beta pair from `BaezDuarteWaveletFourier.lean`).  Its `σ → 0⁺` limit is
`∫_{Ioi 0} m_0 K_k = bdCoeff (k+1)` by dominated convergence (the product is `L¹`, already proved).
So state (14c) as
```lean
theorem ... : Tendsto (fun σ : ℝ => ∫ ξ : ℝ,
    (starRingEnd ℂ) (centeredSchurLimit (rayLine σ ξ)) * 𝓕 (bdKernelVector k) ξ)
  (𝓝[>] 0) (𝓝 (bdCoeff (k+1)))
```
which is the card's zero-free-line beta integral with the limit displayed rather than suppressed.

CARD 7 CLOSED (2026-08-23) — `baez-duarte-critical-mobius-beta-wavelet-law` promoted to stage 3.
Final module: `RHTower/BaezDuarteLineIntegral.lean` — **(14c)** `tendsto_bdLineIntegral`, proved by
pairing the `σ`-damped critical vector against the wavelet, applying `Lp.inner_fourier_eq` with the
corpus's `coeFn_fourierTransform_rayDamp`, and removing the damping by dominated convergence.
NOTE: `inner_lp_eq` collided with `GaloisForLFunctions.inner_lp_eq`
(`HTGeometry/CompactAbelianConvSymmetric.lean`); renamed to `inner_lp_volume_eq`.

9 / 13 CARDS AT STAGE 3.  REMAINING FOUR, each gated on one named classical theorem:
1. `square-aperture-von-mangoldt-correlation-energy` — needs von Koch/Schoenfeld:
   `RH ⟹ |ψ(x) − x| ≤ √x (log x)²/(8π)` for `x > 73.2`.  Everything else on that card
   (the exact finite Fubini identity and the forward implication) is ALREADY formalized in
   `RHTower.CCMSharpPrimeWindowSquareCorrelationEnergy`.
2. `regular-variation-weighted-steinhaus-ldp` — needs Gärtner–Ellis.
3. `kubalalika-parity-weighted-near-diagonal-tail` — needs Granville–Ramaré Thms 9/9' and
   Babu–Sankaranarayanan Thm 1 (Vaughan + exponent pairs).
4. `halasz-ghs-adaptive-coarea-completion` — needs the sharp Halász theorem.

CARD 13 `halasz-ghs-adaptive-coarea-completion` — INVENTORY (do not re-survey).
The corpus already owns most of the Granville–Harper–Soundararajan chain, in
`RHTower/Sieve/`:
- `PartialSumVsTripleConvolution.lean` — steps 1–3: `‖Σ_{n≤N} f(n)‖ log N` vs the triple
  convolution (`norm_sum_Icc_mul_log_sub_ghsTriple_le`).
- `GhsStepFour.lean` — step 4 (`exists_norm_tsum_ghs_smoothWeight_le`), with the vertical integral
  bounded by `√(sieve a)·√(sieve b)`.
- `HalaszGhsMasterBound.lean` — `exists_norm_sum_Icc_mul_log_le`, the whole chain in one
  inequality.  Its docstring says exactly what is missing: "What the bound still awaits is the
  arithmetic evaluation of the two sieve sums".
- `HalaszGhsSharpCutoff.lean` — `norm_sum_Icc_mul_log_le_damped`,
  `norm_sum_Icc_mul_log_le_damped_near`, and a per-block-sieve-level version.
- `HalaszGhsPunctured.lean` — `norm_sum_Icc_mul_log_le_punctured_near` (one exceptional window).
- Supporting: `GallagherAlmostDiagonal.lean`, `MultiplicativeLogRecursion.lean`,
  `SecondLogRecursion.lean`, `MoebiusLogRecursion.lean`, `PerronFiniteSum.lean`,
  `RamareWeight.lean`, `SmoothSum.lean`, `SmoothTilt.lean`, and `PNTPlus/BrunTitchmarsh.lean`.
So card 13 is NOT gated on "build sharp Halász from scratch".  Its remaining pieces are exactly the
card's own lemmas:
- **Lemma B** the adaptive Gallagher–Brun–Titchmarsh mean square
  `∫_{-T}^{T} |Σ_{T² ≤ p ≤ Y} a_p log p · p^{-1-it}|² dt ≤ C Σ |a_p|² log p / p`
  (ONE `log p` on the right — this is the sieve-sum evaluation the master bound awaits);
- **Lemma C** the ordinary-multiplicative (coprime-only) log recursion, correcting the corpus's
  `MultiplicativeLogRecursion` which assumes full multiplicativity;
- Lemmas D–F (cofactor shells, factor-aware truncated Perron, assembly to `(H1)`/`(H2)`).
NEXT: build Lemma B.

LANDED (card 13, batch 1): `RHTower/Sieve/AdaptiveGallagherBrunTitchmarsh.lean` — **Lemma B**.
```lean
theorem gallagher_bt_mean_square_coeff {T : ℝ} (hT : 2 ≤ T) {s : Finset ℕ}
    (hs : ∀ m ∈ s, Nat.Prime m) (hsT : ∀ m ∈ s, T ^ 2 ≤ (m : ℝ)) (a : ℕ → ℂ) :
    (∫ w in Set.Icc (-(T / (2*π))) (T / (2*π)),
        ‖logPoly (fun p => a p * (Real.log p : ℂ) / (p : ℂ)) s w‖ ^ 2)
      ≤ 2250 * ∑ p ∈ s, ‖a p‖ ^ 2 * Real.log p / (p : ℝ)
```
ONE `log p` on the right, exactly as the card's `(B1)` demands.  Chain:
- `cube_mul_le_exp_half : 6(1+u/2)³u ≤ 288 e^{u/2}` — every coefficient of
  `288·Σ_{i<6}(u/2)^i/i! − 6u(1+u/2)³` is nonnegative, so `nlinarith` closes it outright.
- `bt_error_le_main : 6√H(1+log√H)³ ≤ 288 H/log H` (H > 1) — the Brun–Titchmarsh error term at
  sieve level `√H` is a bounded multiple of the main term, so
  `primesBetween_le_div_log : primesBetween a (a+H) ≤ 292 H / log H`.
- `logNeighbourCount_le_of_prime : (logNeighbourCount s (1/T) p : ℝ) ≤ 1800 p/(T log p)`
  for prime-supported `s` and `p ≥ T²`.  The multiplicative window `|log p − log m| < δ` is put
  inside the ADDITIVE window `[p(1−δ), p(1+2δ)]` using only `1−δ ≤ e^{−δ}` and
  `e^δ ≤ 1/(1−δ) ≤ 1+2δ` (δ ≤ 1/2); then `H = 3δp ≥ 3√p` gives `log H ≥ (log p)/2`.
- assembled against the corpus's `integral_Icc_normSq_logPoly_le_count` at `δ = 1/T`,
  `W = T/(2π)`, where the hypothesis `2πδW ≤ 1` holds with equality.

LANDED (card 13, batch 2): `RHTower/Sieve/CoprimeLogRecursion.lean` — **Lemma C**.
```lean
theorem norm_sum_mul_log_sub_vonMangoldt_le_coprime {f : ℕ → ℂ}
    (hf : ∀ a b : ℕ, Nat.Coprime a b → f (a * b) = f a * f b) (hbdd : ∀ n, ‖f n‖ ≤ 1) (N : ℕ) :
    ‖(∑ m ∈ Finset.Icc 1 N, f m * (Real.log m : ℂ))
        - ∑ d ∈ Finset.Icc 1 N, (Λ d : ℂ) * f d * ∑ k ∈ Finset.Icc 1 (N / d), f k‖
      ≤ (16 + (8 + RHTower.Mertens.mertensTail)) * (N : ℝ)
```
This is the ORDINARY-multiplicative correction the card asks for; the corpus's
`sum_mul_log_eq_vonMangoldt` needs `f(ab) = f(a)f(b)` with no coprimality condition.
Structure:
- `sum_mul_log_eq_vonMangoldt_raw` — the divisor swap with NO multiplicativity at all:
  `∑_{m≤N} f(m) log m = ∑_{d≤N} Λ(d) ∑_{k ≤ N/d} f(dk)`.
- `minFac_dvd_of_not_coprime_primePow` — at a prime power `d`, `¬Coprime d k → d.minFac ∣ k`.
  This is what makes the defect `f(dk) − f(d)f(k)` supported on a single arithmetic progression.
- `norm_sum_shift_sub_le` — the inner defect is `≤ 2⌊(N/d)/minFac d⌋`, via
  `card_Icc_filter_dvd`.
- the split into primes and prime powers: the prime part is `≤ 2N ∑_p log p/p² ≤ 8N` using
  `sum_log_div_sq_Icc_le : ∑_{2≤n≤N} log n/n² ≤ 4` (from `log n ≤ 2√n` and
  `RHTower.sum_inv_sqrt_cube_le`, built for card 9); the prime-power part reuses the corpus's
  `norm_sum_notPrimeVonMangoldt_weight_le` with the truncated weight
  `W d = if IsPrimePow d then (defect) else 0`, whose size is `≤ N/d` because `minFac d ≥ 2`.
TRAP: `sum_log_div_sq_le` already exists in `RHTower/EulerTiltMeanEnergy.lean` (same namespace,
different statement — indexed by an arbitrary `Finset`); renamed mine to `sum_log_div_sq_Icc_le`.

LANDED (card 13, batch 3): `RHTower/Sieve/MertensIntervalShell.lean` — **Lemma A, (A3)–(A6)**.
- `mertensIntervalConst = log 4 + 1 + 2·logSqTailConst`, and
  `sum_log_div_prime_interval_le : ∑_{p ∈ s} log p/p ≤ log b − log a + mertensIntervalConst`
  for any `s ⊆ primesLE b \ primesLE a` — just the DIFFERENCE of the corpus's
  `mertensFirst_upper` and `mertensFirst_lower`.
- `sum_log_div_prime_mul_weight_le` **(A4)** and `sum_log_div_prime_mul_weight_sq_le` **(A5)**:
  against any weight `v` with `u ≤ v p` on the shell, the sums are
  `≤ (log b − log a + C)/u` and `≤ (log b − log a + C)/u²`.  Stated with an ABSTRACT `v`, so the
  cofactor logarithm `v_p = log(x/p)` of Lemma D plugs straight in.
- `(A6)` is `mertensFirst_upper` verbatim.
TRAP: `primesLE_subset` already exists in `RHTower/RouteEEulerDeficitTransport.lean` (same
namespace); mine is `primesLE_subset_of_le`.
CARD 13 STATE: Lemmas A, B, C are Lean-closed.  Remaining: Lemma D (cofactor shells — the shell
partition `P_k` and the trivial estimate `(D4)`), Lemma E (factor-aware truncated Perron), and the
assembly to `(H1)`/`(H2)` against `HalaszGhsMasterBound.exists_norm_sum_Icc_mul_log_le`.

LANDED (card 13, batch 4): `RHTower/Sieve/GhsCofactorShell.lean` — **Lemma D, (D4)**.
```lean
theorem norm_ghsShellSum_le {f : ℕ → ℂ} (hbdd : ∀ n, ‖f n‖ ≤ 1) {N : ℕ} {S : Finset ℕ}
    {u : ℝ} (hu : 0 < u) {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b)
    (hS : S ⊆ Nat.primesLE b \ Nat.primesLE a)
    (hv  : ∀ p ∈ S, u ≤ Real.log ((N : ℝ) / p))
    (hvup: ∀ p ∈ S, Real.log ((N : ℝ) / p) ≤ Real.exp 1 * u) :
    ‖ghsShellSum f N S‖
      ≤ (N : ℝ) * (Real.exp 1 * u + Real.log 4)
          * ((Real.log b - Real.log a + mertensIntervalConst) / u)
```
On a shell the interval length is `log b − log a = (e−1)u`, so the right-hand side is
`≍ N·u = N·e^{-k} log x`, which is `(D4)`.  Supporting: `ghsShellInner` (the inner double sum over
`q` prime and `n`) and `norm_ghsShellInner_le : ≤ (N/p)(log(N/p) + log 4)`, which is `(A6)` applied
inside.  The shell hypotheses are stated ABSTRACTLY (`u ≤ log(N/p) ≤ e·u` plus a prime interval),
so the concrete `u_k = e^{-k} log x`, `P_k` of `(D1)` instantiate them directly.
TRAP: `ghsInner`/`norm_ghsInner_le` already exist in `RHTower/Sieve/GhsCoefficients.lean` (same
namespace) as the SINGLE-TERM coefficient `f q log q`; mine are `ghsShellInner` /
`norm_ghsShellInner_le`.  That file also has `ghsOuter f N p = f p·log p/log⌊N/p⌋`, which is the
corpus's version of my shell weight — use it when wiring `(D4)` into the master bound.

LANDED (card 13, batch 5): `RHTower/Sieve/GhsShellEnergy.lean` — **Lemma F, (F1)**.
```lean
theorem integral_normSq_shellPoly_le {f : ℕ → ℂ} (hbdd : ∀ n, ‖f n‖ ≤ 1)
    {T : ℝ} (hT : 2 ≤ T) {S : Finset ℕ} (hSp : ∀ p ∈ S, Nat.Prime p)
    (hST : ∀ p ∈ S, T ^ 2 ≤ (p : ℝ))
    {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) (hS : S ⊆ Nat.primesLE b \ Nat.primesLE a)
    {v : ℕ → ℝ} {u : ℝ} (hu : 0 < u) (hv : ∀ p ∈ S, u ≤ v p) :
    (∫ w in Set.Icc (-(T/(2*π))) (T/(2*π)),
        ‖logPoly (fun p => (f p / (v p : ℂ)) * (Real.log p : ℂ) / (p : ℂ)) S w‖ ^ 2)
      ≤ 2250 * ((Real.log b - Real.log a + mertensIntervalConst) / u ^ 2)
```
This is `I_1(k) ≤ C/u_k` once the shell is inserted: Lemma B supplies the single `log p` and
`(A5)` converts `∑_p log p/(p log²(x/p))` into `1/u`.  The card's requirement "all primes in `P_k`
exceed `T²`" is the hypothesis `hST`, which is exactly what Lemma B needs.
CARD 13 STATE: Lemmas A, B, C, D and F(1) are Lean-closed.  Remaining: Lemma E (the factor-aware
truncated Perron error `(E1)`, whose own inputs are the lattice estimate `(E3)` plus `(A1)`,`(A4)`,
`(A6)` — all but `(E3)` now available), the second reciprocal energy `(F2)`, and the assembly to
`(H1)`/`(H2)`.

LANDED (card 13, batch 6): `RHTower/Sieve/GhsLatticeCutoff.lean` — **Lemma E, (E3)**.
```lean
theorem lattice_min_sum_le {X d T : ℝ} (hX : 0 < X) (hd : 0 < d) (hT : 0 < T) (M : ℕ) :
    ∑ n ∈ Finset.Icc 1 M, min 1 (X / (T * |X - d * (n : ℝ)|))
      ≤ 3 + (4 * X / (T * d)) * (1 + Real.log M)
```
`n₀ = ⌊X/d⌋`; the three `n` with `|n − n₀| ≤ 1` are bounded by `1` each, and every other `n` has
`|X − dn| ≥ d|n − n₀|/2`, so the tail is a sum of reciprocals of DISTINCT integers.
CORPUS ASSET (I duplicated ~90 lines before finding it — search first):
`RHTower/Sieve/DistinctReciprocalSum.lean` already owns
- `sum_inv_le_sum_Icc` (reciprocals of `k` distinct positive integers ≤ the `k`-th harmonic number),
- `sum_inv_le_one_add_log : ∑_{a ∈ A} 1/a ≤ 1 + log |A|`,
- **`sum_inv_abs_le_of_injOn : ∑_{i ∈ s} 1/|v i| ≤ 2(1 + log |s|)`** for injective integer-valued
  `v` with `v i ≠ 0` — exactly the lattice tool `(E3)` needs.
Also: the harmonic bound `sum_inv_succ_le_one_add_log` lives in namespace `ContinuousLinearMap`
(module `HTGeometry/DixmierIdeal.lean`) — the search tool prints the MODULE, not the namespace.

CARD 13 STATE: Lemmas A, B, C, D, E(3), F(1) are Lean-closed.  Remaining: `(E4)`–`(E6)` (the
Perron error split, which now has all its inputs: the corpus's
`RHTower.Sieve.norm_sum_lt_sub_perron_integral_le` gives the factorized error, `(E3)` handles the
near part, `(A3)` the far part), the second reciprocal energy `(F2)`, and the assembly to
`(H1)`/`(H2)`.

LANDED (card 13, batch 7): `RHTower/Sieve/GallagherBoundedHeight.lean` — the engine for `(F2)`.
```lean
theorem gallagher_bt_mean_square_all {S : Finset ℕ} (hs : ∀ m ∈ S, Nat.Prime m)
    {a : ℕ → ℂ} (hbdd : ∀ n, ‖a n‖ ≤ 1) :
    (∫ w in Set.Icc (-(2/(2*π))) (2/(2*π)),
        ‖logPoly (fun p => a p * (Real.log p : ℂ) / (p : ℂ)) S w‖ ^ 2)
      ≤ 4500 * ∑ p ∈ S, ‖a p‖ ^ 2 * Real.log p / (p : ℝ) + 8 * (2 / Real.pi)
```
Lemma B needs primes `≥ T²`; at the bounded height `T = 2` that excludes only `2` and `3`, whose
polynomial is bounded outright (`norm_logPoly_small_le : ≤ 2`), so splitting the support and paying
`(a+b)² ≤ 2a² + 2b²` removes the restriction.  This is exactly the form `(F2)` needs on each unit
cell, after twisting the coefficients by `q^{-ih}` — the twist is free because `‖a_q q^{-ih}‖ =
‖a_q‖`, so no separate twisted lemma is required.
Also landed: `logPoly_union` (additivity in a disjoint support).
TRAP: `continuous_normSq_logPoly` already exists in `RHTower/Sieve/LorentzianMeanSquare.lean`;
reused rather than redefined.
CARD 13 STATE: Lemmas A, B, C, D, E(3), F(1) and the `(F2)` mean-square engine are Lean-closed.
Remaining: `(E4)`–`(E6)` (the Perron error split), the `F_x` / `L_f` bookkeeping that turns the
engine into `(F2)` itself, and the assembly to `(H1)`/`(H2)`.

LANDED (card 13, batch 8): `RHTower/Sieve/PerronCutoffComparisons.lean` — the pointwise core of
`(E4)`–`(E6)` and of the `(F2)` cell decomposition.
- `abs_sub_one_le_two_mul_abs_log : 1/2 ≤ y → y ≤ 2 → |y − 1| ≤ 2|log y|` — the NEAR part: with
  `y = x/n` this turns `|log(x/(pqn))|` into `|x − pqn|/x`, which is what feeds `(E3)`.
- `log_two_le_abs_log : 0 < y → (y ≤ 1/2 ∨ 2 ≤ y) → log 2 ≤ |log y|` — the FAR part, giving
  `min(1, 1/(T|log·|)) ≤ 1/(T log 2)`.
- `inv_one_add_sq_le_cell : |t − h| ≤ 1/2 → 1/(1+t²) ≤ 4/(1+h²)` — the Cauchy weight on a unit
  cell, which is how `(F2)` pulls `sup_{|v−h|≤1/2}|F_x(1+iv)|²/(h²+1)` out of the integral.

LANDED (card 13, batch 9): `(E4)`–`(E6)` and `(E1)`'s error term, in two modules.

`RHTower/Sieve/FactorAwarePerronError.lean`
- `truncPerronWeight T y = if log y = 0 then 1 else min 1 (1/(T|log y|))` — the truncated Perron
  weight carrying its TRUE value `1` at the cutoff itself.  Lean's `1/0 = 0` would have silently
  set the cutoff term to `0`, turning the bound into a false statement about the real Perron
  error; the `if` removes that, at the cost of one extra unit in `(E5)`.
- `perron_weight_near_le` / `perron_weight_far_le` — the two pointwise comparisons in the form
  actually consumed: `1/(T|log(x/n)|) ≤ 4x/(T|x−n|)` on `[x/2, 2x]`, and `≤ 1/(T log 2)` off it.
- `perron_near_pair_le` **(E5)**: `∑_{n ≤ M, near} (x/(dn))·w ≤ 2(3 + 16x/(Td))(1+log M) + 2`.
  The `+2` is the cutoff index, isolated by `card_filter_mul_eq_le_one` (a positive `d` has at
  most one multiple equal to `x`).  The `16` is `(E3)` run at height `T/4`.
- `perron_far_pair_le` **(E6)**: `∑_{n ≤ M, far} (x/(dn))·w ≤ (x/(T log 2 · d))(1 + log M)`,
  by `sum_Icc_one_div_le_one_add_log`.

`RHTower/Sieve/FactorAwarePerronTotal.lean`
- `perron_pair_total_le`: the two halves add to `8 + (34x/(Td))(1 + log M)`.  `34 = 32 + 2` with
  `1/log 2 < 2` from `Real.log_two_gt_d9`.
- `perron_triple_error_le` **(E1)**: for any prime sets `P`, `Q` and any nonnegative weight `w`,
  ```
  ∑_{p,q} w(p,q) ∑_{n ≤ M} (x/(pqn))·truncPerronWeight T (x/(pqn))
    ≤ 8·∑_{p,q} w(p,q) + (34x/T)(1 + log M)·∑_{p,q} w(p,q)/(pq).
  ```
  This is the point of the card's Lemma E: the `1/(pq)` on the main term is what lets `(A4)`/`(A6)`
  absorb it.  Collapsing to one coefficient sequence would leave `∑ w` there instead and force a
  much larger `T`.

CARD 13 STATE: Lemmas A, B, C, D, E (all of `(E1)`–`(E6)`) and `(F1)` are Lean-closed, and the
`(F2)` mean-square engine is built.  Remaining: the `F_x`/`L_f` bookkeeping that turns the engine
into `(F2)` itself, and the assembly to `(H1)`/`(H2)`.

LANDED (card 13, batch 10): `(F2)`, the second reciprocal energy, in three modules.

`RHTower/Sieve/CauchyCellEnergy.lean`
- `cell_energy_le` / `cell_energy_scaled_le`: `∫_{-T}^{T} B(t)F(t)/(1+t²) dt ≤ ∑_k 4 Φ_k E_k/(1+c_k²)`
  for any tiling by cells of half-width `ρ ≤ 1/2`, where `Φ_k` bounds the slowly varying factor on
  cell `k` and `E_k` bounds `∫_{cell k} B`.  The cell width is a parameter because the mean-square
  estimate available for `B` fixes it — for Lemma B at height `2` it is `1/π`, not `1/2`.
  `intervalIntegral.sum_integral_adjacent_intervals` does the tiling; `inv_one_add_sq_le_cell` is
  the only analytic input.

`RHTower/Sieve/TwistedCellMeanSquare.lean`
- `integral_cell_normSq_logPoly_bt_le`: Lemma B at height `2` holds on EVERY interval of that
  length with the SAME arithmetic right-hand side, because a frequency shift only twists the
  coefficients by `n^{-iu}`.  Built on the corpus's `logPoly_add_right` and `norm_twist`
  (`Sieve/LogPolyTranslation.lean`) — do not re-derive the twist.
  TRAP: the corpus already owns `integral_cell_normSq_logPoly_le` in `Sieve/HalaszCellAggregate.lean`
  with the SHARP near-diagonal weight `700 q/log q + 1`.  That is the wrong weight here: `(F2)`
  needs `log q/q`, so the two are complementary, not duplicates.  The name had to be changed to
  `..._bt_le`.

`RHTower/Sieve/SecondReciprocalEnergy.lean`
- `sum_inv_one_add_sq_scaledCentre_le`: `∑_k 1/(1+c_k²) ≤ 2π/ρ`, UNIFORMLY in the number of cells.
  Each centre is charged to `∫_{cell k} dt/(1+t²)` (the cell comparison run backwards), and the
  cells are disjoint, so the total is `(2/ρ)·arctan`-difference `≤ 2π/ρ`.
- `cauchy_energy_bt_le` **(F2)**: for a prime set `S`, coefficients `‖a‖ ≤ 1` and any continuous
  envelope `F` with `0 ≤ F ≤ L`,
  ```
  ∫_{-T}^{T} ‖∑_{q∈S} a_q log q · q^{2πiw}‖² · F(w)/(1+w²) dw
      ≤ 8π² L (4500 ∑_{q∈S} ‖a_q‖² log q/q + 16/π),
  ```
  with NO dependence on `T`.  This is the card's `(F2)` with `L = L_f(x)²`: the length of the range
  cancels because the Cauchy weight is summable and the mean square is cell-invariant.

CARD 13 STATE: Lemmas A, B, C, D, E (`(E1)`–`(E6)`) and F (`(F1)`, `(F2)`) are Lean-closed.
Remaining: the Cauchy–Schwarz step `(F3)` and the assembly to `(H1)`/`(H2)`.

LANDED (card 13, batch 11): `(F3)`, `(H1)` and `(H2)`, in four modules.

`RHTower/Sieve/EnergyCauchySchwarz.lean`
- `integral_mul_sq_le`: Cauchy–Schwarz for an interval integral of continuous functions, proved as
  the discriminant of `λ ↦ ∫ (f − λg)²`.  No `L²` structure and no completeness — the degenerate
  case `∫g² = 0` is handled by the affine argument (`0 ≤ A − 2λB` for ALL `λ` forces `B = 0`), which
  avoids needing "continuous, nonnegative, zero integral ⟹ zero".
- `energy_cauchy_schwarz_le` **(F3)**:
  `∫ A·(B√F/√(1+t²)) ≤ √(I₁ I₂)` whenever `∫A² ≤ I₁` and `∫B²F/(1+t²) ≤ I₂`.
- `sqrt_reciprocal_energies`: `√((C₁/u)·(C₂L²u)) = √(C₁C₂)·L` — the shell parameter cancels
  because `(F1)` carries `u⁻¹` and `(F2)` carries `u`.

`RHTower/Sieve/ShellAssembly.lean`
- `sum_exp_neg_tail_le`: `∑_{K₀ ≤ k < K} e^{−k} ≤ 2e^{−K₀}` (`e/(e−1) < 2` via `1 + 1 ≤ e`).
- `shell_assembly_le`: with a uniform bound `c₁` and a geometric bound `c₂e^{−k}` on every shell,
  `∑_{k<K} S_k ≤ c₁K₀ + 2c₂e^{−K₀}` for EVERY cut `K₀` — no relation between `K₀` and `K` needed.

`RHTower/Sieve/ShellTotalCost.lean`
- `exists_cut_index`: a `K₀` with `e^{−K₀} ≤ L/y` and `K₀ ≤ max 0 (log(y/L)) + 1`.
- `shell_total_le` **(H1)**: `∑_{k<K} S_k ≤ A x (L+1) K₀ + 2 B x L` with that `K₀`.  Dividing by
  `y = log x` and adding the `(D3)` error is the card's `(H1)` verbatim.

`RHTower/Sieve/HalaszExponent.lean`
- `mul_one_add_log_div_mono`: `t ↦ t(1 + log(y/t))` is monotone on `(0, y]`.  Proof is elementary:
  after `u = s/t` it reduces to `−u log u ≤ 1 − u`, i.e. `log(1/u) ≤ 1/u − 1`.
- `shell_cost_of_exp_bound` **(H2)**: `L ≤ c y e^{−M}` ⟹ `L·K₀ ≤ c y e^{−M}(1 + M − log c)`.
  This is exactly the card's warning made precise: the PRODUCT `L·K₀` is what an exponential bound
  on `L` controls, because the map above is monotone.  A standalone bound on `L` loses the
  logarithm and the `(1+M)e^{−M}` shape with it.

CARD 13 STATE: every lemma of the card — A, B, C, D, E (`(E1)`–`(E6)`), F (`(F1)`–`(F3)`) and the
assembly to `(H1)`/`(H2)` — is Lean-closed and axiom-clean.

=== CARD 13 PROMOTED TO STAGE 3 (docs/drafts/pipeline/3-formalized/) ===
Its "Lean formalization map -- notes only" section was replaced by a step→declaration→module table
and the `2 -> 3` gate ticked.  Joint elaboration of all 18 card-13 modules verified in one scratch
import (no namespace collisions).

CARD 12 (`kubalalika-parity-weighted-near-diagonal-tail`) — batch 1 landed.
What the card PROVES itself (as opposed to imports) is three things, and all three are now Lean:

`RHTower/Sieve/ReciprocalPhaseStability.lean` — the card's equation (1), the phase-stability lemma.
- `reciprocalPhase T r u = (T/2π) log(1 + r/u)`, `reciprocalParam T r = Tr/2π`.
- `abs_log_one_add_sub_le_sq : |log(1+z) − z| ≤ z²` for ALL `z ≥ 0` (no upper restriction needed:
  `log(1+z) ≤ z` and `log(1+z) ≥ z/(1+z) ≥ z − z²`).
- order 0: `abs_reciprocalPhase_sub_le : |H − X/u| ≤ ε·(X/u)` whenever `r/u ≤ ε`.
- order 1: `hasDerivAt_reciprocalPhase` gives `H'(u) = −(T/2π)·r/(u(u+r))` exactly, and
  `abs_deriv_reciprocalPhase_add_le : |H' + X/u²| ≤ ε·(X/u²)` — the identity behind it is
  `1/u² − 1/(u(u+r)) = r/(u²(u+r))`, so the relative error is exactly `r/(u+r) ≤ r/u`.
- order 2: `hasDerivAt_deriv_reciprocalPhase` gives `H''(u) = (T/2π)r(2u+r)/(u(u+r))²`, and
  `abs_deriv2_reciprocalPhase_sub_le : |H'' − 2X/u³| ≤ 3ε·(X/u³)` — the relative error is
  `r(3u+2r)/(u+r)²`, and `(3+2z)/(1+z)² ≤ 3` for `z ≥ 0`.
  These are the orders the exponent-pair derivative tests actually consume.

`RHTower/Sieve/VonMangoldtParityCorrection.lean` — the card's parity reduction.
- `eq_two_pow_of_vonMangoldt_ne_zero`: an even integer in the support of `Λ` is a power of two
  (`vonMangoldt_ne_zero_iff` → `isPrimePow_nat_iff` → `2 ∣ p^k` forces `p = 2`).
- `sum_vonMangoldt_even_le : ∑_{m ≤ N, 2∣m} Λ(m) ≤ log N`.  Sharper than the card's `O(log T)`
  claim and with no constant: the support injects into `{2^j : 1 ≤ j ≤ log₂ N}`, each term is
  `log 2`, and `(log₂ N)·log 2 ≤ log N` by `Nat.pow_log_le_self`.

`RHTower/Sieve/PSeriesTailAboveCutoff.lean`
- `sum_rpow_neg_tail_le : c > 1 → ∑_{R ≤ r ≤ N} r^{−c} ≤ (c/(c−1))·R^{1−c}`.  New: the corpus owned
  only the head (`RHTower.sum_rpow_neg_head_le`, `c < 1`) and the `R = 1` tail integral.  REUSED the
  corpus's `antitoneOn_rpow_neg` (`Sieve/ZetaRealBound.lean`) rather than re-deriving it; the new
  integral piece is `integral_rpow_neg_Icc_le` (arbitrary lower endpoint).

`RHTower/Sieve/NearDiagonalOffsetBookkeeping.lean` — the card's `(6)`–`(8)`.
- `tail_contribution_le : T^θ ∑_{r ≥ T^a} r^{−c} ≤ (c/(c−1))·T^{θ−a(c−1)}`.
- `head_contribution_le : T^θ ∑_{r ≤ K T^a} r^{−c} ≤ (1 + K^{1−c}/(1−c))·T^{θ+a(1−c)}`.
- The four exponent identities and `kubalalika_exponent_dominates : max(15/16, 53/54, 7/8) = 53/54`.

CARD 12 REMAINING: the three regime bounds `(2)`, `(3)`, `(4)` for `S_r(I) = ∑_{m∈I} Λ(m) e(H(m))`.
These are Granville–Ramaré Thms 9/9′ and Babu–Sankaranarayanan Thm 1 — Vaughan's identity followed
by exponent-pair derivative tests.  The corpus owns `HTGeometry/VanDerCorputInequality.lean`
(`vanDerCorput_correlation_bound`) and an abstract exponent-pair calculus
(`HTGeometry/ExponentPairSelfDuality.lean`), but NOT Vaughan's identity and NOT a proved
`(κ, λ)` pair.  That is the next layer.

CARD 12 — batch 2, and a DUPLICATION CAUGHT AND REVERSED.

`RHTower/Sieve/ReciprocalPhaseStability.lean` was REWRITTEN.  The corpus already owns
`RHTower/NearDiagonalPhaseCurvature.lean` with EXACTLY the same phase
(`nearDiagonalPhase T r u = (T/2π) log(1 + r/u)`), its two derivative closed forms
(`nearDiagonalPhaseD1`, `nearDiagonalPhaseD2`) and both `HasDerivAt` proofs.  My first version
re-derived all of it.  The module now imports it and keeps ONLY the genuinely new content:
- `reciprocalParam T r = Tr/2π`, `abs_log_one_add_sub_le_sq`,
- `abs_nearDiagonalPhase_sub_le`, `abs_nearDiagonalPhaseD1_add_le`,
  `abs_nearDiagonalPhaseD2_sub_le` — the card's equation (1) at orders 0, 1, 2.
LESSON: for card 12 the corpus's near-diagonal stack (built for card 9) is the base layer.  Search
`nearDiagonal*` BEFORE writing anything about this phase.

`RHTower/Sieve/VaughanIdentity.lean` — NEW, and reusable well beyond this card.
- `truncAF f U` truncates an arithmetic function at `U`.
- `vaughan_identity (U V) : Λ = Λ_U − ζ·Λ_U·μ_V + log·μ_V + (Λ − Λ_U)(1 − ζ·μ_V)`, proved as a
  ONE-LINE `linear_combination μ_V * (Λ * ζ = log)` in the commutative ring of arithmetic
  functions.  No divisor bookkeeping at all — the Dirichlet-series derivation IS the Lean proof.
- `vaughan_apply_of_gt`: above `U` the first term drops out.
- `one_sub_zeta_mul_truncAF_moebius_apply_eq_zero`: the type-II second factor vanishes on `[1, V]`,
  so the bilinear form really is supported in `m > U`, `k > V`.

CORPUS ASSET FOUND (do not rebuild): `RHTower/Sieve/SecondDerivativeTest.lean` owns a GENERAL van
der Corput second-derivative test,
`second_derivative_test' (g g' g'' : ℝ → ℝ) (x₀ : ℝ) (N : ℕ) ... : ‖S‖ ≤ 8Nh√λ + 12/√λ`
for `λ ≤ g'' ≤ hλ` on the span, via the region-index / Kuzmin–Landau route.

CARD 12 NEXT LAYER: the regime bounds `(2)`, `(3)`, `(4)`.  With Vaughan's identity and the
second-derivative test in hand these reduce to
  (i) type-I sums `∑_{d ≤ D} |∑_{m} e(F_r(dm))|` — the second-derivative test applies directly to
      each inner sum after the stability lemma rescales `X ↦ X/d`;
  (ii) type-II bilinear sums `∑∑ a_b c_k e(F_r(bk))` — Cauchy–Schwarz plus Weyl differencing,
      for which the corpus has `HTGeometry/VanDerCorputInequality.lean`;
  (iii) the exponent-pair bookkeeping that turns (i)+(ii) into `X^{1/4}M^{1/2}` etc.

CARD 10 (`square-aperture-von-mangoldt-correlation-energy`) — the von Koch layer opened.
`VK0` turned out to be corpus-owned (`RHTower.exists_bound_norm_riemannZeta_strip`) — my duplicate
was discarded, the THIRD duplication caught this session.
`VK2` is now Lean-closed and axiom-clean, in `RHTower/Sieve/ZetaLandauCriticalDisc.lean` and
`RHTower/Sieve/ZetaLogDerivCriticalBound.lean`:
  `RiemannHypothesis → ‖ζ'/ζ(σ+iγ)‖ ≤ C log|γ|/(σ − 1/2)` for `1/2 < σ ≤ 9/8`, `|γ| ≥ 7`.
The mechanism is a Landau disc of radius 5 (inside 6) at the centre `9/8 + iγ`: the identity radius
`5/8` reaches the critical line exactly.  Full details in
`docs/drafts/pipeline/1-in-progress/von-koch-conditional-chebyshev-error.md`.

SESSION TALLY: 10 of 13 cards at stage 3.  New modules this session, all axiom-clean:
  card 13 (11): PerronCutoffComparisons, FactorAwarePerronError, FactorAwarePerronTotal,
    CauchyCellEnergy, TwistedCellMeanSquare, SecondReciprocalEnergy, EnergyCauchySchwarz,
    ShellAssembly, ShellTotalCost, HalaszExponent, HalaszCellFormSplit
  card 12 (6): ReciprocalPhaseStability, VonMangoldtParityCorrection, PSeriesTailAboveCutoff,
    NearDiagonalOffsetBookkeeping, VaughanIdentity, DilatedNearDiagonalSum
  card 10 (2): ZetaLandauCriticalDisc, ZetaLogDerivCriticalBound

CARD 10 — `VK3` CLOSED.  `RHTower/Sieve/PerronInfiniteSeries.lean` (axiom-clean) proves the
truncated Perron formula for an infinite Dirichlet series, which the corpus did not own; the finite
version in `Sieve/PerronFiniteSum.lean` cannot be pushed to the full series by truncation.  Card 10
now needs only `VK4`, the contour shift.

CARD 10 — the Perron error is closed.  Three more axiom-clean modules:
`RHTower/Sieve/VonMangoldtPerronSeries.lean` (the `LSeries`↔`n^{-s}` bridge and the summability
hypothesis), `RHTower/Sieve/PerronErrorSplit.lean` (the far half plus the half-integer
reciprocal-distance sum), `RHTower/Sieve/PerronErrorNearHalfInt.lean` (the near half).
Card 10 now needs ONLY the contour shift; all of its inputs are Lean-closed.

CARD 10 — VK4 half done.  Three more axiom-clean modules: `Sieve/ContourShiftIdentity.lean`
(`vIntegral_shift`, an identity), `Sieve/PerronIntegrandResidue.lean` (`perron_integrand_residue`:
the integrand has a simple pole at `s = 1` with residue `x`), and
`Sieve/PerronRectangleResidueUnderRH.lean` (`rectangleIntegral_perron_eq`: under RH the rectangle
integral IS `x`).  What is left on card 10 is bounding the shifted vertical side and the two
horizontal sides against `exists_logDeriv_zeta_bound_rh`, then assembling.

CARD 10 — the side estimates are closed.  `Sieve/ZetaLogDerivLineBound.lean`
(`exists_logDeriv_zeta_line_bound`: one constant for the WHOLE line `Re s = σ`, removing the
`|γ| ≥ 7` restriction by compactness) and `Sieve/VerticalLogWeight.lean` (`integral_log_weight_le`:
the `O(log²T)` weight integral).  Card 10 is now pure assembly.

CARD 10 — all four sides of the Perron contour are Lean-closed:
`Sieve/PerronVerticalSide.lean` (the shifted vertical side, `≤ K x^σ log²T`),
`Sieve/PerronHorizontalSide.lean` (each horizontal side, `≤ C log T · x^{σ₀}/T · width`),
`Sieve/PerronContourAssembly.lean` (`norm_vIntegral'_perron_sub_le`: the shift identity divided by
`2πi` with the rectangle replaced by its residue `x`).  What is left is substituting the parameters
and combining with the Perron formula — bookkeeping, no analytic input missing.

CARD 10 — the master inequality is Lean-closed: `Sieve/ChebyshevMasterInequality.lean`
(`norm_chebyshev_sub_halfInt_le`) bounds `|ψ(N) − (N+1/2)|` by the Perron truncation error plus the
three sides of the shifted rectangle, under RH, with every ingredient already proved.  Supporting:
`Sieve/PerronChebyshevIdentification.lean` (both sides of the Perron formula identified) and
`Sieve/LogDominatedByPower.lean`.  What is left is choosing `σ₁ = 1/2+ε/2`, `σ₀ = 1+1/log x`, `T = x`
and bounding the four terms — quantitative only.

DUPLICATION #6 CAUGHT AND REVERSED.  `Sieve/VonMangoldtRealSeries.lean` was written, built, wired,
then DELETED: the corpus already owns `RHTower.Sieve.tsum_vonMangoldt_rpow_neg_le` in
`Sieve/ChebyshevSeriesBound.lean` —
  `1 < d → d ≤ 2 → ∑'_n Λ(n)·n^{-d} ≤ 8/(d−1)²`
(delegating to `RHTower.tsum_vonMangoldt_div_rpow_le`), used at four other call sites.  It was an
exact NAME collision in the same namespace, which would have broken the umbrella.  Its `8/(d−1)²`
is weaker than the `1/(d−1) + A` I was proving but entirely adequate: at `d = 1 + ε/2` it gives
`32/ε²`.

RUNNING DUPLICATION LIST (all caught only AFTER writing the replacement):
  1. `sum_inv_le_sum_Icc` — `Sieve/DistinctReciprocalSum.lean`
  2. near-diagonal phase derivatives — `RHTower/NearDiagonalPhaseCurvature.lean`
  3. ζ strip growth — `RHTower/ZetaVerticalStripPolynomialBound.lean`
  4. module name `PerronRectangleResidue` — already taken at `RHTower/`
  5. `Real.log_le_rpow_div` — MATHLIB, used 63× in this corpus
  6. `tsum_vonMangoldt_rpow_neg_le` — `Sieve/ChebyshevSeriesBound.lean`
LESSON: for anything about ζ, Λ, Perron or the near-diagonal phase, grep the DECLARATION NAME in
`GaloisForLFunctions/` AND `#check` it against Mathlib BEFORE writing a line.

CARD 10 — the Perron error is now in closed form: `Sieve/VonMangoldtPerronMass.lean` and
`Sieve/PerronErrorTotalChebyshev.lean` (`perron_error_vonMangoldt_total_le`).  Taking
`σ₀ = 1 + ε/2` rather than the classical `1 + 1/log x` avoids the `x^{1/log x} = e` computation and
still gives a polylogarithmic error at `T = x`.

CARD 10 — the asymptotic layer is closed: `Sieve/PerronIntegrandContinuity.lean` (the continuity
hypothesis of the vertical-side bound) and `Sieve/PowerAbsorbsPolylog.lean`
(`rpow_mul_log_pow_isBigO : a < b → y^a (log y)^k =O[atTop] y^b`).  Every term of the master
inequality has the shape `x^a (log x)^k` with `a ≤ 1/2 + ε/2`, so the whole bound is `O(x^{1/2+ε})`.

CARD 10 — the transfer layer is closed: `Sieve/ShiftedPolylogTransfer.lean`.
`isBigO_shift_rpow_log : a < b → 0 ≤ b → (N+1/2)^a·(log(N+1/2))^k =O[atTop] N^b`, obtained by
composing `rpow_mul_log_pow_isBigO` with `N ↦ N + 1/2` and paying the constant `2^b` for the shift.
Every term of the master inequality is of exactly this shape with `a ≤ 1/2 + ε/2 < 1/2 + ε = b`,
so the final instantiation is now four applications of one lemma plus `IsBigO.add`.

## CARD 10 CLOSED — `square-aperture-von-mangoldt-correlation-energy` at stage 3 (2026-08-23)

Four new modules finished the chain (49 modules this session, all axiom-clean):

- `Sieve/ChebyshevErrorHalfIntegerBound.lean` — `exists_chebyshev_error_halfInt_bound`.
  The instantiation `σ₁ = 1/2 + ε/2`, `σ₀ = 1 + ε/2`, `T = N + 1/2` of the master inequality.
  Taking the truncation height EQUAL to the cutoff is what makes the Perron error and the
  horizontal sides both `x^{ε/2}` times a logarithm; the classical `σ₀ = 1 + 1/log x` is avoided.
- `Sieve/ChebyshevErrorPowerBound.lean` — `exists_chebyshevPsiReal_error_power_bound`:
  `RH → ∀ ε > 0, ∃ C > 0, ∀ t ≥ 1, |ψ(t) − t| ≤ C t^{1/2+ε}`.  Reusable:
  `exists_bound_of_isBigO_natRpow` upgrades an eventual `IsBigO` against `N^b` (`b ≥ 0`) to a
  bound valid for every `N ≥ 1`, by summing `|f n|` over the initial segment.
- `Sieve/DyadicWindowErrorUnderRH.lean` — the Abel identity with a power-law remainder.
- `Sieve/SquareWindowEnergyUnderRH.lean` —
  `riemannHypothesis_iff_squarePrimeWindowCorrelationEnergySubpower`.

Trap recorded: `abs_add` no longer exists (it is `abs_add_le`); `abs_sub a b : |a-b| ≤ |a|+|b|`
and `MeasureTheory.setIntegral_const` now produces `μ.real s • c`, so the rewrite chain is
`setIntegral_const, measureReal_def, Real.volume_Ioc, ENNReal.toReal_ofReal, smul_eq_mul`.
`integrableOn_const` takes two autoParams and is applied, not `.2`-ed.

REMAINING in `09-mobius-prime-sums`: card 12 (`kubalalika-parity-weighted-near-diagonal-tail`)
and card 11 (`regular-variation-weighted-steinhaus-ldp`).

## CARD 12 — the exponent-sum toolkit (2026-08-23)

Eight new modules; the card's three cited external theorems turn out NOT to be needed.
Recomputing the budget with the corpus's own tools (second-derivative test + Kuzmin--Landau +
Cauchy--Schwarz on either variable) gives `E_Λ(T) ≪ T^{15/16}L^C`, strictly stronger than the
card's `T^{53/54}`.  The reason is the pair of exact cancellations

    F'_{s₁} − F'_{s₂} = −(T/2π)(s₁−s₂)/((u+s₁)(u+s₂)),
    F''_{s₁} − F''_{s₂} = (T/2π)(s₁−s₂)(2u+s₁+s₂)/((u+s₁)²(u+s₂)²),

which say that the difference phase created by the type-II Cauchy--Schwarz is EXACTLY a
reciprocal phase again, at scale `T(s₁−s₂)` — the card only claims this asymptotically.

New modules (all in `RHTower/Sieve/`, all axiom-clean):
`CurvedPhaseBlockSum` (the abstract `CurvedPhase` chain), `DifferencePhaseCurvature`,
`DifferencePhaseKuzminLandau`, `BilinearCauchySchwarz`, `TypeIICorrelation`, `TypeIIEnergyBound`,
`TypeIBound`, `DivisorSquareMoment`, `DirichletConvolutionRearrange`.

Project card: `docs/drafts/pipeline/1-in-progress/kubalalika-weighted-tail-lean.md`.

## CARD 11 (`regular-variation-weighted-steinhaus-ldp`) — parts 3, 4, 5 CLOSED (2026-08-29)

Details in `docs/drafts/pipeline/1-in-progress/steinhaus-ldp-lean.md`.  Summary:

- **Part 4** (the small-coherence trichotomy) is complete.  The scaling identity
  `Λ_α(λ) = λ^{1/α}∫₀^{λ^{−1/α}} log I₀(w_α(u))du` removes `λ` from the integrand entirely, so the
  super-critical regime is "a truncated integral converges" and the critical one is a logarithmic
  Cesàro limit.  An abstract Legendre power law (`tendsto_rvRate_div_rpow`) covers the sub- and
  super-critical lines at once; the critical line needs its own tilt because of the slowly varying
  factor.
- **Part 5** (the high-coherence endpoint) is complete, and required proving the SHARP Bessel
  asymptotic `√x e^{−x}I₀(x) → 1/√(2π)` by Laplace's method (the corpus owned only two envelopes
  with non-matching constants).
- **S9**: Karamata's uniform convergence theorem, Potter's bound and the prime Karamata law
  `∑_{p≤X}(log p)p^{−α}L(p) ∼ X^{1−α}L(X)/(1−α)` are all Lean-proved.  This was a complete
  mathlib gap (there is no regular-variation theory in mathlib).

New modules (all axiom-clean, all wired):
  HTGeometry: `SteinhausScalingIdentity`, `IntegralLogCesaro`, `SteinhausSharpAsymptotic`,
    `SlowShiftUniform`, `SlowlyVarying`
  RHTower: `SteinhausRatePowerAsymptotic`, `SteinhausSuperConstant`, `SteinhausSupercriticalLimit`,
    `SteinhausCriticalCumulant`, `SteinhausCriticalRate`, `SteinhausEndpointCumulant`,
    `SteinhausEndpointRate`, `PrimeShellWeightedSum`, `PrimePowerSumBound`, `PrimeKaramataHead`,
    `PrimeKaramataShell`, `PrimeKaramataDarboux`, `PrimeKaramataBody`, `PrimeKaramata`

CARD 11 REMAINING: `(10)`/`(12)` (the normalized weights and the cumulant limit — both now
immediate consequences of the Karamata law plus the UCT and PNT), then S8, the LDP itself.  The
planar LDP reduces to a one-dimensional Cramér/Gärtner–Ellis statement for `R_X = |Y_X|` because the
law is rotation invariant.

CARD 12 (`kubalalika-parity-weighted-near-diagonal-tail`) — unchanged this session; see
`kubalalika-weighted-tail-lean.md`.  62 modules; what remains is the per-block multiplication, the
per-block orientation choice, the block-count summation and the instantiation at `T = u^16`.
