# Programme: formalize every stage-2 card in `2-fully-proven/leftovers` and `2-fully-proven/route TT`

- **ID:** stage2-leftovers-route-tt-formalization-programme-2026-10-16
- **Stage:** 1-in-progress (tracker; it is not itself a theorem card)
- **Goal:** every proven theorem on the eleven cards below gets an unconditional Lean proof (standard
  axioms only, no premises standing for analytic inputs), wired into its umbrella and audited with
  `lake env lean`; then each card moves to `3-formalized`.

## Rules in force
- One single-threaded Lean process at a time, foreground: `lake env lean -j 1 <file>` for audit;
  an olean only via `lake --old env lean -j 1 -o <olean> -i <ilean> <file>`, module by module.
  Never `lake build` (it runs parallel jobs; OOM). No umbrella or full builds; wire by `cat >>`.
- No computations; no heartbeat raising; scratch files in the session scratchpad.
- Search the corpus before writing any new declaration.

## Card ledger

| # | card | paper content | Lean state at start (2026-10-16) | next step |
|-|-|-|-|-|
| 1 | leftovers/finite-weil-adjacent-nodal-transport | adjacent coupling for every strictly increasing node family | canonical log nodes only | **DONE 2026-10-17** → 3-formalized (`FiniteWeilNodalAdjacentCoupling`, `FiniteWeilNodalMixtureTransport`) |
| 2 | leftovers/lee-yang-prime-pivot-dual-spectrum | spin partition, spectrum, converse chain, wall bound, signed coefficient | two-wall core | **DONE 2026-10-17** → 3-formalized (`LeeYangPrimePivotSpinPartitionSpectrum`) |
| 3 | route TT/tt-boundary-quadratic-norm-orientation | C78 norm/trace orientation at the boundary | `/tmp` drafts lost | **DONE 2026-10-17** → 3-formalized (`ThetaCuspRatioBoundaryNormOrientation`, `...SourceSlopeReal`, `...BoundaryNormInterior`) |
| 4 | route TT/route-tt-structural-theorems-2026-10-14 | T1–T7, L1–L14 | T4 corpus lemma, T1 at convexity rung, T7, L10, L12 §2, L13 | audit each item; T3, T2, L1, L3 … |
| 5 | leftovers/weil-cone-pole-duality-anatomy | (A) modular/Dirichlet fat cones, (B) factorization, (C) function fields | Krein–Milman reduction; Dirichlet symbol positivity (CANNOT-539) | Weil functionals for L(s,f), L(s,χ), curves |
| 6 | leftovers/twisted-minimum-principle | primal TMP construction (C1)–(C4), Steps 1–6 | TMP proved by dual route; Steps 1, 5 pieces | Dirichlet problem on modular strip, corner Martin kernel, Green identity |
| 7 | leftovers/smooth-stein-order-two-autonomous-ade-frequency-rank | Stein surface minimal hull dim ≤ 2 | none | CR/contact geometry, Levi-flat obstruction, Weinstein (Taubes) |
| 8 | leftovers/nonvacuous-independence-and-polarization-import-law | B′ clauses 1–3 | clauses 1–2 proved (`exists_finiteIndex_small_eigenvalue`) | clause 3: Selberg zeta zero at s_j |
| 9 | leftovers/verified-height-one-zero-turing-extension | RH through T₁ = T₀ + 111/256 | consumer theorems only | conflicts with "no computations" (needs Platt–Trudgian + Turing certificate) |
| 10 | leftovers/route-e-cofactor-amplified-e3-token-supply | E₃ token supply | elementary layers, MT mean-square bricks | Matomäki–Teräväinen Thm 1.2 |
| 11 | leftovers/route-e-forbidden-support-e3-stability | MT all-interval E₃ with forbidden support | elementary perturbation layer | Matomäki–Teräväinen Thm 1.2 |

## Log
- 2026-10-16 — ledger created after reading all eleven cards. Started card 1.
- 2026-10-17 — cards 1, 2, 3 formalized, audited (standard axioms), wired, moved to 3-formalized.
  Build rule after user correction: never `lake build` (parallel jobs → OOM); oleans only via
  `lake --old env lean -j 1 -o … -i …`, one module at a time; audits with `lake env lean -j 1`.
  The 25 C75–C77 upstream oleans card 3 needed were built that way.

## Card 4 (route-tt-structural-theorems) item ledger — 2026-10-17

Proven items (formalization targets):
- T1 cone-existence ladder: corpus has the convexity rung in Herglotz form
  (`exists_herglotz_trivialWeights_boosted`, boost `c(s+½)^θ`); TODO: parametric-μ₊ version and the
  Weil-cone form with density `Ω + C(1+|t|)^θ` (pointwise `Re(1+it)^θ ≤ (1+|t|)^θ` + modified bridge).
- T2 gap-weighted carrier (parametric θ₂): TODO (partial summation / continuation).
- T3 invariant forms: simple-zero core exists (`nonempty_positiveInvariantForm_iff`,
  `eq_conj_of_invariant_ne_zero`); TODO: jet components for multiple zeros (correction) and the
  statement over the actual zero set of Ξ.
- T4 depth blindness: TODO corollary of `integral_horizontal_shift_of_upper_inv_one_add_sq_decay`
  (both signs of `β - ½`).
- T5 Ruelle zeta quasi-RH (Ruelle–Pollicott), T6 analytic Ruelle zeta zero-free (nuclear
  Fredholm determinants): TODO, large infrastructure.
- T7: DONE in corpus (MUST-1442).
- L1 Maass–Selberg resonance identity; L2 E* Fourier expansion + Hecke factorization
  `2ζ(2s)E(i,s) = 4ζ(s)L(s,χ₋₄)`: TODO.
- L3 archimedean decomposition, completely monotone kernel, PD positivity, anomaly window, Selberg
  Plancherel density: TODO (check `weilArchRe_eq_levy_pole`).
- L5 (i) `ξ(0) = ξ(1) = ½`; (ii) positive measure `2cosh(x/2)+ε cos(γ₁x)` argument: TODO.
- L6 pencil obstruction; L7 Davenport–Heilbronn (cited theorem, large): TODO.
- L10 twin rigidity (paper) + unconditional corollary: TODO; [L] parts DONE (`weilPositiveDegree_iff`,
  `forall_re_weilDegreePoleFunctional_nonneg_iff`).
- L12 §1 second clause (no compactly supported test is Ξ²-divisible), §3 exact archimedean form,
  §4 keystone reduction: TODO; §2 DONE in corpus.
- L13: DONE in corpus (MUST-1458/1463).
- L14 1 (pole-negative violators), 2 (dilation continuity, PBAP(1) ⟹ PBAP(1/k), PBAP(½) theta
  datum), 3 (Markov + pole, sinh-capacity criterion), 4 (cores = wandering vectors, Farkas dual),
  5 (`e^{|Ω(0)|} = 8π e^{γ+π/2}`), 6 (`Ω ≥ Ω(0)`): TODO.
Not proven theorems on the card (no formalization obligation, recorded as such): the
"structural laws for the PBAP lane" addendum (marked heuristic); L4, L8, L9 (named heuristic
obstructions); L11 index law and L12 §1 first clause (paper with an explicitly stated unproved
C^k-approximation gap); the conjectured quasi-RH ladder in L14.2; core existence (open) in L14.4.
- 2026-10-17 card 4 progress: T4 DONE (`TranslationAveragedDensityDepthBlindness`:
  `integral_translationAveraged_depth_blind`, both shift directions). `ArchimedeanAnomalyConstantLaws`:
  L5(i) `XiC_pole_points`; L14.5 `gammaBracket_zero_eq`, `exp_abs_gammaBracket_zero`; L14.6
  `gammaBracket_zero_le`/`gammaBracket_mono`; L3 `weilArchRe_eq_autocorrelation_form`,
  `exp_half_div_sinh_eq`, `hasSum_archLevyDensity`, `completelyMonotone_archLevyDensity`,
  `plancherelDensity_nonneg`; L14.1 `weilArch_sub_pole_ge`, `pole_lt_of_violation`,
  `weilArchRe_nonneg_of_pole_heavy` (exact constant `|A(0)| = γ+π/2+log 8π`). Remaining in L3: the
  anomaly window `A < 0 ⟺ |t| < t₀`, `t₀ > 2π` (needs `Re ψ(¼+iπ) < log π`, margin ≈ 1.6e-3).
- 2026-10-17 card 4: T3 with the multiplicity correction DONE (`ZeroAlgebraJetInvariantForms`):
  jet model of `O/(Ξ)` with `M_q` = character × unipotent; support law
  `invariantForm_eq_zero_of_ne_conj` (via `exists_rat_exp_ne_one`, `2^a ≠ 3^b`); PSD radical
  `invariantForm_higherJet_radical`; `posDef_invariantForm_real_simple`; `valueForm`
  (best-possible PSD form); `exists_posDef_invariantForm_XiC_iff` (PD invariant form ⟺ RH ∧ simple
  zeros). Standard axioms; wired.
- 2026-10-17 card 4: L6 DONE (`HermitianPencilEulerFactorObstruction`: real roots of `det(B+tH)`,
  `riemannHypothesis_of_XiC_eq_det_pencil`, resolvent trace continuous off ℝ,
  `not_pencilResolventTrace_eq_eulerFactor`). Standard axioms; wired.
- 2026-10-17 card 4: T2 DONE (`PrimeGapDirichletContinuation`, namespace `RHTower.PrimeGapDirichlet`):
  `GapMomentBound θ` (Σ_{p_k≤X} g_k² ≤ C X^{1+θ}); `GapMomentBound.nonneg`;
  `gapMomentBound_of_eventually_gap_le`, `gapMomentBound_one` (Bertrand), `gapMomentBound_hoheisel`
  (θ = 71/100, corpus Hoheisel supply); Abel summation `summable_gap_sq_mul_rpow`;
  `exists_gapDirichlet_continuation` (D = 1/(s−1) + G, G holomorphic on Re s > θ),
  `differentiableOn_gapDirichletCont`, `tendsto_sub_one_mul_gapDirichletCont` (residue 1, θ < 1),
  `norm_gapDirichletCont_critical_le` (θ < ½ ⟹ |D(½+it)| ≤ C(1+|t|)),
  `gapDirichlet_continuation_hoheisel` (unconditional instance). Standard axioms; wired.
  Recorded: Heath-Brown's admissibility of 5/18+ε is a cited literature input, not proved on the card;
  the card's "≍ |t|" lower half has no paper proof (only ≪ is a theorem).
- 2026-10-17 card 4: L14.3 DONE (`WeilMarkovPoleCapacity`, namespace `RHTower.WeilMarkovPole`):
  `weil_eq_markovForm_add_pole` (W = M_N + ½⟨c,g⟩² − ½⟨s,g⟩², M_N = V_N‖g‖² + Lévy jumps + prime
  jumps), `markovForm_abs_le` (Markov/normal contraction), `pole_le_pole_abs` (pole anti-Markov),
  `weil_nonneg_iff_sinhCapacity`, `riemannHypothesis_iff_sinhCapacity` (RH ⟺ sinh-capacity bound at
  every level), `forall_sq_dotProduct_le_iff` (Gram form: bound ⟺ ⟨s,Q⁻¹s⟩ ≤ 2). Standard axioms; wired.
- 2026-10-17 card 4: L14.2 core DONE (`WeilNodeDilationFamily`, namespace `RHTower.NodeDilation`):
  `PrimeBlindPositiveDilated t`; dilation formula `weilArchRe_comp_div`, continuity
  `tendsto_weilArchRe_comp_div`; `riemannHypothesis_of_tendsto` / `riemannHypothesis_iff_exists_tendsto`
  (dilation continuity theorem); `primeBlindPositiveDilated_one_div_of_one/_of_riemannHypothesis`
  (PBAP(1) ⟹ PBAP(1/k)); `primeBlindPositiveDilated_iff` (PBAP(t) = blind positivity of the dilated
  datum A_t at log n); `gammaBracket_two_mul` (Ω(2r) = log 2 + ½(D_{−1/4}+D_{3/4})),
  `Gammaℝ_sub_quarter_mul` (Γℝ(s−¼)Γℝ(s+¾) = Γℂ(s−¼)), `primeBlindPositiveDilated_half_iff`.
  Standard axioms; wired. Remaining in L14.2: criticality law (sign of S) for the null ray G₀.
- 2026-10-17 card 4: L12 §1 second clause DONE (`CompactTestXiDivisibilityObstruction`:
  `eq_zero_of_paperFT_eq_zero_of_XiC_eq_zero` — a compactly supported test whose transform vanishes
  at every real zero of Ξ is 0; `not_exists_paperFT_eq_XiC_mul`, `not_exists_paperFT_eq_XiC_sq_mul`;
  via corpus `exists_simpleCritical_nonzero_of_exponentialType`). L12 §3 DONE
  (`WeilArchimedeanExactForm`: `weilArchRe_eq_exactForm`, `integral_autocorr_mul_cosh`). L5(ii) DONE
  (`WeilLinearEffectivityObstruction`: `weightDensity_pos`, `pairing_eq`,
  `pairing_eq_zero_of_isRepairedPrincipal`, `exists_pairing_pos_and_neg`). `WeilMarkovPoleCapacity`
  now reuses `ArchimedeanAnomaly.integral_sub_shift_sq` (duplicate removed). All standard axioms; wired.
- 2026-10-17 card 4: L12 §4 computational part DONE (`CoreNullTestPoleSign`, namespace
  `RHTower.CoreNullPole`): `cosDilationCertMultiplier_one` (R_f(1) = −2(∫f log y)(∫f/y)),
  `coreNullPole_eq` (P = 2ξ(1)²R_f(1) = −(∫f log y)(∫f/y)), sign trichotomy
  `coreNullPole_neg_iff` / `_eq_zero_iff` / `_pos_iff` (odd/primitive/even cores). The "⟹" half of the
  keystone equivalence (every pole-negative null test in the witness class comes from a core) rests on
  the row-415 null-face rigidity, i.e. on L12 §1 first clause, which the card itself marks as having an
  unproved C^k-approximation gap: not a dependency-closed theorem, recorded as such.
- 2026-10-17 card 4: L14.4 resonance law + L3 window existence DONE (`ArchimedeanResonanceRange`,
  namespace `RHTower.ArchimedeanResonance`): `exists_anomaly_window` (Ω<0 ⟺ |τ|<t₀, 0<t₀≤20),
  `exists_gammaBracket_eq_neg_log_iff` (stationary phase Ω(τ) = −log n solvable ⟺ n ≤ 8πe^{γ+π/2}),
  `neg_log_two_lt_gammaBracket_two_pi`, `abs_lt_two_pi_of_gammaBracket_eq_neg_log` (resonances lie in
  |τ|<2π). Standard axioms; wired. Remaining in L3: t₀ > 2π (Re ψ(¼+iπ) < log π, margin ~1e-3) needs
  a sharp complex digamma bound (Binet remainder) — next infrastructure target.
- 2026-10-17 card 4: L14.4 bounded separators DONE in rigorous form (`KelvinChirpSeparatorBound`,
  namespace `RHTower.KelvinSeparator`): `exp_le_of_posDefOn` / `exp_le_of_abs_le` — a continuous
  1-periodic F ≢ 0 with H(v) = e^{v/2}F(e^v)+e^{−v/2}F(e^{−v}) positive definite on [−L,L] forces
  e^L ≤ 4+2√2 ≈ 6.83. The card's "≈ 5.83 = (1+√2)²" assumes the maximum of |F| is reached exactly at
  v = L (heuristic); the rigorous constant is 1+(1+√2)² = 4+2√2. Standard axioms; wired.
  Remaining L14.4: (a) NB-wandering reformulation (Mellin–Plancherel for F = Σ f(k·)), (b) Farkas
  dual (one direction exact per source), "dimension count threshold 2" = heuristic (not a theorem).
- 2026-10-17 card 4: L3 anomaly window DONE. New infrastructure `DigammaBinetFourthOrder`
  (`norm_digamma_sub_stirling_le`: |ψ(w) − log w + 1/(2w) + 1/(12w²)| ≤ 1/(120 (Re w)⁴) on Re w > 0,
  via Gauss + Frullani + Binet kernel bounds 0 ≤ ρ(t) ≤ t³/720 from hyperbolic inequalities).
  `AnomalyWindowTwoPi`: `gammaBracket_two_pi_neg` (Re ψ(¼+iπ) < log π), `gammaBracket_two_pi_add_pos`,
  `anomaly_window_two_pi` (Ω<0 ⟺ |τ|<t₀ with 2π < t₀ ≤ 2π + 1/50). Certified Lean bounds only
  (no external computation). Standard axioms; wired. L3 now complete (decomposition, kernel, PD
  positivity, window, Selberg Plancherel density).
- 2026-10-17 card 4: T1 DONE in full Weil-cone form (`TrivialWeightBoostedWeilCone`, namespace
  `RHTower.TrivialWeightCone`; infrastructure `LineShiftHalfPlaneHolomorphic`: two-line residue
  identity and critical-line shift for half-plane holomorphic multipliers). `ZetaGrowthExponent μ`
  (|ζ(σ+it)| ≤ K(1+|t|)^μ on σ ≥ ½, |t| ≥ 1), `.nonneg`; parametric producer
  `exists_herglotz_trivialWeights_boosted_of_growth`; `weilCone_of_boostedProducer`;
  `trivialWeights_boostedWeilCone` (∀ admissible μ, ∀ θ > μ, ∃ C > 0: 0 ≤ Re W_{λ≡1}(f⋆f̃) +
  (1/2π)∫|f̂|²C(1+|r|)^θ for every C²_c f with convergent density pairing) and the unconditional
  `trivialWeights_boostedWeilCone_of_quarter_lt` (θ > ¼). Standard axioms; wired.
- 2026-10-17 card 4: L14.1 (iii) DONE (`BlindMomentRegion`): `momentRegion` K = {(P/N, A_∞/N)} over
  nonnegative blind combinations; `convex_momentRegion`; `momentRegion_subset` (A_∞/N ≥ Ω(0), via
  Ω ≥ Ω(0) and Plancherel); `primeBlindPositive_iff_momentRegion` / `riemannHypothesis_iff_momentRegion`
  (PBAP ⟺ RH ⟺ K above q = −p); `closure_momentRegion_of_riemannHypothesis`; null edge approached
  from both pole signs under RH (`exists_mem_momentRegion_pole_neg/pos_of_riemannHypothesis`). The
  "(P₀,−P₀) = image of G₀" clause lives in the decay class (G₀ is not compactly supported); the
  supporting-line reformulation is the above with the null point on the line. Standard axioms; wired.
- 2026-10-17 card 5: (A) and (B) DONE (`WeilConePoleDualityAnatomy`, namespace
  `RHTower.PoleDualityAnatomy`): `ArchDatum`, `weilFunctional`, `InWeilCone`;
  `modularDatum_zero_mem_cone` (weight 2m ≥ 14, via ψ(7) > log 2π from the Binet bound),
  `dirichletDatum_odd_zero_mem_cone` (q ≥ 10), `dirichletDatum_even_zero_mem_cone` (q ≥ 216, using the
  corpus γ < 0.577216), `eq_zero_of_cone_pinned`; `zetaDatum`/`weilFunctional_zetaDatum` (agrees with the
  corpus functional), `weilFunctional_mulDatum`, `vonMangoldt_mem_cone_mulDatum` (RH ⟹ Λ ∈ cone(ζL′)),
  `not_riemannHypothesis_of_pinned` and the odd-Dirichlet instance. Standard axioms; wired.
  (C) needs the explicit formula for curves over F_q and Weil's RH for curves (positivity of
  W_{C′,Λ_{C′}}): not in the corpus or mathlib — infrastructure project still to be built.
- 2026-10-17 card 4: L14.4 (a) NB-wandering reformulation DONE (`BlindCoreWanderingNymanBeurling`,
  namespace `RHTower.BlindCoreWandering`): `nbSum` F = Σ_{k≥1} f(k·), `abs_nbSum_le` (|F| ≤ ½∫|f'| by
  first-order Euler–Maclaurin), `mellin_nbSum_of_one_lt` / `mellin_nbSum_eq` (𝓜F = ζ𝓜f on Re s > 0,
  Im s ≠ 0, identity theorem), `integral_norm_mellin_half_sq` (Mellin–Plancherel on Re s = ½ for bounded
  G vanishing beyond β), `integral_mul_dilate_eq` (polarized), `integral_nbSum_mul_nbSum_dilate`
  (∫F(x)F(nx)dx = Σ d(m)Ψ_f(mn)), `eq_zero_of_tsum_divisorCard_eq_zero` (divisor-transform injectivity via
  Σ_{m≥2}m⁻² < 1), `blind_iff_wandering`. Standard axioms; wired.
- 2026-10-17 card 4: L14.4 (b) Farkas separation DONE in its proven direction (`BlindCoreFarkasSeparation`,
  namespace `RHTower.BlindCoreFarkas`): `kelvinChirp`, `kelvinChirp_zero` (= pole kernel 2cosh(v/2)),
  `logAutocorr` b_f(v) = e^{v/2}A_f(e^v), `autocorr_logPull` (b_f = autocorrelation of √α e^{u/2}f(αe^u),
  supported in [0, L]), `integral_kelvinChirp_mul_logAutocorr` (⟨b_f, φ_n⟩ = Ψ_f(n)), `IsBlindCore`,
  `coreAnnihilator` (closed for pointwise convergence on C([−L,L]) ⊇ weak-* closure),
  `closure_span_le_coreAnnihilator`, `kernelFunctional_sum_mem_span`, `StrictPD`,
  `eq_zero_of_mem_closure_span_of_strictPD`, `eq_zero_of_kernel_strictPD`. Standard axioms; wired.
  The converse (no cores ⟹ a strictly PD separator exists) is NOT a proven theorem: the source row 447
  records it as "exact one direction; Farkas closure caveat for the other" (a sum of autocorrelations in
  the annihilator is only an L² core by Boas–Kac, and algebraic separation from a non-closed cone need not
  be strict). Not an obligation of the card; recorded on the card.
- 2026-10-17 card 4: L1 DONE. Corpus had the resonance identity for Im ρ > 0
  (`heckeHermitianMoment_resonant`, `heckeHermitianMoment_resonant_re`, Maass–Selberg norm
  `integral_norm_sq_resonantState`); new `EisensteinHeckeResonanceAllZeros` adds the conjugate half and the
  card's every-zero statement: `heckeHermitianMoment_conj`, `heckeHermitianMoment_resonantZero`
  (⟨T_pΛ^Y E_u, Λ^Y E_u⟩ = (p^u + p^ū)‖Λ(ρ−1)‖²Y^{1−Re ρ}/(1−Re ρ) for every zero ρ off the real axis,
  u = ρ/2 − ½, Y ≥ p), `heckeHermitianMoment_resonantZero_re` (real). Standard axioms; wired.
- 2026-10-17 card 4: L2 DONE. Corpus: Fourier expansion of the completed Eisenstein series
  (`d4BM_actualCompletedPoincare_eq_canonicalCuspLeg`, Re s > 1; the canonical cusp model defines E* for
  all s) and the ζ-free tail entire in s (`differentiableAt_cuspTailPart`, every u₀). New:
  `GaussianTwoSquaresCount` (`card_normSet`: Jacobi r₂(n) = 4Σ_{d|n}χ₄(d), via the prime recursion
  F(pm) = (1+χ₄p)F(m) − χ₄(p)F(m/p) in ℤ[i]) and `EisensteinHeckeFactorizationAtI` (`latticeSum_eq`
  Σ(m²+n²)^{-s} = 4ζL(χ₋₄); `latticeSum_eq_zeta_mul_primitive`; `two_mul_zeta_mul_eisenstein_I`
  2ζ(2s)E(i,s) = 4ζ(s)L(s,χ₋₄); `eisensteinLineModel_I_eq` E*(i,s) = 2Γ_ℝ(2s)ζ(s)L(s,χ₋₄) on Re s > 0,
  Im s > 0; `eisensteinLineModel_I_eq_zero_iff`; `re_lt_half_of_lambda_two_mul_eq_zero` one-sidedness).
  Standard axioms; wired. The "identities hold uniformly in s / no identity locates zeros" bullet is an
  interpretive meta-statement (no theorem content beyond the above).
- 2026-10-17 card 4: L10 DONE in full. Infrastructure: `WeilLineIntegralAnyAbscissa` (Weil functional as a
  line integral on any line Re s = c ≥ 3/2 of absolute convergence), `HerglotzWeilBridgeAnyLine`
  (`weilPositiveFull_of_herglotz_abscissa`: Herglotz on Re s > ½ + agreement beyond any abscissa σ₂ ⟹
  Weil positivity), `CompletionOrderOneEnvelopeAnyLine` (`orderOneEnvelope_of_finiteOrder_abscissa`).
  `TwinRigidityZetaPower` (namespace `RHTower.TwinRigidity`): Dirichlet inverse `dinv`, `lamT` (coefficients
  of −T′/T), `lseries_identities`, `TwinDatum`, `re_logDeriv_nonneg` (zero-pair Hadamard sum),
  `eq_zetaPow_of_lamT`, **`twin_rigidity`** (all zeros of (s(s−1)Γ_ℝ)^d T critical ⟹ RH ∧ T = ζ^d).
  `TwinRigidityOffLineZero`: **`exists_zero_offLine`** (unconditional corollary for every degree d ≥ 1: a
  real FE-invariant twin ζ^d + E, E = Σ e(n)n^{−s} ≢ 0 with e(1) = 0 and Γ_ℝ^d E entire of finite order,
  has a zero of (2ξ)^d + (s(s−1))^d Γ_ℝ^d E off Re s = ½; the card states d = 3). `TwinRigidityPoleOrder`:
  `orderOneEnvelope_pole`, `weilPoleWeightFunctional_eq_line`, `weilPoleWeight_nonneg_of_herglotz_abscissa`,
  `PoleTwinDatum`, **`pole_order_rigidity`** (pole order κ, degree d ≥ 1, all zeros critical ⟹ κ = d ∧ RH ∧
  T = ζ^d: the full κ<d / κ=d / κ>d classification). Standard axioms; wired.
- 2026-10-17 card 4: L14.2 criticality law DONE. `NullRayDilationSpectral` (namespace `RHTower.NullRayDilation`):
  `dil` (Φ_t(z) = tΦ(tz)), `stripTest_dil` (stripTest Φ_t = stripTest Φ(·/t)), `crossCorr_stripTest_dil`,
  `NullFamily` (Ξ-divisible strip family with jointly blind autocorrelation), `nullRay` G₀, `nullDensity` R,
  `nullRay_eq_stripTest` (G₀ = stripTest R), `stripDecay_nullDensity`, `hasDerivAt_nullRay`,
  `exists_abs_deriv_nullRay_le` (|G₀′(y)| ≤ K e^{−9|y|/8}). `NullRayDilationCriticality`: `dilatedEnergy`
  a(t) = A(G₀(·/t)) (`nullRay_div_eq`), `nullRaySlope` S = Σ Λ(n)n^{−1/2} log n G₀′(log n),
  `dilatedEnergy_eq` (a = zero side + prime side via the decay-class explicit formula),
  `norm_dil_le_of_zero` (Cauchy + mean value: (1+|γ|)|tΦ(tγ)| ≤ |t−1|BC at zeros), `hasDerivAt_zeroPart`
  (Z′(1) = 0), `hasDerivAt_primePart` (P′(1) = −2S), `dilatedEnergy_one`, **`hasDerivAt_dilatedEnergy`**
  (a′(1) = −2S), **`dilatedEnergy_neg`** (S ≠ 0 ⟹ a(t) < 0 on the side (t−1)S > 0),
  `exists_nullFamily_xiShiftedGamma` (the TMP family is a null family), `twistedArc_nullRay_criticality`.
  Standard axioms; wired. Recorded: the clause "pole-negative near-null tests break every t > 1" is the
  source row 438(b) approximation A(g(·/t)) ≈ |P|(1 − t e^{(t−1)L/2}) for the c*-family "given the
  β-Herglotz bridge" (W_β-positivity ⟹ Herglotz at β ≠ 1, unproved; row 424 (iii) states it as an
  assumption): heuristic, not a theorem.
- 2026-10-17 card 4: T6 DONE (programme card `t6-nuclear-ruelle-zeta-lean-programme-2026-10-17`, now in
  3-formalized). HTGeometry: `DiscHolomorphicFixedPoint` (Schwarz–Pick contraction, unique attracting fixed
  point), `DiscCoefficientExpansion` (Cauchy coefficients, expansion, substitution), `WeightedCompositionTrace`
  (residue trace formula w(p)/(1−Φ'(p))), `GeometricDecayMatrixPowers`, `GeometricDecayFredholmDeterminant`
  (entire det(1−λM) for |M_ij| ≤ Cη^{i+j}, holomorphic in parameters, = exp(−Σ λⁿTr Mⁿ/n), continued to λ=1),
  `AnalyticMarkovSystem` (inverse-branch data of a real-analytic orientation-preserving expanding Markov map
  with nuclear transfer operators; words, composites, real periodic points, chain rule),
  `AnalyticMarkovTransferMatrix` (matrix of L_s, decay, entireness, path expansion of powers,
  `itrace_mat` trace formula). RHTower `RuelleZetaNuclearZeroFree`: **`ruelleZeta_continuation`**
  (D(s)=det(1−L_s) entire, ζ_R(s)D(s)=D(s+1) on Re s>σ₀, D(s+1)≠0 on Re s>σ₀−1: zero-free on Re s>0 for
  entropy 1) and **`not_riemannZeta_eq_ruelleZeta`** (ζ is not such a Ruelle zeta; uses the corpus Hardy
  zero `exists_riemannZeta_zero_re_half`). Standard axioms; wired.
- 2026-10-17 status and order of the remaining work (each item below is a standalone formalization project):
  1. card 4 T5 — Ruelle–Pollicott for suspension flows over mixing SFTs with Hölder roof (transfer operators on
     F_θ, Lasota–Yorke, quasi-compactness, flat-trace asymptotics, nonvanishing of ζ_R on Re s > 1 − ε).
  2. card 4 L7 — Davenport–Heilbronn for Epstein zeta functions with class number > 1 (imaginary quadratic orders,
     class group characters and their L-functions, primes in ideal classes, Kronecker, Rouché).
  3. card 6 — the primal TMP construction (Dirichlet problem on the cusped modular strip, corner Martin kernel,
     Green/jet identity, stream-function regularity); the TMP theorem itself is already formalized (dual route).
  4. card 8 clause 3 — Selberg zeta function and trace formula with scattering for the cofinite noncongruence Γ_N.
  5. cards 10/11 — Matomäki–Teräväinen Theorem 1.2 (all-interval E₃), including its Kuznetsov-level inputs.
  6. card 5 (C) — Weil's Riemann hypothesis for curves over F_q (Riemann–Roch, Bombieri–Stepanov) and the
     function-field explicit formula.
  7. card 7 — needs Taubes's 3-dimensional Weinstein theorem (Seiberg–Witten theory) for the contact case.
  Card 9 is blocked by the session rule "no computations": its headline theorem is a certified numerical
  verification (Platt–Trudgian prefix + Turing count at height 3·10¹²); its mathematical content is already
  Lean-closed (`rhVerifiedThrough_amplify_of_fiber_ncard_le_one`). Needs a user decision.
