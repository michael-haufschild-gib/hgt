# Review-2110 §2.1 just-work items, formalized unconditionally

- **ID:** `review-2110-just-work-lean-2026-10-21`
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) programme
- **Source:** `docs/reports/review-2110/hard-obstacles-summary.md` §2.1 (eleven rows)
- **Statement:** every §2.1 row closed by an unconditional Lean theorem (no premises, no axioms, no
  numerical computation), compiled with `lake env lean`, wired into its umbrella.

## Rules in force
Unconditional statements only; one foreground Lean process; `lake env lean <file>` for the audit,
`lake --old env lean -j 1 -o … -i …` for oleans; wire every finished module (umbrella edits by
append/in-place insert only, never rewrite); no full or umbrella builds; no heartbeat raises; crisp
mathematical comments; no git; corpus search tool first; clean scratch files.

Several lanes are active in parallel (WP3 all-profile window, AIP odd window, SRT explicit lag,
BVI WP4, THIM WP5, BiScale WP6). Items those lanes are pushing are tracked here and closed when
their module lands; this card does not edit their files.

## Items and deliverables

| # | §2.1 row | Concrete Lean deliverable | Owner | Status |
|---|---|---|---|---|
| 1 | a1 wiring | all nine modules imported by their umbrellas; WideNearTopZone docstring complete | lanes / me | 8/9 wired in working tree (APole pending, THIM lane compiling it) |
| 2 | all-profile window `3/10 → log 2/2` | `Ẑ(F) ≥ c∫F²` on `[−log2/2, log2/2]`-limit window, all profiles | WP3 lane | open (lane probing `0.311`) |
| 3 | odd window `353/1000 → 0.355 → 0.375` | capstone at `356/1000`; further odd windows to the inner-edge limit | AIP lane | `356/1000` module in working tree, wired |
| 4 | ACT shift-averaged converse | theorem settling whether `∫₀^∞ Q(m_a u) da ≥ 0 ∀u` implies RH | me | open |
| 5 | RW/SZ/CHMD common core on completed norms | equality or explicit separation of the completed source norms | me | open |
| 6 | Beurling selectivity audit | each positivity theorem restated for general prime data; Beurling/Liouville verdicts | me | open |
| 7 | SRT constants | aperture beyond `1/100`; explicit `V₀(w,η,δ₀)`, `V(a,σ)` | SRT lane / me | open |
| 8 | APT/EWU constants | explicit `M₀`, slopes, offsets, range of the cell kernel `R` | me | open |
| 9 | BVI/THIM finite laws | (i) defect sign at every `N ≥ 2`; (ii) least long-window threshold; (iii) sandwich constant; (iv) large sieve `N + Q² − 1`; (v) Vasyunin error below `O(p+q)` | me | open |
| 10 | AIP finite items | collar ratio second-order term; quarter-point set `14 ≤ n ≤ 22`; bump bridge | AIP lane / me | open |
| 11 | finite checks | PA Hausdorff block thresholds; HCF/TH fixed-rank Hankel; TT/TH inner chamber at bounded action; XN disc; RB finite range; JAS budget constant | me | open |

## Log
- 2026-10-21 — card created; ownership surveyed from running processes and lane cards.
- 2026-10-21 — **9(iv) closed** (factor two in the log-free large sieve). Lean, axioms standard, wired:
  `HTGeometry/MontgomeryVaughanHilbertInequality` (`norm_sum_mul_conj_hilbertDifferenceKernel_le`:
  `|Σ_{r≠s} z_r z̄_s/(λ_r−λ_s)| ≤ (π/δ)Σ|z_r|²`, eigenvector identity + `κ_s ≤ π²/(3δ²)`),
  `HTGeometry/MontgomeryVaughanCosecantInequality` (`norm_sum_mul_conj_div_sin_le`, constant `δ⁻¹`,
  Fejér means of alternating copies), `BezoutValuationIncidence/LargeSieveWithTheMontgomeryVaughanConstant`
  (dual `K + δ⁻¹`; Farey/roots-of-unity separation `1/(Q(Q−1))`; Farey, multiplicative, Montgomery
  sieve and card bound with `N + Q² − 1`), `BezoutValuationIncidence/ArithmeticLargeSieveWithTheMontgomeryVaughanConstant`
  (squarefree arithmetic large sieve `N + Q² − 1`). BVI README updated.
- 2026-10-21 — **row 1 complete** in the working tree: all nine listed modules umbrella-imported
  (APole wired by the THIM lane; WideNearTopZone docstring finished). Committing is the user's (no git).
- 2026-10-21 — **9(ii) already closed** by THIM `QuadraticLongWindowThreshold` (committed): Möbius
  defect `≤ 0` for `M ≥ 10N² + 8N` at every `N ≥ 2`, damped `10N² + 72N^{1+2ε}`; eventually `< 0` for
  all `M ≥ 2N`. The review row listing it as open was stale.
- 2026-10-21 — **row 7, aperture part**: `SquareRootThreshold/ZetaWeilPositivityThroughApertureThreeTenths`
  (`zetaZeroConfig_re_W_ge_of_window` transfer lemma; `Re W_ζ(f,f) ≥ (1/5000)∫|f|²` on `[−3/10,3/10]`;
  windowed positivity at `3/10`), axioms standard, wired; SRT README updated. Further toward
  `(log 2)/2` is row 2 (WP3 lane) and transfers through the same lemma.
- 2026-10-21 — **row 10, quarter-point set closed**: `ArithmeticIncidencePositivity/QuarterPointClassification`
  (`antiDiagonalLevel_le_quarter_iff_mem`: quarter paid ⟺ `n ∈ {10,12}` or `n ≥ 14, n ≠ 17`, all `n ≥ 2`;
  `unpaidSet_eq_of_le_midpoint`: midpoint paid ⟹ unpaid set = two axis intervals with exact end `c`;
  `midpoint_paid_and_quarter_unpaid_iff`: exactly `n ∈ {6, 17}`; `unpaidSet_level_eq_of_quarter_unpaid`).
  Axioms standard, wired; AIP README item 3′ updated. Remaining in row 10: collar ratio second-order
  term, bump bridge.
- 2026-10-21 — **row 10, collar ratio closed**: `ArithmeticIncidencePositivity/CollarEndSecondOrderLaw`
  (`collarEnd_second_order`: collar = `(0,c) ∪ (s−c,s)`, `ℓ ≤ c ≤ 2ℓ`, `|c − ℓ − (coth(s/2)/2)ℓ²| ≤ 8ℓ³`
  for `s ≥ 4 log 2`; `half_coth_mul_collarInnerEnd`: coefficient `= e^{−s}/(1−e^{−s})³` exactly;
  `collarEnd_ratio`: `|c/ℓ − 1 − e^{−s}/(1−e^{−s})³| ≤ 37e^{−2s}`). Axioms standard, wired, README item 3.
  Remaining in row 10: bump bridge.
- 2026-10-21 — **row 10, bump bridge closed (prime part)**: `ArithmeticIncidencePositivity/BumpBridgeOfThePrimeJumpEnergy`
  (`tendsto_gaugePrimeJump_bumpProfile`: centre form for any finite centre set, gauge `|M| ≤ Ce^{−|x|}`;
  `tendsto_gaugePrimeJump_latticeBumpProfile_netAtom`: lattice `{± log a}`, odd gauge,
  `∫β²(2Σc_a²M𝒢 − 4Σ_{a<b}c_ac_bMM·netAtom − 2Σc_a²M²·netAtom(a,a))`; the README formula lacked the
  crossing-pair term `(−log a, log a)`). Axioms standard, wired, README item 2 updated. Follow-up (not
  in the §2.1 row): archimedean self-energy asymptotic `≍ w log(1/w)`. **Row 10 complete.**
- 2026-10-21 — **9(v) closed** (Vasyunin error): `BezoutValuationIncidence/ExactOrderOfTheVasyuninReciprocityDefect`
  (`residueDifferenceEnergy_ge_gap`: `E(p,q) ≥ (q−p)/8`; `residueDifferenceEnergy_exact_order` /
  `vasyunin_reciprocity_exact_order`: `h(1+log⁺(p/h))/18 ≤ π(V(q,p)+V(p,q)) + (q−p)log(q/p) ≤ 12h(1+log⁺(p/h))`,
  `h = q − p`). The defect is below `O(p+q)` iff `h = o(p)`; for moduli of different sizes no bound
  below `O(p+q)` holds. Axioms standard, wired, BVI README updated.
- 2026-10-21 — **9(iii) sharpened** (window sandwich constant): `abs_sum_window_norm_sq_sub_le` (two-sided MV
  window bound `|Σ_W − K Σ|b|²| ≤ δ⁻¹ Σ|b|²`), `abs_window_rootsOfUnity_sub_le` (`Q(Q−1)` over roots of
  unity), `BezoutValuationIncidence/WindowSandwichWithTheMontgomeryVaughanConstant`
  (`isWindowSandwichConstant_mv`: `N(N−1)` admissible; `windowSandwichConstant_between`: optimal
  constant in `[Φ(N)−2, N(N−1)]`, previously `[N²/8 + N − (N/2)H_N − 2, 2N²−1]`). The exact value is
  arithmetic (the length-two window already reads `Σ_{q≤N} μ(q)`); recorded as open in the README.
  Correction: the "length-two window reads `Σ μ(q)`" remark holds for general coefficients on the
  response roots, not proved for Selberg (class-constant) rows; it is not in the README.
- 2026-10-21 — **9(i) status**: at every `N ≥ 2` the Möbius defect is `≤ 0` for `M + 1 < 11(N+1)`
  (ratio ladder) and for `M ≥ 10N² + 8N` (THIM, both [L]); the window `11N + 10 ≤ M < 10N² + 8N` is
  covered only eventually in `N` (ineffective PNT inputs). Closing it needs explicit prime-count
  inputs in `eventually_moebiusRenormalizedDefect_polynomial_cofinal_bound` and
  `eventually_periodCovariance_moebius_zero_ge`, plus the finite horizons below the resulting `N₀`.
- 2026-10-21 — **Row 5 decided** (RW/SZ/CHMD completed norms). `RHTower/SuzukiScrewCompletionInsideTheWeilFormDomain`:
  dilation `g(r·)` multiplies `‖g'‖²` by `r` while the Weil form norm decays like `√((1+log r)/r)`, so
  `not_exists_derivative_norm_le_weilFormNorm`; the primitive map `P : L²₀ → 𝒟_W` is injective with dense range
  and `not_surjective_suzukiZeroMeanPrimitiveCCMFormCLM` — the SZ completion is a proper dense subspace of RW's.
  Signs agree: `screw_nonneg_iff_restrictedWeil_nonneg`, `quotientWeilForm_nonneg_of_restrictedWeil_nonneg`.
  `RHTower/CHMDGraphNormIsTheWeilFormNormOnAnAperture`: `‖testLift u‖² = W(u) + 2‖u/Φ‖²_μ − 2⟨·,1⟩² + 2⟨·,tanh⟩²`
  gives `exists_testLift_norm_sq_equiv_weilFormNorm` (graph ≍ RW norm on a fixed aperture) and
  `exists_norm_suzukiCoreSignedQuotient_le`. Answer: one receiver for the sign; norms SZ ⊊ RW ≍ CHMD-graph;
  open: lower bound of the signed-radical quotient norm on the aperture core. Wired in RHTower.lean; axioms standard.
- 2026-10-21 — **Row 8 (closed-form thresholds)**: `arithmetic-positivity-theory/ExplicitBlockThresholdsOfTheCriticalFamily`
  replaces every `∃ M₀` of the critical family by `logLinearThreshold s c C = max 2 (⌊exp(c + C/s)⌋ + 1)`:
  complete form + translated patterns (`criticalBlockThreshold`), collared, doubly collared truncations and the
  full Weil functional of ζ on them (`criticalTruncatedBlockThreshold`), lacunary unions, polynomial windows with
  `δ = s/(4(W+1))`, threshold `max 2 (⌊exp(2K/s)⌋ + 1)`. Numerical evaluation of `C` blocked on explicit bounds
  for the smooth-transition collar integrals (`∫|ψ'|, ∫|ψ''|`) and `Σ Λ(r) r^{-3/2}`; range of `R` beyond
  `R ≤ −1/7000` not attempted. Wired in ArithmeticPositivityTheory.lean; axioms standard.
- 2026-10-21 — **Row 6 (selectivity audit, window theorems)**: `SquareRootThreshold/WindowCertificatesAndThePrimeWeight`:
  `weilFullFunctional_eq_of_eqOn` (the functional reads `w(n)` only for `log n ∈ supp k`); prime-free windows are
  weight-independent (`weilFullFunctional_eq_of_tsupport_subset`), so the 3/10 certificate holds for every weight,
  incl. `λΛ` (`re_weilFullFunctional_ge_of_aperture_le_threeTenths`, `…liouvilleTwist…`); below `log 3` only the
  atom at 2 is read (`weilFullFunctional_sub_eq_atom_two`); the 362/1000 odd window holds for every `w` with
  `w(2) = log 2` (`re_weilFullFunctional_ge_of_odd_window`); Liouville twist: certificate + `√2 log 2·(k(log2)+k(−log2))`
  (`re_weilFullFunctional_liouvilleTwist_odd_window`). Continuous Beurling systems (no integer weight) are outside
  the `weilFullFunctional` API; the audit of non-window positivity theorems (APT blocks, BVI, SRT lags) is open.
  Also repaired the SRT umbrella (two imports had been appended after its docstring by another lane).
