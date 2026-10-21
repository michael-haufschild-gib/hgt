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
