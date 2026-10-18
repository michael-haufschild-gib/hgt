# Classical RH bridges and current-worktree ledger audit

- **ID:** classical-rh-bridges-2026-10-18
- **Stage:** 3-formalized
- **Type:** THEOREM (classical), Lean formalization complete
- **Source:** User attachment `7934a5ab-daf8-4d09-9749-24e6d93e3973/pasted-text-1.txt`
- **Statement:** Close the requested classical converse interfaces, prove the sharp conditional dyadic prime-error energy bound and unconditional BSY zero-sum identity, and reconcile BVI/MC/CTF/PM/FEL ledger evidence.

## Scope and completion requirements

- [x] Remove any extra classical-converse premise from the intended BVI power-saving increment criterion, using an existing proved Möbius-to-RH bridge; audit every consumer.
- [x] Prove `RH →` the sharp dyadic Chebyshev mean-square bound, with no extra analytic premise. The named `dyadic_band_energy_bound` is absent from the current worktree. The precise Cramér target proved is a constant `C≥0` with `∫_[X,2X] (ψ(x)-x)^2 dx ≤ C X²` for all `X ≥ 1`.
- [x] Prove the literal BSY integral identity as a convergent sum over all right-half-plane zeta zeros, counting multiplicity.
- [x] Reconcile the requested ten BVI modules and affected route rows with current source/import/compiler evidence.
- [x] Check every changed/new Lean leaf using `lake --old env lean <original-source>`; audit axioms in `/tmp`; run `scripts/formal_tools.py lint`; wire new leaves and remove owned temporary/stale artifacts. Global lint has unrelated ownership/wiring failures, detailed below.

No full or umbrella builds, numerical experiments, new axioms, proof debt, heartbeat increases, commits or pushes. Preserve pre-existing concurrent changes. Implications and equivalences retain their mathematical arguments; no assumed classical theorem or unproved bridge may be added as a parameter.

## Final results and verification

- `BezoutValuationIncidence/PowerSavingIncrementCriterion.lean`:
  `mobiusFirstOctavePowerSaving_iff_riemannHypothesis`, via the exact Mertens equivalence.
  No classical-converse parameter. `PrimeTailCalibrationAndMobiusDefect.lean` already had no
  such parameter; its proved raw-defect obstruction is preserved.
- `RHTower/CramerZeroSumMeanSquare.lean` and `RHTower/CramerChebyshevMeanSquare.lean`:
  `dyadic_chebyshev_mean_square_of_riemannHypothesis` proves
  `RH → ∃ C≥0, ∀ X≥1, ∫_X^{2X}(ψ(x)−x)² dx ≤ C X²`. This is the literal sharp Cramér
  bound, including the compact initial range, with no extra analytic premise.
- `RHTower/BalazardSaiasYorZeroSum.lean`:
  `hasSum_log_norm_rightZetaZeros` and
  `integral_log_norm_zeta_criticalLine_eq_tsum_rightZeros` prove convergence and the
  unconditional BSY identity with each zero's analytic multiplicity.
- All four new leaves are umbrella-wired. Fifteen original leaves passed targeted Lean
  checks, including every one of the ten requested BVI modules. All 33 audited statements
  have exactly `[propext, Classical.choice, Quot.sound]` axiom closure. No full/umbrella
  builds, numerical experiments, heartbeat increases, commits or pushes were performed
  by this task.
- `scripts/formal_tools.py index` passed and refreshed the generated API/overview/gap
  indexes and source-search database. `git diff --check` passed on the task's changed
  documentation and umbrellas. All nine owned `/tmp` scratch/audit/search files were removed.

**Global lint limitation:** `scripts/formal_tools.py lint --check-generated` exited 1 with
seven unrelated ownership/wiring errors, and no proof-debt, heartbeat or generated-index
error. The five current untracked RHTower leaves `IntervalMeanSquareTransfer`,
`ZetaDirichletBandMeanSquare`, `ZetaFiniteMeanSquare`, `ZetaSuperlinearCutoff`, and
`ZetaSuperlinearTruncation` are not reachable from their umbrella. Existing root modules
`GaloisForLFunctions/ArithmeticPositivityTheory.lean` and
`GaloisForLFunctions/TransHorizonIncidenceMechanics.lean` are absent from the lint tool's
allowed root-module registry. These belong to other concurrent work and were left unchanged
under the user's task-scope boundary. No global lint pass is claimed.

The frontier ledger and BVI README now reflect the proved interfaces. The ledger distinguishes
the freshly audited, uncommitted Cramér leaves (`[Lw]`) from the committed checkpoint and keeps
all source-derived RH-closing estimates open.

## Initial-state investigation

- `PowerSavingIncrementCriterion.lean` is absent. `PrimeTailCalibrationAndMobiusDefect.lean` has no RH or classical-converse parameter; it proves a sharp calibration and rules out sublinear bounds for the **raw** defect. This obstruction must not be silently replaced by an RH criterion for that false target.
- `RHTower/MobiusMertensLittlewood.lean` already closes `MobiusMertensAllStrictHalfPowerBound ↔ RiemannHypothesis` without a classical-converse premise. Its converse comes from `MobiusMertensSelfConvolutionCriterion.lean`.
- Exact symbols `riemannHypothesis_of_cesaro_mobius_bound`, `riemannHypothesis_of_dyadic_log_moment_bound`, and `dyadic_band_energy_bound` are absent in source searches. `riemannHypothesis_of_mertens_bound` in `MertensPolylogStrictMultiplicity.lean` has a different, fixed-polylogarithmic hypothesis.
- `RHTower/ZetaCriticalLineJensenEquality.lean:910` already proves the unconditional limit of finite Jensen divisor sums equal to the normalized BSY integral. The remaining interface is a literal summable zero series and its exact multiplicities/reindexing.
- The frontier ledger already lists all nine requested primitive-energy/prediction/lag modules as `[L]`. The shifted-exponent module is imported but still `[S]` because the ledger defines `[L]` as committed. A verified worktree status must be distinguished from a committed checkpoint; no commit is authorized.
- `FEL` currently denotes theta likelihood and has no BSY identity claim. Any added BSY evidence must keep its scalar identity separate from the open source-derived contrast balance.
- Serena symbol retrieval rejects these ignored Lean paths. Use source-text inspection and patches as fallback. `update_plan` is unavailable; this card is the persistent plan.
- Initial corpus search returned relevant BSY and Mertens results but reported partial coverage (deadline/reranking pending). Exact `rg` searches supplement it; search hits are not compilation certificates.

## Proof strategy and adversarial audit

1. Recover the intended increment observable from literal first-octave Möbius sums. Prove its equivalence with the existing strict-half-power Mertens bound and then apply the already proved RH equivalence. The user subsequently instructed “do all. decide yourself”; use this precise target and do not infer a false raw-defect estimate.
2. Establish Cramér's **sharp** `X²` mean square using the explicit formula and the zero-pair kernel. Squaring von Koch's pointwise bound only gives `X² log⁴ X`, which does not satisfy the request. Source reference: Brent–Platt–Trudgian, *The mean square of the error term in the prime number theorem*, https://arxiv.org/abs/2008.06140, introduction and equation (4).
3. For BSY, use `G(w)=(s−1)ζ(s)`, `s=1/(1−w)`, with `G(0)=1`. Jensen sums have nonnegative terms. As `r↑1`, each zero term increases to `m_u log(1/|u|)`; monotone convergence identifies a summable family with the already proved finite boundary integral. The bijection `u=1−1/ρ` maps `Re ρ>1/2` to `|u|<1`, preserves multiplicity, and gives `log(1/|u|)=log|ρ/(1−ρ)|`. Prove the reindexing, not only a commentary interpretation of a radial limit.
4. Verify requested existing leaves and their relevant declarations. Reconcile ledger labels without equating uncommitted work with committed evidence or claiming RH/source cancellation.

## Development verification (historical)

`lake --old env lean GaloisForLFunctions/BezoutValuationIncidence/ShiftedExponentAsymptoticDensityAndActiveMartingaleRate.lean` exited 0 with no diagnostics. Remaining original-source and axiom audits pending. Read-only checks above are source evidence, not proof audits.

`/tmp/hgt_classical_rh_bsy.lean` and `/tmp/hgt_classical_rh_increment.lean` now compile without
diagnostics. Installed as `RHTower/BalazardSaiasYorZeroSum.lean` and
`BezoutValuationIncidence/PowerSavingIncrementCriterion.lean`; both umbrella imports added.
The BSY original-source audit with a targeted `.olean` output has also passed. The remaining
original-source and axiom audits are in progress; no full/umbrella build is used.

Both new original-source audits have now passed with targeted `.olean` outputs. A concurrent
workspace checkpoint (`433a7db3362b2f5cff3442b1624dfc59c3573156`) now tracks these leaves and
the shifted-exponent leaf; this task did not commit or push. Concurrent ledger edits already
promoted the shifted-exponent row and added the MC/BVI increment receiver. Preserve those edits;
the present reconciliation adds the precise CTF receiver, the FEL BSY identity, and fresh audit
evidence. The requested nine primitive/prediction/lag leaves are being checked sequentially.

The increment criterion quantifies every `δ > 0`, one `Cδ ≥ 0` independent of `N,n`, and
`1 ≤ N < n ≤ 2N`. Its bound is
`|fermiCellResponse N moebiusReal n - 1| ≤ Cδ (n+1)^(1/2+δ)`.
Strong induction with `N = (n+1)/2` and scale ratio `3/4` proves the reverse passage to the
global Mertens bound. The resulting RH equivalence has no classical-converse parameter.

For the sharp Cramér proof, `/tmp/hgt_classical_rh_cramer.lean` now contains the dyadic
zero-height shell estimates. A shell indexed by `k` contributes at most
`10240 A³ D² X⁻¹ (k+1)³ 2⁻ᵏ` when `|cρ| ≤ D/|Im ρ|`. Weighted Cauchy–Schwarz with
weights `(3/4)^k` will sum this uniformly in every finite zero set. These estimates are
under verification, not yet claimed proved.

## Log

- 2026-10-18 — `RHTower/CramerChebyshevMeanSquare.lean` is installed and umbrella-wired. Its original-source audit passed without diagnostics, as did the four Cramér axiom checks: exactly `[propext, Classical.choice, Quot.sound]`. The sharp theorem `dyadic_chebyshev_mean_square_of_riemannHypothesis` has only RH as its premise and covers every `X≥1`. All four requested mathematical/ledger tasks are complete; generated-index refresh, formal lint and temporary-file cleanup are the remaining final gates.
- 2026-10-18 — `RHTower/CramerZeroSumMeanSquare.lean` now proves the finite and absolutely convergent zero-sum estimates under RH. Installed, umbrella-wired, and original-source checked with a targeted `.olean` output; no diagnostics. The short-window coefficient bound `|cρ(r)|≤2/|Im ρ|`, exact dilation, uniform trivial-zero correction, measurable window error, right continuity, and window-to-`ψ−x` limit also compile in scratch. The full sharp `∫_X^{2X}(ψ−x)²≤C X²` proof is now drafted in `/tmp/hgt_classical_rh_cramer_window.lean`, including compact `1≤X<2`; its final integration/limit assembly is being checked.
- 2026-10-18 — All ten requested BVI leaves passed original-source checks; the nine primitive/prediction/lag leaves were checked sequentially with targeted `.olean` outputs, and the shifted-exponent leaf had passed earlier. `PrimeTailCalibrationAndMobiusDefect.lean` also passed. All 29 public statements in `/tmp/hgt_classical_rh_axioms.lean`, including both new endpoints and the relevant statements from every requested leaf, have exactly `[propext, Classical.choice, Quot.sound]` axiom closure. No extra converse premise or raw-defect change is needed. Cramér's sharp bound and final lint/cleanup remain open.

- 2026-10-18 — Read attachment and session guidance; inspected relevant memories and current source. Recorded stale task names, existing Littlewood equivalence, BSY Jensen-limit proof, and current ledger differences. No mathematical target is claimed complete.
- 2026-10-18 — The user confirmed autonomous decisions for all four tasks. BSY finite-sum domination, summability and disc-series equality compile in `/tmp/hgt_classical_rh_bsy.lean`; actual-zero reindexing is under verification. `/tmp/hgt_classical_rh_increment.lean` contains the first-octave/Mertens equivalence draft.
- 2026-10-18 — Located the sharper Cramér ingredients: `ZetaZeroSumMeanSquare.integral_norm_sq_zeroSum_div_cube_le`, `XiZeroOrdinateHarmonicSums.sum_inv_one_add_abs_im_sub_le`, `VonKochChebyshevBound.card_xiCopiesBelow_le_log`, and the absolutely convergent smoothed window formula in `ChebyshevShortWindowLowerBound`. Dyadic **zero-height** decomposition plus weighted Cauchy–Schwarz can turn shell estimates `O((k+1)^3 2^(-k))` into a uniform finite-zero-sum L² bound. Then apply it to multiplicative short-window coefficients, uniformly as window length tends to zero, and use Fatou to recover the literal prime error. This proof remains to be formalized; no sharp dyadic bound is yet claimed.
