# Classical Möbius, Cramér and BSY interfaces — 2026-10-18

Completed four user-requested tasks. Persistent final card: `docs/drafts/pipeline/3-formalized/classical-rh-bridges-and-ledger-audit-2026-10-18.md`.

## Proven interfaces

- `formal/GaloisForLFunctions/BezoutValuationIncidence/PowerSavingIncrementCriterion.lean`: `mobiusFirstOctavePowerSaving_iff_mertens` and `mobiusFirstOctavePowerSaving_iff_riemannHypothesis`. For every δ>0, one constant bounds the actual first-octave increment |fermiCellResponse N moebiusReal n − 1| by Cδ(n+1)^(1/2+δ), uniformly for 1≤N<n≤2N. Strong induction with N=(n+1)/2 recovers Mertens bounds, then uses `RHTower.MobiusMertensLittlewood`. No classical-converse hypothesis. Requested file had been absent. `PrimeTailCalibrationAndMobiusDefect.lean` already had no converse parameter; preserve its raw-defect sublinear-bound obstruction.
- `formal/GaloisForLFunctions/RHTower/CramerZeroSumMeanSquare.lean`: uniform finite and absolutely convergent zero-sum mean-square estimates for coefficients bounded by D/|Im ρ| under RH. Dyadic zero-height shell estimate O(D² X⁻¹(k+1)³2⁻ᵏ); weighted Cauchy–Schwarz weights (3/4)^k eliminate cutoff dependence. Public `cramer_finite_zero_energy`, `cramer_summable_zero_energy`.
- `formal/GaloisForLFunctions/RHTower/CramerChebyshevMeanSquare.lean`: `dyadic_chebyshev_mean_square_of_riemannHypothesis` proves RH → ∃ C≥0, ∀ X≥1, ∫_X^{2X}(Chebyshev.psi x − x)² dx ≤ C X², with no extra analytic premise. Multiplicative short windows have coefficients uniformly ≤2/|Im ρ|; bounded trivial-zero correction and dominated convergence recover the literal error. Includes 1≤X<2. Requested names `dyadic_band_energy_bound` and `riemannHypothesis_of_dyadic_log_moment_bound` were absent; do not equate this proved literal Cramér bound with an endpoint-free spectral band bound without an additional transfer.
- `formal/GaloisForLFunctions/RHTower/BalazardSaiasYorZeroSum.lean`: `hasSum_log_norm_rightZetaZeros` and `integral_log_norm_zeta_criticalLine_eq_tsum_rightZeros` prove the unconditional BSY identity, summability, and analytic multiplicities. Uses the existing radial Jensen limit, nonnegative finite-sum domination, Cayley reindexing and order transport.

## Verification and ledger

All four leaves umbrella-wired. Fifteen original leaves passed `lake --old env lean`, including all ten requested BVI leaves and the raw prime-tail leaf. Thirty-three endpoint axiom checks report only propext, Classical.choice, Quot.sound. No full/umbrella build, numerical experiment, heartbeat increase, commit or push by this task. A concurrent checkpoint 433a7db3362b2f5cff3442b1624dfc59c3573156 had already captured the first two new leaves and shifted-exponent work.

Frontier ledger and BVI README synced. New Cramér current-worktree evidence marked [Lw], separate from committed [L]. All arithmetic RH-closing estimates remain open.

`formal_tools.py index` passed. Global `lint --check-generated` failed with seven unrelated ownership/wiring errors: untracked RHTower IntervalMeanSquareTransfer, ZetaDirichletBandMeanSquare, ZetaFiniteMeanSquare, ZetaSuperlinearCutoff, ZetaSuperlinearTruncation unreachable from umbrella; root ArithmeticPositivityTheory.lean and TransHorizonIncidenceMechanics.lean absent from allowed-root registry. No proof-debt, heartbeat or generated-index error was reported. These concurrent files were left unchanged under the task-scope boundary. Do not claim global lint passed.

Owned /tmp proof/API/audit/search files removed. Serena symbol operations reject ignored Lean paths; rg/read/patch fallback was used.