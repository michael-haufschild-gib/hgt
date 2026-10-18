# Classical RH bridges and current-worktree ledger audit

- **ID:** classical-rh-bridges-2026-10-18
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper), formalization in progress
- **Source:** User attachment `7934a5ab-daf8-4d09-9749-24e6d93e3973/pasted-text-1.txt`
- **Statement:** Close the requested classical converse interfaces, prove the sharp conditional dyadic prime-error energy bound and unconditional BSY zero-sum identity, and reconcile BVI/MC/CTF/PM/FEL ledger evidence.

## Scope and completion requirements

- [ ] Remove any extra classical-converse premise from the intended BVI power-saving increment criterion, using an existing proved Möbius-to-RH bridge; audit every consumer.
- [ ] Prove `RH →` the sharp dyadic Chebyshev mean-square bound, with no extra analytic premise. The user describes Cramér's bound; the named `dyadic_band_energy_bound` is absent from the current worktree. Proposed precise target: a constant `C` with `∫_[X,2X] (ψ(x)-x)^2 dx ≤ C X²` for all `X ≥ 1`.
- [ ] Prove the literal BSY integral identity as a convergent sum over all right-half-plane zeta zeros, counting multiplicity.
- [ ] Reconcile the requested ten BVI modules and affected route rows with current source/import/compiler evidence.
- [ ] Check every changed/new Lean leaf using `lake --old env lean <original-source>`; audit axioms in `/tmp`; run `scripts/formal_tools.py lint`; wire new leaves and remove owned temporary/stale artifacts.

No full or umbrella builds, numerical experiments, new axioms, proof debt, heartbeat increases, commits or pushes. Preserve pre-existing concurrent changes. Implications and equivalences retain their mathematical arguments; no assumed classical theorem or unproved bridge may be added as a parameter.

## Current-state investigation

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

## Verification record

`lake --old env lean GaloisForLFunctions/BezoutValuationIncidence/ShiftedExponentAsymptoticDensityAndActiveMartingaleRate.lean` exited 0 with no diagnostics. Remaining original-source and axiom audits pending. Read-only checks above are source evidence, not proof audits.

## Log

- 2026-10-18 — Read attachment and session guidance; inspected relevant memories and current source. Recorded stale task names, existing Littlewood equivalence, BSY Jensen-limit proof, and current ledger differences. No mathematical target is claimed complete.
- 2026-10-18 — The user confirmed autonomous decisions for all four tasks. BSY finite-sum domination, summability and disc-series equality compile in `/tmp/hgt_classical_rh_bsy.lean`; actual-zero reindexing is under verification. `/tmp/hgt_classical_rh_increment.lean` contains the first-octave/Mertens equivalence draft.
- 2026-10-18 — Located the sharper Cramér ingredients: `ZetaZeroSumMeanSquare.integral_norm_sq_zeroSum_div_cube_le`, `XiZeroOrdinateHarmonicSums.sum_inv_one_add_abs_im_sub_le`, `VonKochChebyshevBound.card_xiCopiesBelow_le_log`, and the absolutely convergent smoothed window formula in `ChebyshevShortWindowLowerBound`. Dyadic **zero-height** decomposition plus weighted Cauchy–Schwarz can turn shell estimates `O((k+1)^3 2^(-k))` into a uniform finite-zero-sum L² bound. Then apply it to multiplicative short-window coefficients, uniformly as window length tends to zero, and use Fatou to recover the literal prime error. This proof remains to be formalized; no sharp dyadic bound is yet claimed.
