# Smooth complete arithmetic sections with exact pole degrees

- **ID:** acs-smooth-hecke-complete-sections
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Route:** ACS: source sections → Riemann–Roch and ampleness → Hodge index → RH.
- **Statement:** Complete logarithmic cells admit injective realization in the original compact C² test carrier, preserving exact Hecke subdivision and both pole moments, and recovering the original full arithmetic form.

## Mathematical result

Let `ρ_n` be the even nonnegative compact mollifier of integral one and shrinking support. Set

\[
 C_n=\int\rho_n(u)\cosh(u/2)\,du,\qquad
 K_n=C_n^{-1}\rho_n,\qquad S_nf=K_n*f.
\]

Then `C_n ≥ 1`, `C_n → 1`, and both exponential moments of `K_n` equal one. For every compact BV source, `S_n f` is compact C², preserves both exponential and hyperbolic pole coordinates exactly, contracts the full Gamma jump energy, and recovers ordinary L² mass and Gamma energy in the limit.

For positive integers `a,m`, let `φ_{a,n}=S_n 1_[log a,log(a+1))`. These sections satisfy the exact identity

\[
 \phi_{a,n}(x-\log m)=\sum_{r=0}^{m-1}\phi_{am+r,n}(x).
\]

For every `n,X`, the first `X` sections are linearly independent in `realTests`; their span has dimension `X`. The same smoothing map acts on every coefficient vector and commutes with every translation.

For arbitrary real coefficients `c : ℕ → ℝ`, the original surface form on
`S_n (wholeCellProfile c X)` converges to the existing `finiteCellWeil c 0 1 X`. This is the canonical cell window `[log 1, log (X+1))`. The limit retains square mass, the full Gamma jump energy, every prime translation, and both signed pole terms.

## Proof

1. Evenness equates the two exponential kernel moments. Dividing by their common positive value fixes both moments. Weighted convolution and Fubini give exact pole preservation; translation covariance and finite linearity preserve the whole-cell Hecke identity.
2. A nonzero coefficient vector has a first nonzero cell. Its signed left support edge survives convolution with the positive kernel, proving injectivity even when smoothed supports overlap. Linear independence gives the exact dimension.
3. Approximate-identity convergence in Lebesgue L² recovers mass and every fixed translation correlation. Kernel normalization tends to one. The original BV jump energy dominates the smoothed jump integrands, so dominated convergence retains the entire singular Gamma integral.
4. All smoothing scales share one compact support horizon. The prime sum is therefore one finite sum of converging correlations. Exact pole preservation and the mass and Gamma limits recover the full Weil form.
5. Zero extension of the actual half-line `cellSection` equals the whole-cell profile almost everywhere. Its compressed translation pairing equals the whole-line correlation. Thus `cellPrimeEnergy` is exactly the profile's `primeSum`; `weilQuad_eq_zetaW` identifies the limit with the original surface.

## Lean declarations

Namespace: `GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells`.

| Module | Main declarations |
| --- | --- |
| `PolePreservingSmoothing.lean` | `poleKernel_expMoment`, `poleSmooth_expMoments`, `poleSmooth_translate`, `levyEnergy_poleSmooth_le`, `tendsto_poleSmooth_L2_error`, `tendsto_poleSmooth_levyEnergy` |
| `SmoothArithmeticCellSections.lean` | `smoothCell_hecke`, `poleSmooth_rawSection_ne_zero`, `linearIndependent_smoothCell`, `finrank_smoothCell_span` |
| `SmoothCompleteWeilTransfer.lean` | `poleSmooth_halfMoments`, `tendsto_poleSmooth_primeSum`, `tendsto_poleSmooth_weilQuad`, `complete_cells_smooth_realization` |
| `SmoothFiniteCellArithmeticForm.lean` | `cellPrimeEnergy_eq_wholeCellProfile`, `finiteCellWeil_smooth_realization`, `finiteCellWeil_original_surface_limit` |

## Verification

The four sources have passed Lean checking through their checked drafts or required dependency builds. Seventeen principal transitive axiom audits contain only `propext`, `Classical.choice`, and `Quot.sound`. All four modules are imported by the ACS umbrella; the umbrella is not compiled.

Final plain exact-project-file checks remain before promotion:

- [ ] `PolePreservingSmoothing.lean`
- [ ] `SmoothArithmeticCellSections.lean`
- [ ] `SmoothCompleteWeilTransfer.lean`
- [x] `SmoothFiniteCellArithmeticForm.lean` — exit 0; all three audits standard-only.

## Remaining ACS blockers

Full-source effectivity and the signed Gamma–prime–pole index bound remain open on `acs-complete-cell-index-payment`. The construction closes smooth realization and exact arithmetic compatibility; no positivity of arbitrary complete-cell forms is asserted.

## Working state

Owned checked drafts: `/tmp/acs-polar-mollifier-api.lean`, `/tmp/acs-polar-smoothing-draft.lean`, `/tmp/acs-polar-smoothing-extension.lean`, `/tmp/acs-smooth-cells-draft.lean`, `/tmp/acs-smooth-weil-draft.lean`, `/tmp/acs-smooth-finite-form-draft.lean`. Remove these and the owned ACS check logs after the final audits.

## Log

- 2026-10-28 — Constructed and checked all four modules. Final plain exact-file audits pending; no stage-2 card created.
