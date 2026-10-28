# Complete logarithmic cells recover the full Weil source form

- **ID:** acs-complete-cell-archimedean-transfer
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Route:** ACS: full-source sections → Riemann–Roch and ampleness → Hodge index → RH.
- **Statement:** Every finite family of real compact C² sources admits one complete logarithmic-cell exhaustion that converges in L² and recovers the original `zetaZeroConfig.W` on every real linear combination, together with every polarized Gram entry.

## Mathematical result

The arithmetic form `finiteCellWeil` depends only on finite cell coefficients and their coordinates. It includes square mass, the entire Gamma Lévy energy, all prime translations, and both pole moments. Evaluating it on logarithmic samples gives `completeCellWeil`.

The same cells realize the actual Hilbert-space sections: zero extension agrees almost everywhere with the translated cell profile. Sampling commutes exactly with finite linear synthesis. The convergence theorem therefore applies to one coherent finite-dimensional source space.

All support, regularity, and error bounds are derived from compact C² sources. No positivity, effectivity, spectral estimate, or additional analytic input is assumed.

## Proof

1. The logarithmic floor map is monotone and samples each cell at its left endpoint. A Lipschitz source has uniform cell error at most `K / N`; the error has total variation at most twice the source variation.
2. For compact BV functions, uniform size times total variation bounds the complete Gamma jump integral. Its finite first moment gives
   `levyEnergy (step_N f - f) ≤ 8 K Var(f) J / N`,
   where `J = ∫ t > 0, t * archLevyDensity t`. The jump vectors lie in one fixed L² space, so their energies converge.
3. A common compact support window and dominated convergence recover ordinary L² error, square mass, and both hyperbolic pole moments.
4. The previously formalized complete prime transfer recovers `primeSum` on this same window, including every successor remainder. Adding these limits recovers `weilQuad`, identified with the real part of the original `zetaZeroConfig.W`.
5. The sum of squared source magnitudes selects a common window without cancellation. Every real linear combination uses it; polarization recovers all Gram entries.

The explicit `O(1/N)` estimate above concerns jump-error energy. The full Weil-form theorem asserts convergence.

## Lean declarations

Namespace: `GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells`.

| Module | Main declarations |
| --- | --- |
| `LogarithmicStepProfiles.lean` | `abs_logStep_sub_le`, `variation_logStep_sub_le`, `logStep_eq_sample` |
| `CompleteCellLevyTransfer.lean` | `levyEnergy_logStep_sub_le`, `exists_complete_cell_levy_rate`, `tendsto_logStep_levyEnergy` |
| `CompleteCellMomentTransfer.lean` | `tendsto_logStep_mass`, `tendsto_logStep_coshHalfMoment`, `tendsto_logStep_sinhHalfMoment` |
| `CompleteCellRealization.lean` | `logStep_eq_indicator_sum`, `halfLineExtend_cellSection_logSamples`, `cellSection_logSamples_sum` |
| `CompleteWeilSourceTransfer.lean` | `exists_completeScalingSurfaceSource`, `exists_completeWeilGram`, `exists_completeFiniteSourceTransfer` |

## Verification

All five modules passed plain exact-file checks from `formal/` with `lake --old env lean`, exit 0, no warnings. Eighteen printed transitive axiom audits contain only `propext`, `Classical.choice`, and `Quot.sound`. No placeholders, new axioms, trusted-computation shortcuts, or raised resource limits occur in these modules.

All five modules are imported by the ACS umbrella; the umbrella was not compiled. The card moved directly from stage 1 to stage 3 after verification; no paper-only result remains.

## Remaining ACS blockers

Full-source effectivity, section-count Riemann–Roch and ampleness, and the signed joint Gamma–prime–pole index bound remain open. This result closes source transfer; it does not assert positivity of arbitrary complete-cell forms or close RH.

## Log

- 2026-10-28 — Formalized complete finite-source transfer and promoted directly from stage 1 to stage 3.
