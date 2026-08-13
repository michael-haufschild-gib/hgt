# BOTTLENECK 1 CLOSED — M. Riesz proved, MaximalTranslationInputs constructed (2026-08-13)

All axiom-clean, wired into `GaloisForLFunctions.HTGeometry` (umbrella EOF).

## The two closing modules

1. `NevanlinnaTransferMinimalType.lean` — **M. Riesz via Simon's transfer route** (Simon, Adv.
   Math. 137 (1998) §4; NO Hadamard/Weierstrass needed — earlier no-go corrected):
   - transfer identities `p_n(z) = q_n(0)·D_n(z) − p_n(0)·B_n(z)`,
     `q_n(z) = q_n(0)·C_n(z) − p_n(0)·A_n(z)` — one `linear_combination` each from the corpus
     Duhamels (`monicOrthoC_duhamel`/`secondKindC_duhamel` at `(0,z)`), after rewriting
     `bilinearPartialSum` term order by `Finset.sum_congr … ring`;
   - four-entry max recursion + `exists_prod_le_exp_of_summable` tail split;
   - `nev{A,B,C,D}inf_hasMinimalExponentialType (h : PositiveMomentForm s) (h0b : BoundedKernel s 0)`.
2. `AnalyticNevanlinnaMaximalTranslationInputs.lean`:
   - **`analyticNevCarrierFamilyMaximalTranslationInputs h h0b h0`** — complete term;
   - **`analyticNevCarrierFamily_maximalTranslationPhase_dense_residual`** and full-rank version —
     the ten-card capstone with NO open analytic input.

## What the ten moment-fibre cards still need (per-card assembly)
Cards 5, 11, 17, 19, 21, 25, 34, 35, 36, 41 in the nad ledger: each must be audited for its OWN
numbered statements above the capstone (spectral-type stratification, Schur defect, Toeplitz weld,
jet aperture, Cholesky selection, …), then promoted with companions.  The interface work is done.
Optional polish: leaf/label covariance (task #5, `NevanlinnaConstraintProjector` — the transport
theorem exists; the "arbitrary normalization change" upgrade needs a canonicity statement).

## Lean gotchas this session
- This toolchain lacks `le_or_lt` (use `by_cases`+omega), `sum_le_tsum` is
  `Summable.sum_le_tsum`, `Summable.tendsto_sum_nat` is `hasSum.tendsto_sum_nat`,
  `Finset.one_le_prod` takes ONE explicit arg, `Finset.range_subset.mpr` doesn't elaborate (use
  intro/omega subset proofs), `Finset.prod_le_prod_of_subset_of_one_le'` needs OrderedCommMonoid
  (NOT ℝ — use prod_Ico_consecutive split + le_mul_of_one_le_right).
- `field_simp` often closes goals fully — don't append `ring` blindly ("no goals").
- `unfold X bilinearPartialSum` + `Finset.sum_range_succ` + `ring` handles all truncation
  increments.
