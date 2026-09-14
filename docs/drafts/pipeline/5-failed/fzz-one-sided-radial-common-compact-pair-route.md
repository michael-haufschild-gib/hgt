# FZZ one-sided common-compact reflected-pair route

- **ID:** fzz-one-sided-common-compact-pair-route
- **Stage:** 5-failed
- **Type:** FALSIFIED
- **Source:** `rh-current-frontier-map.md` · FZZ-P
- **Statement:** A source-fixed/conjugate-blind complex compact response can cancel a nonzero reflected radial pair.

## No-go closure

- **Exact killing theorem/mechanism:** `D(-p)=-conj(D(p))`, while `Re D(p)=0 ↔ p=0`; equality of
  the two receivers required by one common response therefore forces `p=0`.
- **Strongest positive survivor:** independently cancelling responses obey exact orientation law
  `C₋=-conj(C₊)` (`fzzOneSidedRadial_cancellingCompactResponses_neg_eq_neg_conj`).
- **New insight:** viable compact FZZ source must retain orientation and be conjugate-odd; any
  phase-erasing/common source response is excluded off critical momentum.
- **Status:** dependency-closed and formalized in
  `FZZCigarOneSidedRadialCommonCompactPairNoGo.lean`; direct checks and targeted leaf build pass.

## Scope

Kills common-response branch only. Orientation-sensitive compact response remains open and must
also match physical normalization and all-depth cross-charge weights.
