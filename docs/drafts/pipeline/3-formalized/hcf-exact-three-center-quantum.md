# HCF exact three-center lattice quantum

- **ID:** HCF-3C-EXACT-001
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `rh-current-frontier-map.md` · Route HCF receiver geometry
- **Statement:** `[PROVED HERE]` On the open critical strip and in a nearest lattice cell,
  three fixed critical-feature centers carry Hermitian energy at least `23232/4225`; equality is
  attained at half-cell points on the critical axis.  Hence corrected HCF source budget
  `1452/4225 * N` suffices for a 75% critical-line receiver.

## Goal

Recover all coercive mass already present in the divisor-independent three-center window.  Earlier
proof retained only independent per-center floors, giving source thresholds `21/100` and then
`209/900`.  Joint optimization is required because near- and far-center denominator extrema cannot
occur at the same strip point.

## Gates

- [x] 0 → 1  in-progress: exact compact polynomial inequality and source-independent centers
- [x] 1 → 2  fully-proven: degree-six tensor Bernstein certificate plus sharpness witness
- [x] 2 → 3  formalized: targeted Lean check green; axiom audit pending final session gate
- [ ] 3 → 4  publication-ready: standalone exposition and external novelty audit

## Approach

Write `u = Re z - t`, `y = Im z`, `x = 4u²`, and `p = 1 - 4y²`.  The nearest-cell strip gives
`x,p ∈ [0,1]`.  After clearing the three positive kernel denominators, the claimed lower bound is a
bivariate polynomial of degree six in each coordinate.  Its tensor Bernstein coefficients on
`[0,1]²` are nonnegative; exactly one endpoint coefficient vanishes.  Re-dividing by the positive
denominator product proves

`threeCenterCriticalFeatureEnergy t z ≥ 23232/4225`.

At `z = t + 1/2`, the three energies are `64/169`, `64/25`, and `64/25`, whose sum is exactly
`23232/4225`.  Finite lattice summation and the existing holomorphic-sector factor two give strict-
right source charge `11616/4225`.  Combining `N = N₀ + 2S` with budget
`B ≤ 1452/4225 * N` yields `S ≤ N/8` and therefore `3N/4 ≤ N₀`.

Formal module:
`formal/GaloisForLFunctions/RHTower/HedenmalmCriticalFeatureThreeCenterSharpQuantum.lean`.

Principal theorems:

- `threeCenterCriticalFeatureDenominatorCleared_nonneg`
- `sharp_threeCenterCriticalFeatureEnergy_lower`
- `sharp_threeCenterCriticalFeatureEnergy_eq_at_halfCell`
- `finite_strictRight_card_mul_sharpThreeCenterSourceCharge_le_offLineLatticeBudget`
- `three_quarters_line_of_exactThreeCenter_primeGammaOffLineLatticeBudget`

## No-go closure (mandatory when falsified)

- **Exact killing theorem/mechanism:** not falsified
- **Strongest positive survivor:** exact sharp three-center quantum and improved 75% receiver
- **New insight:** HCF receiver bottleneck was not `21/100`; joint denominator geometry raises
  admissible source covariance ceiling to `1452/4225`.  Remaining frontier is entirely source-side.
- **Status:** paper proof dependency-closed and formalized; quantitative source covariance ceiling
  remains open.

## Log

- 2026-08-28 — corpus search exposed discarded far-neighbor mass in existing three-center window.
- 2026-08-28 — conjectured exact half-cell minimum; derived nonnegative Bernstein certificate;
  formalized sharpness, finite-packet charge, and 75% receiver.
