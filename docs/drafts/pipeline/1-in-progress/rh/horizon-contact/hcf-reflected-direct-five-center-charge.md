# HCF reflected direct five-center charge

- **ID:** HCF-REFLECT-DIRECT-5C
- **Stage:** 2-fully-proven on paper; Lean modules verified but not umbrella-integrated
- **Type:** THEOREM (paper)
- **Source:** `rh-current-frontier-map.md` · Route HCF
- **Statement:** Keeping the two next integer feature centers raises reflected HCF off-line charge
  by `32/221` per strict-right copy and the 75%-sufficient source ceiling by `4/221`.

## Goal

Improve HCF receiver without changing its source statistic.  Previous direct three-center proof
discarded all outer nonnegative holomorphic-square channels.  Retaining centers at displacement
two raises sufficient source ceiling from `15872/21125` to `15872/21125 + 4/221`.

## Gates

- [x] 0 → 1: well-posed, source statistic unchanged, whole-corpus nonduplication search complete
- [x] 1 → 2: dependency-closed paper proof
- [ ] 2 → 3: direct build and axiom audit pass; shared umbrella integration remains
- [ ] 3 → 4: publication-ready note and Door-2 novelty audit

## Approach

For `|Re z-t| ≤ 5/2` and `|Im z| ≤ 1/2`, direct polynomial monotonicity gives

```text
|1 + (z-t)^2|^2 ≤ 221/4,
|criticalFeature(t,z)|^2 ≥ 16/221.
```

Global holomorphic-sector coercivity retains half, so each of centers `t-2` and `t+2` contributes
at least `8/221`.  Add this `16/221` to direct three-center charge `63488/21125`, then apply
critical-line reflection to double both base and gain.  With `N=N0+2 card(S)`, budget ceiling
`(15872/21125 + 4/221)N` forces `card(S)≤N/8` and hence `3N/4≤N0`.

## Lean status

- `HedenmalmCriticalFeatureReflectedPairDirectFiveCenterCharge.lean`: local denominator bound,
  five-center charge, reflected finite-packet bound, exact 75% receiver.
- `HedenmalmCriticalFeatureReflectedPairDirectFiveCenterCanonicalTransfer.lean`: exact equivalence
  with zero-independent pole--Gamma Plemelj covariance and connectors from regular finite source
  majorants at new constant.
- Direct builds pass. `#print axioms` reports only `propext`, `Classical.choice`, `Quot.sound`.
- Global lint is red on many concurrently unintegrated umbrella modules, including these two;
  shared umbrella was intentionally not edited.

## Remaining target

No 75% theorem is claimed.  Required producer is now the source-only ceiling

```text
CriticalFeatureCanonicalAsymptoticUpper
  criticalFeaturePoleGammaPlemeljCovariance
  (15872/21125 + 4/221).
```

Equivalent finite phase-preserving target uses
`criticalFeatureCanonicalRegularPhaseSourcePieceMajorant`.  Corpus search still finds no
quantitative upper bound for the surviving pole--Gamma/thin-contour cancellation.

## Log

- 2026-08-30 — conjectured outer-center gain from unused global sector coercivity; corpus search
  found no five-center theorem; paper proof, Lean receiver, canonical source transfer, builds, and
  axiom audits completed.
