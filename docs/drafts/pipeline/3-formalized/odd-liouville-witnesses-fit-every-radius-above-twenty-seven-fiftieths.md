# Odd Liouville witnesses above radius 27/50

- **ID:** odd-liouville-witnesses-fit-every-radius-above-twenty-seven-fiftieths
- **Stage:** 3-formalized
- **Statement:** Every radius `r>27/50` admits a smooth compactly supported
  odd test in `[-r,r]` with positive square mass, zeta energy exceeding
  `mass/25`, and Liouville energy below `−3 mass/10`. The corresponding
  Liouville ground energy is therefore strictly below `−3/10`.

## Proof

The existing cubic-quintic test is supported in `[-27/50,27/50]` and has
both strict energy inequalities. Its even mollifications preserve oddness;
their square masses and both energies converge to those of the original
test. Their support expands by `1/(4(k+1))`, which tends to zero. Choose one
index satisfying both strict inequalities, positive mass, and support
expansion below `r−27/50`. The existing narrow-support condition below
`log(3)/2` retains the exact first-prime Liouville identity.

This sharpens the published radius `23/40` without changing either margin.
No claim is made at the limiting radius `27/50`.

## Verification

`SelectivePositivityAndThresholdLaws/TwoPrimeCatalanSeparationAndContinuumTowerObstruction`
passed its direct Lean check. Caps:
`exists_smooth_odd_zeta_pos_liouville_neg_of_gt_twentySevenFiftieths` and
`liouvilleWindowGroundEigenvalue_lt_neg_threeTenths_of_gt_twentySevenFiftieths`.
Both transitive axiom audits contain only `propext`, `Classical.choice`,
and `Quot.sound`. Existing umbrella import includes the extended leaf.
