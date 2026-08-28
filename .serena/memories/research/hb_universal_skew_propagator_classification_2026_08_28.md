# HB universal skew-propagator classification (2026-08-28)

Formalized an exact classification and global RH receiver for arbitrary complex-linear skew propagators on the two-dimensional universal Peierls carrier.

Modules:
- `GaloisForLFunctions.RHTower.ThetaCuspHawkingBMUniversalSkewPropagatorClassification`
- `GaloisForLFunctions.RHTower.ThetaCuspHawkingBMUniversalSkewPropagatorGlobalRigidity`

Main theorems:
- `hbUniversalPeierls_skewPropagator_eq_targetScaledRotation`
- `hbUniversalPeierls_skewPropagator_existsUnique_targetScaledRotation`
- `exists_hbUniversalPeierls_fixedSkewPropagator_unit_BM_incidence_iff_rh`
- `not_exists_hbUniversalPeierls_nonzero_fixedSkewPropagator_unit_BM_incidence`

Insight: testing skewness on the coordinate basis forces every endomorphism to matrix `[[0,-T],[T,0]]`, uniquely. Thus arbitrary skew maps add no freedom beyond the earlier scalar family. Any fixed skew propagator matching all unit-seed BM targets exists iff RH, and any such propagator is necessarily zero.

Verification: direct Lean checks and target-specific Lake builds passed for both modules. Axiom audits report only `propext`, `Classical.choice`, and `Quot.sound`. Umbrella imports added. Repository-wide lint reports only unrelated pre-existing unreachable modules.

Cards:
- `docs/drafts/pipeline/3-formalized/hb-universal-skew-propagator-classification.md`
- `docs/drafts/pipeline/5-failed/hb-nonzero-fixed-skew-propagator-global-incidence-no-go.md`

Do not modify `docs/drafts/pipeline/1-in-progress/rh-current-frontier-map.md`; user designated it read-only.