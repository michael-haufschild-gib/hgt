# HB fixed-propagator global rigidity (2026-08-28)

- New module: `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMFixedPropagatorGlobalRigidity.lean`.
- Umbrella: imported in `formal/GaloisForLFunctions/RHTower.lean` immediately after Peierls arbitrary-incidence realization.
- Main theorem: `exists_hbUniversalPeierls_fixedPropagator_unit_BM_incidence_iff_rh (n)`.
- No-go: `not_exists_hbUniversalPeierls_nonzero_fixedPropagator_unit_BM_incidence (n)`.
- Insight: existing fixed universal propagator condition says BM target is constant across all Xi copies. Hardy's unconditional critical-line Xi divisor makes one unit-seed target zero, so constant must be zero. Global zero target forces every copy critical; conversely RH is realized by zero propagator. Thus fixed global incidence is exactly RH, and no nonzero fixed scalar can work unconditionally.
- Verification: direct `lake env lean` passed; targeted `lake build GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFixedPropagatorGlobalRigidity` passed; both axiom audits only `propext`, `Classical.choice`, `Quot.sound`. Global lint only reports unrelated unreachable modules and does not flag this module.
- Cards: `docs/drafts/pipeline/3-formalized/hb-fixed-propagator-global-rigidity.md`; `docs/drafts/pipeline/5-failed/hb-nonzero-fixed-propagator-global-incidence-no-go.md`.
- Frontier map remained read-only.
- Remaining HB burden: literal gauge/constraint/corner-completed augmented source must construct one fixed time-oriented Peierls propagator and prove all-copy incidence. This theorem shows that landing would prove RH immediately.
