# PW-B source-amplitude-uniform incidence test

- **Chain:** literal two-event CTP → source-faithful oriented optical incidence → fixed-grade magnitude/extinction → RH.
- **Hard obstacle:** establish incidence without suppressing cap/lift or choosing a fitted phase/normalization.
- **Corpus basis:** `fullCausalSourcePair_amplitude_biquadratic`, `pwb_fullCircleCrossBranch_eq_fullCausalSourcePair`, `weakSourceFlux_eq`, `weakSourceFlux_pair`, `pwb_weakSourceMass_pos`, and critical-fibre CTP cancellation.

**Lean-proved obstruction:** For the actual completed CTP source and the weak response to the scaled quadratic forcing, CTP scales as `a⁴`; weak mass and flux each scale as `‖a‖⁴`, so crossed optical flux scales as `‖a‖⁸`. Fixed nonzero real calibration of oriented CTP to crossed flux at both `a=1,2` forces `Re ρ=1/2` by strict source mass and nonzero divisor ordinate. With unit calibration, the two incidences hold **iff** `Re ρ=1/2`. Thus a purported amplitude-uniform incidence is already RH-strength, not a general homogeneity identity; this kills the amplitude-uniform *off-line identity* subroute, not the possibility of deriving RH from an independently proved incidence.

**Positive survivor / open:** Source-faithful scaling law is exact. A source identity intended off-line must instead derive fixed-amplitude incidence or nonlinear amplitude-dependent normalization/phase frame from ordered Peierls and weak optical sources, then establish outer receiver limit. Neither is proved here; PW-B remains active. Lean: `ThetaCuspHawkingBMPWAmplitudeIncidenceNoGo.lean` (direct check and exact-module `lake --old build` passed).
