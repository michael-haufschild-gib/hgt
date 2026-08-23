# Claim trace: persistent phase geometry of quantum recurrence

Date: 2026-08-23

Scope: internal verification ledger. Publication manuscript must not mention this file, Lean, HGT, or repository terminology.

## Main manuscript claims

| Manuscript claim | Closed declaration | Source |
|---|---|---|
| Anchored temporal rank plus balanced relation rank equals `D - 1` | `anchoredTemporalRank_add_relationRank` | `formal/GaloisForLFunctions/HTGeometry/AnchoredProjectiveRecurrenceConservationLaw.lean:122` |
| Detuning-map kernel and range descriptions used in Law 1 | `projectiveEnergyDetuning_ker_eq_relationSpace`; `projectiveEnergyDetuning_range_eq_anchoredGapSubspace` | `formal/GaloisForLFunctions/HTGeometry/UniversalProjectiveRecurrenceCapstoneLaw.lean:74`; `formal/GaloisForLFunctions/HTGeometry/AnchoredProjectiveRecurrenceConservationLaw.lean:78` |
| Non-VWA vector has exact logarithmic first-hit exponent `d` | `tendsto_log_firstHit_div_log` | `formal/GaloisForLFunctions/HTGeometry/FirstHitExponentLaw.lean:213` |
| Dirichlet first-hit upper bound | `firstHit_le` | `formal/GaloisForLFunctions/HTGeometry/SimultaneousDirichlet.lean:167` |
| Exact survival-fidelity replica expansion | `finiteSpectralSurvivalFidelity_pow_expansion` | `formal/GaloisForLFunctions/HTGeometry/ReplicaCollisionExtremality.lean:181` |
| Long-time moment tends to collision mass | `finiteSpectralSurvivalFidelityMean_tendsto_collisionMass` | `formal/GaloisForLFunctions/HTGeometry/ReplicaCollisionExtremality.lean` |
| All-order floor equality iff maximal projective rank | `all_fidelityReplicaCollisionMass_eq_floor_iff` | `formal/GaloisForLFunctions/HTGeometry/ReplicaCollisionExtremality.lean:619` |
| All long-time survival moments tend to floor iff maximal projective rank | `all_finiteSpectralSurvivalFidelityMean_tendsto_floor_iff` | `formal/GaloisForLFunctions/HTGeometry/ReplicaCollisionExtremality.lean:638` |
| Exact full traceless onsite-plus-edge Pauli path family | `ChainLabel`; `chainPauliFin`; `reindexFin_mem_span_range_chainPauliFin` | `formal/GaloisForLFunctions/HTGeometry/ChainPauliFinFamily.lean:30`; same file lines 40 and 80 |
| Pauli path escapes every nonzero balanced real spectral relation | `chainPauliFin_spectrumEscapesRealRelations` | `formal/GaloisForLFunctions/HTGeometry/ChainPauliFinEscape.lean:39` |
| Linear homogeneous escape implies affine escape | `SpectrumEscapesRealRelations.linearFamily_toAffine` | `formal/GaloisForLFunctions/HTGeometry/LinearSpectrumAffineEscape.lean:16` |
| Every-chart same-Hamiltonian qubit-path capstone: maximal rank, `2^n-1` and `2^n-2` exponents, all collision and moment floors | `qubitPath_everyChart_sameDraw_recurrenceCollisionLaw` | `formal/GaloisForLFunctions/HTGeometry/QubitPathRecurrenceCollisionCapstone.lean:122` |
| Non-maximal Pauli-path set is Lebesgue null | `volume_notMaximallyProjective_chain_eq_zero` | `formal/GaloisForLFunctions/HTGeometry/PathShellProjectiveGenericity.lean:80` |
| Traceless nearest-neighbour qudit path maximal set is dense, residual, and full measure | `exists_uniformQuditPathTracelessLocalHamiltonianMaximalSet_dense_residual_fullMeasure` | `formal/GaloisForLFunctions/HTGeometry/NearestNeighborQuditPathGenericityLaw.lean:115` |
| Maximally projective spectrum has exact anchored chord-return density | `maximallyProjectiveEnergy_anchoredProjectiveReturnFrequency` | `formal/GaloisForLFunctions/HTGeometry/AnchoredProjectiveReturnDensityLaw.lean:400` |
| At least three maximally projective levels have no nonzero exact anchored return | `MaximallyProjectiveEnergy.no_nonzeroExactAnchoredReturn` | `formal/GaloisForLFunctions/HTGeometry/AnchoredProjectiveReturnDensityLaw.lean:426` |
| Qudit-path completed density vanishes with exact Hilbert rate and double-log limit | `thermodynamicProjectiveRecurrenceExtinctionLaw` | `formal/GaloisForLFunctions/HTGeometry/ThermodynamicProjectiveRecurrenceExtinctionLaw.lean:209` |

## Quantifier audit

- Main qubit theorem is every nonempty preconnected open simple-spectrum chart, almost every coefficient in that chart.
- One coefficient draw simultaneously satisfies maximal projectivity, both first-hit limits, all positive weights, and all replica orders.
- Stroboscopic exponent is `D - 1`; winding exponent is first-gap-clock normalized and is `D - 2`.
- Manuscript does not upgrade winding theorem to unrestricted continuous-time first-return distribution.
- Thermodynamic statement takes completed-time limit at fixed finite size before size limit.
- Qudit theorem claims same-Hamiltonian rank/collision consequences only through universal maximal-projectivity equivalences; it does not claim qudit same-draw metric capstone.

## Closure audit

- `lake env lean GaloisForLFunctions/HTGeometry/QubitPathRecurrenceCollisionCapstone.lean`: passed.
- `lake build GaloisForLFunctions.HTGeometry.QubitPathRecurrenceCollisionCapstone`: passed; targeted module only, no umbrella build.
- Axiom audit for every-chart capstone, existence capstone, and linear affine bridge: only `propext`, `Classical.choice`, `Quot.sound`.
- No `sorry`, `admit`, custom `axiom`, `opaque`, or `unsafe` declaration in two new modules.
- Project-wide lint has unrelated pre-existing reachability failures in RHTower modules; no manuscript claim depends on treating that global lint as clean.
