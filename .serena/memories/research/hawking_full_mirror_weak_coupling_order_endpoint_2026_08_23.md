# Hawking full-mirror weak-coupling/order endpoint (2026-08-23)

New module: `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingFullMirrorWeakCouplingOrderEndpoint.lean`; imported by `formal/GaloisForLFunctions/RHTower.lean`.

Exact source-faithful chain now Lean-proved:
1. Dominated differentiation of genuine eikonal Davies--Fulling amplitude at coupling zero:
   `hasDerivAt_thetaCuspHawkingEikonalFourier_zero`.
2. Full mirror tangent equals source-derived tilted Born numerator:
   `hasDerivAt_thetaCuspHawkingFullMirrorAmplitude_zero`.
3. Coupling-normalized full-mirror probability tends to Born probability:
   `tendsto_thetaCuspHawkingFullMirrorBornScaledPairProbability`.
4. Fixed-total-frequency shell of full-mirror derivative equals existing tilted Hawking shell:
   `thetaCuspHawkingFullMirrorWeakCouplingRightEnergyShellDensity_eq`.
5. Existing KMS width is positive thermal factor times this full-mirror tangent shell:
   `thetaCuspHawkingKMSResonanceWidth_eq_fullMirrorWeakCouplingShell`.
6. Actual Davies resonance sector mixes iff full-mirror tangent shell is positive:
   `thetaCuspHawkingDaviesSectorMixes_iff_fullMirrorWeakCouplingShell_pos`.
7. Global tangent-shell mixing is RH-equivalent:
   `riemannHypothesis_iff_thetaCuspHawkingFullMirrorWeakCouplingShellMixing`.

New canonical invariant:
`thetaCuspHawkingFullMirrorSectorCouplingOrder a w ha` is least positive nonzero eikonal power-moment order. Existing eventual nonvanishing makes it finite unconditionally. Lower positive jets vanish; order=1 iff principal Xi/Born moment is nonzero. Global no-order-jump law is RH-equivalent:
`riemannHypothesis_iff_thetaCuspHawkingFullMirrorNoOrderJump`.

Interpretation:
- [LEAN-PROVED] Full scattering selects Born/Davies only in weak-coupling tangent scaling.
- [LEAN-PROVED] Every exact tilted sector couples at some finite order.
- [FALSIFIED] Exact full finite-coupling mirror equals canonical sectorwise Cayley completion.
- [FALSIFIED as RH producer] All-order mixing: unconditional.
- Remaining RH-bearing producer is an upstream source/dynamical law forcing least order 1 in every noncentral tilt, equivalently strict positivity of every full-mirror weak-coupling shell. KMS detailed balance supplies only a positive multiplier and cannot remove Xi dark shells.

Verification:
- Direct `lake env lean` compile passed.
- Targeted olean build passed.
- `#print axioms` on ten core declarations: only `propext`, `Classical.choice`, `Quot.sound`.
- `git diff --check` passed.
- Formal lint still reports ten unrelated pre-existing umbrella-unreachable modules; new module is wired and absent from failures.
- `scripts/formal_tools.py research "full mirror weak coupling shell mixing no order jump"` finds all new declarations.

Endpoint ledger `docs/reports/endpoints.md` updated locally (directory is gitignored): total 1,769; two new operator/dynamics equivalences; Cayley-selection route marked no-go.
