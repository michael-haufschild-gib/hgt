# HB phase-blind threshold-spectrum no-go (2026-08-31)

Qualifying HB route-class kill. Hardest current HB chain tested: literal Einstein--Teukolsky source -> completed continuum plus threshold atom -> radiative `++` extinction -> fixed-clock covariance -> full cokernel extinction -> RH.

First conjecture using FE-reflection parity failed because the forced AIME threshold counterterm is FE-shadow invariant. Pivot from corpus to seed half-turn phase parity succeeded.

New theorem: arbitrary strictly damped finite-variation spectra and arbitrary `L¹` real-axis continuum transients may differ completely between seed phases `A` and `-A`. If both completed pole numerators asymptotically cancel, their threshold atoms satisfy the exact jump law
`zeroMode(-A) - zeroMode(A) = 2 * d4FundamentalQNMCrossBranchAIMENumerator A ...`.
Because AIME is nonzero for every `A != 0` on every Xi copy, one source-independent/half-turn-even threshold atom cannot cancel both sectors.

Lean module: `GaloisForLFunctions.RHTower.ThetaCuspHawkingAIMEPhaseBlindThresholdSpectrumNoGo`.
Closed capstone: `RHTower.d4BMPassivePeripheralSpectralPhaseBlindThresholdCancellationRouteKilled`.
Wired in `formal/GaloisForLFunctions/RHTower.lean`.

Positive survivor: successful regular zero-mode completion must carry the forced odd cubic phase charge; adding arbitrary phase-blind zero-frequency mass is insufficient. Singular non-Rajchman and infinite-variation spectra remain.

Targeted build passed 11406/11406. Axiom audit only `propext`, `Classical.choice`, `Quot.sound`. Global lint only has unrelated concurrent unwired modules.

Docs: `docs/drafts/pipeline/3-formalized/hb-phase-blind-threshold-spectrum-no-go.md`; failed card `docs/drafts/pipeline/5-failed/hb-source-independent-phase-blind-threshold-spectrum.md`.