# Theta-cusp Hawking modular-superselection endpoint (2026-08-23)

Implemented `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingModularSuperselectionEndpoint.lean` and imported it from `formal/GaloisForLFunctions/RHTower.lean`.

## Exact proved delta

- Defined normalized physical horizon charge
  `thetaCuspHawkingBackreactionHorizonCharge r := portDissipation r / (2 * thetaSource.mass * physicalEnergy r)`.
- Proved `thetaCuspHawkingBackreactionHorizonCharge_eq_im`: charge equals `r.1.im`.
- For every positive-charge two-ended Hawking resonance, proved existence of an actual `XiRightZeroCopy q` with
  `xiSpectralPoint q.1 = -r.1` and
  `xiRightSourceModularCharge q = horizonCharge r`.
- Packaged physical port dissipation plus existing `XiRightSourceModularTypeSuperselectionCertificate q`.
- Proved no finite-Rees-moderate operator family can sew the reflected prime-valuation Hellinger sectors selected by a positive Hawking horizon charge.
- Proved every exact sewing family has norm beyond every inverse Wold-Rees power.
- Defined open producer `ThetaCuspHawkingFiniteReesPartnerRecoverable` and proved it equivalent to RH. Forward direction uses finite-grade obstruction and reflected Hawking resonance; reverse direction is vacuous under RH.

## Scientific status

Unconditional new result is the resonance-charge identification and essential sewing obstruction. Do not claim causal/high-frequency-transparent mirror scattering implies finite Rees grade. Primary literature supports:
- causal, unitary, high-frequency-transparent partially transmitting mirror models and passive/stable impedance (Jaekel-Reynaud, arXiv:quant-ph/0101068 and quant-ph/0101080);
- modular nuclearity/trace-class conditions implying localization/split properties (Buchholz-Lechner, math-ph/0402072; Buchholz-D'Antoni-Longo, math-ph/0603083);
- Gaussian non-Markovianity iff CP-divisibility violation (Torre-Roga-Illuminati, arXiv:1504.00671).

No literature theorem found identifying high-frequency transparency with project-specific finite Rees grade. This is exact open core.

## Hostile tests

- Generic Bogoliubov/modular boosts do not force passivity; persistent partner memory yields non-divisibility only.
- QEI route does not force sign because sharp derivative counterterm permits local negative flux and loses phase.
- Therefore only UV transparency -> finite-grade recovery remains viable, explicitly marked OPEN PRODUCER.

## Verification

- Scratch proof: `lake env lean /tmp/hawking_modular_superselection_check.lean` passed.
- Target module typecheck and emitted build-tree olean passed.
- Axiom audit: only `propext`, `Classical.choice`, `Quot.sound`.
- `git diff --check` passed and module contains no `sorry/admit/axiom/opaque/unsafe`.
- Global `scripts/formal_tools.py lint` reached unrelated shared-worktree umbrella failures for untracked `DeningerDynSysFrobeniusOpenMap` and `HTGeometry.CauchyKernelLineMass`; do not attribute those to this endpoint.

Related: `mem:research/theta_cusp_hawking_modular_boost_endpoint_2026_08_23`, `mem:research/theta_cusp_hawking_backreaction_passivity_endpoint_2026_08_23`, `mem:research/xi_source_modular_type_superselection_law_2026_04_24`.