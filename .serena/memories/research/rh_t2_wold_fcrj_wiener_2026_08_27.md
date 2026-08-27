# RH T2/Wold/FCRJ research, 2026-08-27

Formalized exact fixed-packet FCRJ ultraviolet-tail law.

## New module
`formal/GaloisForLFunctions/RHTower/XiPhysicalPrimeEndpointUltravioletTail.lean`

Public infrastructure:
- `GaloisForLFunctions.HTGeometry.tendsto_weightedTail_invSq`
- `GaloisForLFunctions.HTGeometry.tendsto_cesaro_invSqTail_of_summable`

Physical capstones:
- `RHTower.tendsto_xiPhysicalPrimeLogEndpointCircleMoment_ultravioletTail`
- `RHTower.tendsto_xiPhysicalPrimeLogCharacterAmplitude_ultravioletTail`
- `RHTower.not_tendsto_xiPhysicalPrimeLogCharacterAmplitude_ultravioletTail_zero`

For endpoint moment `U_n`, jump charge `J`, and raw FCRJ amplitude `A_n`:
`N * Σ_{n>N} |U_n|²/n² -> J`, and
`N * Σ_{n>N} |A_n|² -> A² J/(4π²)`.
Every nonempty active packet with `0 < k-m < A` has `J>0`, so scaled tail cannot tend to zero; fixed-packet character energy is exactly order `1/N`, not `o(1/N)`.

Proof uses normalized cumulative `g_n=S_n/n` and exact Abel split:
`tail = -g_M/M + Σ g_(j+1)/j² + Σ [g_(j+1)j/(j+1)]/j²`.
Two weighted tails tend to `J`; boundary tends to `-J`. Generic Lean transfer takes weighted summability; exact physical character Parseval discharges it unconditionally.

Novelty classification: generic Abel implication and Fourier jump theory are classical/REDISCOVERED. Candidate-new content is source-specific physical coefficient and route no-go. Closes fixed-packet high-frequency decay as missing FCRJ/CCM-FU saving. Remaining core: uniform two-parameter convergence for moving prime packets/endpoints, especially phase collisions, plus common-source total-energy upper control.

Wiring/docs:
- imported by `formal/GaloisForLFunctions/RHTower.lean`
- Stage-3 card `docs/drafts/pipeline/3-formalized/fcrj-endpoint-ultraviolet-tail.md`
- appended conjecture loop 59 to `critical-multiplicative-compensated-cancellation-rh.md`
- appended frontier update to `rh-current-frontier-map.md`

Verification:
- direct `lake env lean` passed
- targeted `lake build GaloisForLFunctions.RHTower.XiPhysicalPrimeEndpointUltravioletTail` passed
- `#print axioms` capstones: only `propext`, `Classical.choice`, `Quot.sound`
- `scripts/formal_tools.py lint` passed

Prior same-session results retained:
- `XiHeatCassiniWoldOrbitChargeQuantization.lean`
- `XiHeatCassiniWoldOrbitChargeCompactOpenNoGo.lean`
- `XiPhysicalPrimeEndpointWienerCharge.lean`
