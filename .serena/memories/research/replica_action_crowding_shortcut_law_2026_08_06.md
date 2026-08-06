# Replica-action crowding shortcut law (2026-08-06)

Formalized a replacement for global minimum replica-action resolution.

Modules:
- `formal/GaloisForLFunctions/HTGeometry/ReplicaActionCrowdingShortcutLaw.lean`
- `formal/GaloisForLFunctions/RHTower/DirectAdaptiveStaticChoiCrowdingLaw.lean`

Core invariant: `replicaActionCrowdingDegree energy r δ`, maximum number of replica multiplicity vectors within nonzero action distance `< δ` of one fixed vector. Symmetric weighted Schur/AM-GM gives near-action mass <= crowding degree * permutation floor.

Generic Gaussian/uniform moment and capture-measure laws are proved. Under maximal projective spectrum, direct normalized Choi collision and floor are each <= `r! d^-r`. Final adaptive padded-circuit theorems:
- `gaussian_directAdaptivePaddedCircuitShortcut_crowdingProbability_le`
- `uniform_directAdaptivePaddedCircuitShortcut_crowdingProbability_le`

Bound: circuit entropy times `((1+κ_r(δ))*r!*d^-r + window remainder)`. No smallest nonzero spectral gap. Isolated arbitrarily small action costs one floor unit.

Verification: targeted `lake env lean` passed; final `lake build GaloisForLFunctions.RHTower.DirectAdaptiveStaticChoiCrowdingLaw` passed; axiom audit only `propext`, `Classical.choice`, `Quot.sound`. Global lint failed only unrelated umbrella omissions `CompoundHomothety` and `MultipleSineFaceIteration`. No task-owned stale Lean process.

Pipeline card: `docs/drafts/pipeline/3-formalized/replica-action-crowding-shortcut-law.md`. Master log updated.

Hostile status: real finite-window strengthening, does not close O4. Remaining finite-window frontier is quenched/local-Hamiltonian control of `κ_r(δ)` at growing replica order; fixed-time coefficient-space anti-concentration remains separate. External quick search found adjacent higher-SFF/random-dynamics/static-ramp work but no exact crowding synthesis; novelty remains unverified.