# Quenched replica incidence–covariance advance, 2026-08-07

## Conjecture loop
- Raw coarea mass remains circular.
- Raw observer Jacobian remains replica-compensated.
- Rank times worst source eigenmode is true but leaves a hard supremum.
- Survivor: compressed quenched covariance collision on occupied return-removed replica target span.

## Proved law
Let S_r be span of return-removed target r-fold tensors, h_r=dim S_r, q_r(x)=||Proj_Sr psi(x)^tensor r||², and C_r the quenched covariance matrix of coordinates in a fixed ON basis of S_r. For complete target capture E_a at threshold a>0:

(a^r μ(E_a))² ≤ (∫q_r dμ)² ≤ h_r * Σ_ij ||(C_r)_ij||².

The complete union is handled before squaring. Source sheets remain in covariance integrals. Target span extensionality, duplicate labels, and exact-return zero residual invariance are Lean-proved on both event and RHS where applicable.

## Files
- Lean: formal/GaloisForLFunctions/HTGeometry/QuenchedReplicaIncidenceCovarianceLaw.lean
- Card: docs/drafts/pipeline/3-formalized/quenched-replica-incidence-covariance-law.md
- Logs appended to oriented-no-shortcut-without-return-law.md and static-local-complexity-law.md
- Umbrella: HTGeometry import present

## Verification
- lake env lean module PASS
- lake build GaloisForLFunctions.HTGeometry.QuenchedReplicaIncidenceCovarianceLaw PASS, 8657 jobs
- Axioms only propext, Classical.choice, Quot.sound
- Global lint reaches new module and reports no local error; global lint red only on unrelated concurrent unwired RHTower Prolate/Slepian modules.
- No stale Lean/lake process from this agent.

## Exact remaining frontier
Prove growing-r decay of replicaTargetIncidenceCollision for ordinary fixed-q Gaussian static local Hamiltonians, strong enough to beat occupied shallow-circuit Hilbert growth. This is the reduced O4 input; Brown–Susskind remains open.