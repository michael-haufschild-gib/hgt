# Replica-projector frame bridge (2026-08-14)

## Result
Added `formal/GaloisForLFunctions/HTGeometry/StaticShortcutReplicaProjectorFrameLaw.lean` and wired it into `formal/GaloisForLFunctions/HTGeometry.lean`.

For normalized pure states, the Euclidean inner product of vectorized rank-one projector coordinates for r tensor replicas is exactly replica fidelity:
[
\langle \operatorname{Proj}(\psi^{\otimes r}),\operatorname{Proj}(\phi^{\otimes r})\rangle_{\mathbb R}
= |\langle\psi,\phi\rangle|^{2r}
= \operatorname{Fidelity}(\psi,\phi)^r \ge 0.
]
Consequently the abstract finite preparation frame energy is exactly the complete pair-average replica fidelity, retaining every ordered pair and its sheet multiplicity:
[
F_r = |C|^{-2}\sum_{c,d\in C}\operatorname{Fidelity}(y_c,y_d)^r.
]

## Lean declarations
- `finitePureProjectorCoordinate`
- `finitePureProjectorEuclidean`
- `inner_finitePureProjectorEuclidean`
- `inner_finitePureProjectorEuclidean_tensorPower`
- `real_inner_finitePureProjectorEuclidean_tensorPower`
- `finitePreparationFrameEnergy_replicaProjector_eq_averageFidelity`
- `real_inner_finitePureProjectorEuclidean_tensorPower_nonneg`

## Verification
The exact combined sources were copied to `/tmp/hgt_static_replica_projector_combined.lean` and checked with `lake env lean /tmp/hgt_static_replica_projector_combined.lean`; exit 0. Axiom audit for the key theorems reports only `propext`, `Classical.choice`, and `Quot.sound`. Forbidden-token scan is empty. No project build was used. Scratch files were removed after verification.

## Frontier meaning
This retires minimum endpoint separation and minimum spectral gap as the target-side invariant. The exact invariant is occupied-image average replica fidelity/frame energy. It also discharges the nonnegative-overlap premise automatically for pure-state projector targets.

It does **not** prove Brown–Susskind onset. Remaining hard estimates are:
1. return/carrier-excised occupied-image frame energy of order inverse intrinsic capacity at growing replica;
2. quenched centralizer-centered recurrence-energy control for ordinary one-draw static local Hamiltonians.

Related memory: `mem:quantum_recurrence/observer_spectral_frame_energy_reciprocity_2026_08_14`.