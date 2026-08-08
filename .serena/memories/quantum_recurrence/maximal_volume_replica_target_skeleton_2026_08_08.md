# Maximal-volume replica target skeleton (2026-08-08)

Persistent goal: prove Brown–Susskind full growth–plateau–recurrence for ordinary time-independent local Hamiltonians, plus permanent locality/Haar separation at maximal complexity.

## Conjecture loop
- C0 compressed occupied-image kernel <= physical pair fidelity: FALSE. Orthogonal full vectors can have parallel projections.
- C1 arbitrary occupied target basis has bounded coefficients: FALSE by arbitrarily ill-conditioned bases.
- C2 maximal-volume target tuple: PROVED. Among all ordered h-tuples of occupied replica targets, maximize |det|. Cramer column replacement yields every target coefficient norm <= 1.
- C3 D-optimal weights can improve h^2 to h but are established design theory; not claimed or formalized.

## Formal theorem
Module:
`formal/GaloisForLFunctions/HTGeometry/MaximalVolumeReplicaTargetSkeletonLaw.lean`

Main results:
- `exists_maxVolumeTargetBasis_coeff_norm_le_one`
- `exists_replicaTarget_maxVolumeSkeleton`
- `replicaTarget_maxVolumeSkeleton_pointwise`
- `measure_completeTargetCapture_le_maxVolumeSkeletonMoments`
- `measure_completeTargetCapture_le_hilbert_sq_mul_fixedMoment`

For independently fixed measurable return set R, finite source measure mu, positive threshold a, replica order r>0:
[
mu(E_a) <= mu(R) + h_r a^{-r} sum_{j=1}^{h_r} M_r(z_j),
]
where selected z_j are actual occupied endpoints and moments are integrated against mu restricted to R^c. If each moment <= M_r:
[
mu(E_a) <= mu(R) + h_r^2 a^{-r} M_r.
]
All source fibre sheets remain in original restricted measure. Circuit-description cardinality disappears.

## Verification
- direct `lake env lean GaloisForLFunctions/HTGeometry/MaximalVolumeReplicaTargetSkeletonLaw.lean`: PASS.
- final `lake build GaloisForLFunctions.HTGeometry.MaximalVolumeReplicaTargetSkeletonLaw`: PASS, 8669 jobs.
- axioms for five capstones: only propext, Classical.choice, Quot.sound.
- forbidden-token scan: PASS.
- umbrella import in `formal/GaloisForLFunctions/HTGeometry.lean`.
- global lint has only unrelated unwired RHTower.ProlateCanonicalSeparationLimit and RHTower.XiMassCriticalCenteredCosineCone.

Card:
`docs/drafts/pipeline/3-formalized/maximal-volume-replica-target-skeleton-law.md`
Master log updated:
`docs/drafts/pipeline/1-in-progress/static-local-complexity-law.md`

## Honest frontier
This is an unconditional representation/union advance, not Brown–Susskind closure. Classical max-volume/Cramer algebra is not novelty. Targeted collision search found no exact recurrence/complexity composition, but priority remains unverified. Remaining ordinary-local-Hamiltonian core: prove growing-replica fixed-endpoint moments for selected physical endpoints, plus a small target-independent return tail, strong enough to beat h_r^2. Brown–Freedman–Lin–Susskind explicitly leave purely local Hamiltonian dynamics without continuously injected randomness as open.
