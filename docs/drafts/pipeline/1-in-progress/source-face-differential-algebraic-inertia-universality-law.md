# Source-face differential-algebraic inertia universality law

## Status

In progress — paper proof and Lean source complete; exact check and literature novelty audit pending.

## Theorem-first provenance

- `HTGeometry/SourceRigidificationFaceInertia.lean`
  - `gammaPositivePeriodicModes_linearIndependent`
  - `gammaPositivePeriodicFourierPacket_periodic`
  - `gammaPositivePeriodicFourierPacket_not_periodic_of_im_ne_zero`
- `HTGeometry/ExponentialSumDA.lean`
  - `differentiallyAlgebraic_finset_expSum_general`

## Universal law

Deleting any nonreal source translation creates unit-periodic gauge inertia of every prescribed
finite rank. The complete packet—not only its displayed basis—is differentially algebraic. Every
coefficient packet is fixed by the surviving unit translation, and a packet is fixed by the
deleted nonreal translation only when its coefficient vector is zero.

Hence source-face specialization can create reconstruction ambiguity of unbounded finite rank
while the entire new ambiguity remains in the DA phase; no hypertranscendental direction is born.

## Paper proof

The positive Gamma Fourier modes are linearly independent. Their finite coefficient packet is a
finite sum of exponentials with frequencies `gammaPeriodicFrequency (m+1)`, so the general finite
exponential-sum theorem makes every packet differentially algebraic. Existing translation laws
give unit periodicity, while eigenvalue separation for a nonreal shift proves that simultaneous
periodicity forces every coefficient to vanish.

## Lean status

Source complete in
`formal/GaloisForLFunctions/HTGeometry/SourceFaceDifferentialAlgebraicInertiaUniversalityLaw.lean`.

Direct source check is deferred to final audit because the terminal source-face provenance module
currently lacks a cached `.olean` artifact; no early `lake build` was run.

## Novelty status

Pending post-discovery literature audit. Discovery used Lean statements only; corpus search found
arbitrary-rank gauge birth and finite exponential-sum DA separately, but no classification of the
entire face-created inertia packet as DA.
