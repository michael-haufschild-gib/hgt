# Card: observer-visible-local-time-dimension-obstruction — Lean formalization

Card: `docs/drafts/pipeline/2-fully-proven/observer-visible-local-time-dimension-obstruction.md`
(now marked Stage 3 / `[LEAN-PROVED]` in its header; file still physically in
`2-fully-proven/` — move it once the last remark below is closed.)

## Pre-existing
`HTGeometry/ObserverVisibleLocalTimeDimension.lean` (namespace `QuantumAlg`):
QFI Gram factorization, `qfim_rank_eq_centeredRealification_rank`,
`centeredRealification_mulVec_eq_zero_iff_eigenvector`.

## Built in this pass (all unconditional; axioms = propext/Classical.choice/Quot.sound)

1. `HTGeometry/ObserverInvisibleRayPreservation.lean` — eqs (3),(4):
   `exp_mulVec_of_eigenvector`, `unitaryEvolution_mulVec_of_eigenvector`,
   `unitaryEvolution_generatorCombination_mulVec_of_invisible`,
   `exists_unit_phase_unitaryEvolution_of_centered_eq_zero`,
   `finrank_ker_centeredRealification_add_rank`, `centeredLinear`.
2. `HTGeometry/FiniteSupportCounting.lean` — `card_configSupport_card_eq`,
   `card_configSupport_pos_le`.
3. `HTGeometry/FiniteQuditHermitianUnit.lean` — local Hermitian basis
   `quditHermUnit` ((0,0)=identity, rest traceless) + `single_eq_sum_quditUnitCoeff`.
4. `HTGeometry/FiniteQuditHermitianStringBasis.lean` — `quditStringOf`,
   `quditString`, `quditStringOf_sum`, `span_quditString_eq_top`,
   `linearIndependent_quditString`, `linearIndependent_real_quditString`,
   `QLocalStringLabel`, `card_QLocalStringLabel`.
5. `HTGeometry/ProductStateObserverVisibleRank.lean` — eqs (13)–(17):
   `quditString_mulVec_vacuum`, `centered_quditString_vacuum`,
   `map_qLocalDictionary`, `finrank_map_qLocalDictionary` (= 2N),
   `finrank_qLocalDictionary` (= m), `finrank_ker_add_finrank_map_qLocalDictionary`,
   qubit corollaries.
6. `HTGeometry/ObserverKernelTubeVolume.lean` — `exponent_le_of_forall_rpow_le`,
   `exponent_le_natCast_of_forall_le`, `measure_annulus`, `measure_annulusTube`.
7. `HTGeometry/GaussianSmallBallLowerBound.lean` — `gaussianDensityFloor`,
   `measure_pi_gaussian_closedBall_lower`,
   `measure_pi_gaussian_transverse_ball_lower`.
8. `HTGeometry/ObserverInvisibleTubeShortcut.lean` — eqs (6),(7),(8),(10):
   `norm_unitaryEvolution_mulVec_sub_le`, `RayClose`,
   `rayClose_of_transverse_small`, `measure_rayClose_ge_annulusTube`,
   `measure_rayClose_ge_gaussian_smallBall`, `exponent_le_visible_of_upper_law`.

All eight wired into `GaloisForLFunctions/HTGeometry.lean`.

## Still open (last card remark)
Card line ~220: "The same rank holds for every product state, by local change of
basis."  Plan: (a) local basis property of `quditHermUnit` over ℂ and real
coordinates for Hermitian matrices; (b) `trace (quditHermUnit p) = if p = 0 then D
else 0`; (c) `quditStringOf M * quditStringOf N = quditStringOf (M*N)` and
`(quditStringOf M)ᴴ = quditStringOf Mᴴ`; (d) conjugating a string by a product
unitary lands in the real span of strings with the SAME support, so the
dictionary is local-unitary invariant; (e) rank transports.

## Note
Another session is concurrently editing this repo (`RHTower/GibbsScaleContraction.lean`,
`HTGeometry/MatrixCompound.lean` appeared mid-session; `formal_tools.py lint`
reports MatrixCompound unreachable from its umbrella — not ours, do not touch).
