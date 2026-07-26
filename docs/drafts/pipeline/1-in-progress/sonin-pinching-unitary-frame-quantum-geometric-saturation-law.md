# Sonin-pinching unitary-frame quantum-geometric saturation law

Status: Stage 2 — dependency-closed paper proof; Lean formalization in progress  
Lean target: `GaloisForLFunctions.RHTower.SoninPinchingUnitaryFrameQuantumGeometricSaturationLaw`  
Novelty: `[NOVELTY UNVERIFIED]`

## Theorem-generated discovery

`SoninPinchingUnitaryFrameProjectiveRayUniversalityLaw` proves that Sonin pinching produces, after
every two-sided unitary frame change, a physical scattering vector pair with exactly zero
projective Gram tangent energy.

The HTGeometry quantum-geometric consumer layer identifies that same projective energy with:

- the quotient-free projective quantum-Fisher numerator;
- the gap between quantum metric area and Berry-curvature area;
- the complex two-vector Gram determinant;
- the dependence classifier for the two channels;
- the negative-square determinant of the pure-state projector tangent.

No corpus theorem applies these consumers to the unitary-frame Sonin pinching locus.

## Statement

For every normalized native Sonin physical state, every pinching observable, and every two-sided
unitary reference frame, the pinched state and its framed scattering image:

1. remain physical;
2. have the same projective Gram energy as the native pinched pair, namely zero;
3. have zero pure-state quantum-Fisher value;
4. saturate the quantum metric--Berry inequality;
5. have zero complex Gram determinant and fail complex two-channel independence;
6. have Hermitian pure-state projector-tangent compression with zero determinant.

## Dependency-closed proof

Apply `soninLogPinching_unitaryFrameProjectiveRayUniversality` for physicality, exact frame
transport, and zero projective energy. Rewrite that zero through
`projectiveGramTangentEnergy_eq_value`,
`quantumMetricAreaValue_eq_projectiveGram_add_berry`,
`det_gram_pair_eq_projectiveGramTangentEnergy`, and
`det_pureStateProjectorTangentCompression_eq_neg_projectiveEnergy_sq`. Use
`quantumMetricArea_eq_berry_iff_not_linearIndependent_pair` for dependence and the existing
Hermitian theorem for the projector tangent.

No computation or extra spectral hypothesis is used.

## Novelty audit

Corpus audit: exact search found Sonin projective-ray vanishing and generic quantum-geometric
consumer identities, but no theorem closes them into a unitary-frame quantum-geometric saturation
certificate.

Literature audit: deferred until exact Lean proof succeeds, per research protocol.

## Lean verification

Pending exact source check and final umbrella audit.
