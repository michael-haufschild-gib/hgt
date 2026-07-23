# Sonin logarithmic pinching projective-ray universality law

## Status

Fully proven on paper; Lean 4 formalization in progress.

## Theorem-first source

- `soninLogPinching_zeroQFI_multiplicativeDomain_compression`: invariant pinching annihilates the
  hidden-clock QFI, all Ward values, the star-Kadison defect, and the compressed constraint.
- `soninLogClock_erasedPureStateQuantumFisherValue_eq_zero_iff_observedPhysical`: zero hidden-clock
  QFI is equivalent to physicality of the observed vector.
- `soninLogFourierScattering_projectiveAsymmetry_eq_rayDistanceSq_mul_massComplement`: projective
  scattering asymmetry is the exact ray-distance/complement product.
- `soninLogFourierInvariantAverage_apply`: the invariant average is the explicit scattering
  symmetrizer.

All statements act on the same pinched vector `Y ψ`; no model identification is introduced.
Corpus research found no theorem joining the pinching zero-locus certificate to the signed-ray and
projective geometry.

## Universal law

For every Sonin observable and normalized physical state, invariant-sector pinching sends the
observed vector into one common static locus: it remains physical; its QFI, every Ward value,
star-Kadison defect, compressed constraint sandwich, signed-ray distance, and projective scattering
asymmetry all vanish.

## Paper proof

Apply the existing pinching theorem. Its zero-QFI component and the QFI physicality equivalence
show that the observed vector remains physical, hence is fixed by scattering. The explicit
symmetrizer therefore fixes it and annihilates its complementary sector, so signed-ray distance is
zero. The exact homogeneous ray/asymmetry identity then gives zero projective asymmetry. No
numerical computation is used.

## Lean formalization

Module: `GaloisForLFunctions.RHTower.SoninLogPinchingProjectiveRayUniversalityLaw`.

## Novelty audit

Pending literature audit after exact Lean formalization. Corpus audit is negative.
