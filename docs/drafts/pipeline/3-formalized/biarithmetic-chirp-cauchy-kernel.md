# Strict positivity and exact diagonal of the chirp Cauchy kernel

- **ID:** biarithmetic-chirp-cauchy-kernel
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parent:** [Logarithmic chirp tangents](../1-in-progress/biarithmetic-logarithmic-chirp-tangents.md)
- **Statement:** For `α>0`, every finite chirp Cauchy matrix at distinct positive cofactors is positive definite. Every nonzero real packet has positive energy. For `α≠0`, the diagonal is exactly `j^(-2β)`; each real kernel entry is continuous in the unit phase family.

Logarithmic nodes are injective and lie in the right half-plane. The
matrix is a positive scalar multiple of an invertible diagonal congruence
of the corpus's positive-definite Hardy Cauchy matrix. Unit phases leave
amplitude norms unchanged, giving the exact diagonal.

Lean: `BiarithmeticGeometry/ChirpCauchyKernel.lean`.
Audited declarations: `chirpCauchyNode_injective`, `chirpCauchyNode_add_star`,
`chirpCauchyKernel_posDef`, `chirpRealKernel_packet_pos`,
`norm_chirpCauchyAmplitude`, `chirpCauchyKernel_diagonal`,
`chirpRealKernel_diagonal`, and `continuous_chirpRealKernel`.

- [x] Direct check: `lake --old env lean GaloisForLFunctions/BiarithmeticGeometry/ChirpCauchyKernel.lean`.
- [x] All eight transitive audits contain only `propext`, `Classical.choice`, `Quot.sound`.
- [x] Default proof limits; umbrella import wired; umbrella not compiled.

The source covariance asymptotic, actual tangent classification, and
completed source representation remain separate formalization obligations.
