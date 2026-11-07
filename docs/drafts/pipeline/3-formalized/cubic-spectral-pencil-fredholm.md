# The cubic spectral pencil is Fredholm below one

- **ID:** cubic-spectral-pencil-fredholm
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Parent:** [cubic theta residue](../1-in-progress/cubic-theta-residue-and-gauss-coefficients.md)
- **Statement:** The actual completed-energy pencil `T(λ)=Id−(λ+1)M*M` has finite-dimensional kernel, closed range, and finite-dimensional cokernel for every `0≤λ<1`, including `λ=8/9`.

Write `m=‖Mu‖`, `g=‖Gu‖`, `n=‖u‖`, `t=‖T(λ)u‖`, and
`k=‖1_KMu‖`, with `K,C` from [exterior coercivity](cubic-quotient-exterior-coercivity.md).
The actual energy norm gives `n²=m²+g²`. Exterior coercivity gives
`m²≤g²+Ck²`, and Cauchy–Schwarz gives `g²−λm²≤nt`.
Completing a square yields
`n²≤4t²/(1−λ)²+4Ck²/(1−λ)`.

Thus the pair of compact restriction and spectral residual is bounded
below. The corpus theorem
`HTGeometry.cofinalTransducer_of_compact_jointlyBoundedBelow` gives finite
kernel and closed range. The real-parameter pencil is self-adjoint, so
its range is the orthogonal complement of its kernel. Orthogonal
decomposition then makes its cokernel finite-dimensional as well.

Lean: `MetaplecticMobiusDescent/TheCubicSpectralPencilIsFredholm.lean`,
namespace `CubicEisenstein`: `kernelSpectralFormOperator_isFredholm` and
`kernel_theta_spectral_fredholm`. Direct source and transitive audits use only `propext`,
`Classical.choice`, and `Quot.sound`.

[Meromorphic inversion](cubic-meromorphic-resolvent.md),
[initial source matching](cubic-initial-resolvent-matching.md), and the
[nonzero residual eigenvector](cubic-constant-term-nonvanishing.md) are formalized.
Gauss-coefficient identification remains on the parent card.
Spectral estimates adapt OpenAI's
`Eisenstein/FredholmAlternative.lean`; compact-operator closure reuses the
existing local corpus theorem.
