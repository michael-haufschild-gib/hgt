# Finite-index Haar carriers split modulo polynomial kernels

- **ID:** HAAR-RELATIVE-PONTRYAGIN-SPLITTING
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Parent:** [Finite-index Mautner rigidity](finite-index-mautner-rigidity-for-the-haar-successor.md)
- **Statement:** Every Hermitian finite-index kernel `k` on `Aff(ℚ)` with integer Haar successor admits `k=p+ψ∘slope+Q`, where `p` is positive definite with the same successor, `ψ` is a Hermitian slope kernel, and `Q` has finite column rank and vanishes on both translations and dilations.

## Consequence and missing input

The dilation reading of `k` equals that of `p+ψ∘slope`. If it is continuous at identity, the existing separable-carrier theorem gives infinite index for `p+ψ∘slope`; a finite-rank perturbation cannot remove infinitely many negative directions. Thus this splitting would resolve the finite-index Mautner obstruction while classifying its mixed polynomial component.

The [canonical polynomial correction](../3-formalized/finite-index-periodic-affine-kernels-have-a-zero-axis-polynomial-correction.md) constructs `Q` and proves finite negative index of the bi-integer-invariant remainder. Constructing its positive part `p` and slope part `ψ` remains open. Subtracting an arbitrary positive kernel from a finite-index kernel does not preserve finite negative index.

No paper proof or Lean theorem is claimed. The missing input is a relative decomposition along the normal translation subgroup; arbitrary negative completion features cannot be treated as a group representation.

The [finite affine orbit of period defects](../3-formalized/haar-period-defects-have-a-finite-affine-orbit.md) is formalized from unipotence and the isotropic fixed kernel. It supplies a covariant finite-dimensional correction space.

A [cyclic averaging decomposition](bi-integer-invariant-haar-kernels-split-into-positive-and-slope-parts.md) is proposed for the resulting bi-integer-invariant carrier.

## Uniqueness of the proposed decomposition

The finite-rank term must equal the canonical polynomial correction: finite column rank gives polynomial translation fibres, while the positive Haar and slope terms are integer-invariant. The correction's difference and zero dilation reading determine it uniquely.

After fixing this term, suppose `p+ψ∘slope=p′+ψ′∘slope`. The exact index law applied to `p′=p+(ψ−ψ′)∘slope` makes `ψ−ψ′` positive definite, since `p′` has index zero. Its value at identity is zero because both positive Haar terms have value one there. The positive-kernel norm bound forces `ψ=ψ′`, and hence `p=p′`. Thus existence would give a canonical triple; the monotone-limit construction is the remaining input.
