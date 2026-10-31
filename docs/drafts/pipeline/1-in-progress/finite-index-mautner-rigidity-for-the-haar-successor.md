# Finite-index Mautner rigidity for the Haar successor

- **ID:** HAAR-FINITE-INDEX-MAUTNER
- **Stage:** 1-in-progress
- **Type:** THEOREM (rational obstruction formalized; positive survivor open)
- **Parent:** [O5](weil-positivity-five-structural-mechanisms.md)
- **Statement:** A Hermitian kernel on `Aff(ℚ)` with nonzero Haar successor `c·1_ℤ` and dilation correlation continuous at the identity has infinite negative index.

## Mathematical issue

The rational-affine statement is proved for every nonzero scalar by `negIndex_eq_top_of_nonzero_haar_continuous_dilation` in `AdelicKreinGeometry/Haar/ScaledHaarObstruction.lean`, with a direct Lean audit and standard axiom closure. It requires no Hecke support or integer-invariance premise. Weil's scalar dilation correlation has the required continuity.

For a Haar successor, all vectors `v_{b+n}−v_b`, with `b∈ℚ` and `n∈ℤ`, span a totally isotropic translation-invariant space. Finite negative index bounds its dimension in the nondegenerate kernel quotient. The analogous radical of the dilation-cyclic space is also finite-dimensional. These are the only directions invisible to the positive-kernel Mautner argument.

The canonical polynomial correction removes the finite period defect without changing either axis reading. Cyclic averaging then excludes a finite-index bi-integer-invariant remainder with continuous dilation reading. The obstruction is formalized on the full and positive-slope rational affine groups and on `ℚ⁺ ⋉ (ℝ × 𝔸_f)`, where rational dilations act on both components. The actual finite-adelic Haar overlap integral is identified with the integral-subring indicator. The positive structural decomposition remains unfinished.

Without dilation continuity, Haar successors admit finite nonzero index: [the explicit state `haarState−4(log|affSlope|/log 2)²`](../3-formalized/the-haar-successor-admits-one-negative-square.md) has index exactly one. Its rank-one completion, Haar reading, failure of Hecke support, and dilation discontinuity are formalized.

## Remaining structural decomposition

The corpus's finite-rank correction theorem gives functions on the group, not a covariant negative representation. For bounded kernels, [Kissin–Shulman–Turovskii, Theorem 5.1](https://arxiv.org/pdf/2005.02745) gives a difference of positive-definite functions with a finite-dimensional negative part. Its global boundedness assumption has not been deduced from the two prescribed readings. The [connected-group extension theory of Kissin–Shulman](https://repository.londonmet.ac.uk/8622/1/COHOMOLOGY%20and%20EXTENSIONS%20SUBMITTED%20EUROPEAN%20J.%20MATH..pdf) also requires topology absent from the abstract rational affine kernel. Neither theorem closes the mixed-coefficient gap.

[Finite rational affine unitary rigidity](../3-formalized/finite-rational-affine-unitary-representations-kill-translations.md) is formalized: every finite-dimensional complex affine representation has translation trace equal to its dimension, and every unitary one factors through dilations, without continuity. Thus a covariant finite-dimensional negative unitary component is translation-blind; covariance itself remains unproved.

Without unitarity, [translations are unipotent with exponent bounded by the dimension](../3-formalized/finite-rational-affine-representations-have-unipotent-translations.md). This governs any finite-dimensional invariant component but does not produce one.

[Haar addition preserves the index of a slope kernel](../3-formalized/haar-addition-preserves-the-index-of-a-slope-kernel.md): `κ(haarState+ψ∘slope)=κ(ψ)` for every Hermitian `ψ`, including infinite index. The same exact law holds for [every positive affine carrier with integer successor](../3-formalized/positive-haar-carriers-preserve-the-index-of-slope-corrections.md), without Hecke support. Translation averages remove the positive contribution while preserving the slope Gram matrix. The [formalized continuous-dilation obstruction](../3-formalized/separable-haar-carriers-cannot-have-continuous-dilations.md) forces infinite index throughout this class, including when the dilation reading is Weil's spline correlation.

[Mixed quadratic perturbation](../3-formalized/mixed-polynomial-affine-perturbations-preserve-both-axis-readings.md) proves that this separable class is incomplete: `haarState+i(1−a⁻²)b²` has index exactly three, preserves both Haar axis readings, and is unbounded on a fixed slope. It cannot be a positive affine kernel plus a slope kernel. Its unchanged dilation reading remains discontinuous. The [rank law for axis-invisible kernels](../3-formalized/axis-invisible-finite-index-kernels-have-finite-rank.md) proves column-space dimension at most the square of the index.

The [relative splitting conjecture](finite-index-haar-carriers-split-modulo-polynomial-kernels.md) asks whether adding a finite-rank zero-axis term makes the separable class exhaustive. Existence of that splitting remains open.

[Isotropic translation unipotence](../3-formalized/isotropic-translation-defects-are-unipotent.md) is formalized via the canonical column form and dilation orbits of joint characters. It controls the translation-period radical without assuming dilation invariance.

The [full affine orbit of period defects](../3-formalized/haar-period-defects-have-a-finite-affine-orbit.md) is formalized: it is invariant and has dimension at most `r²` when the kernel has negative index at most `r`. Its [zero-axis polynomial correction](../3-formalized/finite-index-periodic-affine-kernels-have-a-zero-axis-polynomial-correction.md) is formalized, including uniqueness, Hermitian symmetry, both zero-axis identities, and finite index of the bi-integer-invariant remainder.

The [finite cyclic averaging argument](cyclic-haar-averages-force-infinite-index-at-continuous-dilations.md) is formalized: nonnegative moving subspaces give a cyclic Hecke bound, while fixed-part Gram matrices converge to `J−I`. It proves the normalized obstruction independently of the positive-plus-slope decomposition. The latter remains the positive survivor to establish.
