# Actual elliptic squarefree-divisor cancellation

- **ID:** RIAC-elliptic-squarefree-divisor-cancellation
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [Curve orientation counts](../1-in-progress/riac-curve-orientation-square-root.md)
- **Statement:** Actual even/odd squarefree-divisor counts on `Y²Z=X³−XZ²` over `F₃` have square-root-scale signed cancellation.

## Arithmetic counts and bounds

A finite set of actual closed points defines a squarefree divisor.
Its degree is the sum of residue-field degrees; infinity has degree one.
Let `E_n` and `O_n` count degree-`n` divisors with even and odd support.
Every supporting place has degree at most `n`, so the finite cutoff
omits no divisor. Both counts are defined without a Möbius function.

For every `n≥0`,

`|E_n−O_n| ≤ 8(n+1)²(√3)^n`,

`|Σ_(k≤n)(E_k−O_k)| ≤ 24(n+1)²(√3)^n`.

Thus at norm horizon `N=3^n` the loss is quadratic in `log N` times `√N`.
No simplicity or linear-independence assumption on Frobenius roots enters.

## Proof

The finite product `∏_v(1−t^deg(v))` expands into actual squarefree subsets;
its degree-`n` coefficient is `E_n−O_n`. The proved actual-place Euler
product and point-count rationality identify its stabilized series with
`(1−t)(1−3t)/∏_i(1−α_i t)`. The actual curve theorem proves `|α_i|=√3`.
A product-of-geometric-series estimate bounds the denominator inverse by
`(n+1)²(√3)^n`; the two numerator factors cost `2·4=8`.
Finally `Σ_(k≤n)(√3)^k≤3(√3)^n` gives the prefix estimate.

## Formalization

[SquarefreeDivisorCounts.lean](../../../../formal/GaloisForLFunctions/RenormalizedIntersectionArithmeticCounts/SquarefreeDivisorCounts.lean):
`squarefreeEuler_expansion`, `coeff_squarefreeEuler_eq_counts`.

[EllipticSquarefreeCounts.lean](../../../../formal/GaloisForLFunctions/RenormalizedIntersectionArithmeticCounts/EllipticSquarefreeCounts.lean):
`ellipticEulerProduct_eq_inverseRoots`, `norm_coeff_ellipticEulerProduct_le`,
`elliptic_divisor_support_subset`, `mem_ellipticDegreeSubsets_iff`,
`ellipticPlace_product`, `coeff_ellipticEulerProduct_eq_counts`,
`elliptic_signed_divisor_count_bound`, `elliptic_signed_divisor_prefix_bound`.
Direct Lean checks passed; all ten audits use only `propext`,
`Classical.choice`, `Quot.sound`.

## Scope and precedent

The finite-field mechanism is classical: [Humphries, §3, equations (5)–(6)](https://arxiv.org/pdf/1209.6087)
identifies the divisor Möbius series with reciprocal zeta;
[Cha, §2.1](https://arxiv.org/pdf/1008.4711) analyzes polynomial losses from
repeated roots. This contribution realizes the cancellation with actual
finite arithmetic sets and a dependency-closed Lean proof.

The Frobenius orientation-quotient comparison remains separate. No integer
estimate for `Σ_p index_p(N)=1−M(N)` follows. A transfer must preserve
signed arithmetic incidence and control conductor-height errors.
