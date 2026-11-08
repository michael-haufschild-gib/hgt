# Actual elliptic squarefree-divisor cancellation

- **ID:** RIAC-elliptic-squarefree-divisor-cancellation
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** [Curve orientation counts](riac-curve-orientation-square-root.md)

For the actual curve `Y²Z=X³−XZ²` over `F₃`, let `E_n` and `O_n` count
finite sets of closed points of total residue degree `n`, with respectively
even and odd cardinality. Infinity has degree one. These are independently
defined finite arithmetic sets; no Möbius value enters their definitions.

The existing actual-place Euler product and derived Frobenius root bound
suggest the unconditional estimate

`|E_n−O_n| ≤ 8(n+1)²(√3)^n`.

The corresponding degree-prefix target is
`|Σ_(k≤n)(E_k−O_k)| ≤ 24(n+1)²(√3)^n`.

Proof obligations: expand the finite inverse Euler product into these
literal subsets; retain infinity; identify the stabilized product with
`(1−t)(1−3t)/∏_i(1−α_i t)`; apply the proved `|α_i|=√3` bound.
Every degree has finite support by the established residue-degree cutoff.

The finite subset expansion is formalized in
[SquarefreeDivisorCounts.lean](../../../../formal/GaloisForLFunctions/RenormalizedIntersectionArithmeticCounts/SquarefreeDivisorCounts.lean):
`coeff_squarefreeEuler_eq_counts`. Its direct check and both axiom audits
passed. The actual elliptic comparison and inequalities remain under
formalization.

This specializes the general curve programme to a concrete nonzero
square-root-scale signed count. Comparison with the orientation quotient
is separate. No estimate for integer `Σ_p index_p(N)=1−M(N)` follows;
the missing transfer must preserve signed arithmetic incidence and control
the conductor-height error.

Existing inputs:
[actual closed-point Euler product](../../../../formal/GaloisForLFunctions/ArithmeticEffectivityTheory/FiniteFieldEllipticFormalEulerProduct.lean),
[actual rational zeta series](../../../../formal/GaloisForLFunctions/ArithmeticEffectivityTheory/FiniteFieldEllipticZeta.lean),
[coefficient estimates](../../../../formal/GaloisForLFunctions/ArithmeticCompensationTheory/TheReceiverOfACurveIsAdmittedAboveTheZeroWidth.lean).
The finite-field mechanism is classical. [Humphries, §3, equations (5)–(6)](https://arxiv.org/pdf/1209.6087)
identifies the divisor Möbius series with reciprocal zeta. [Cha, §2.1](https://arxiv.org/pdf/1008.4711)
relates polynomial degree losses to repeated reciprocal roots. The intended
contribution here is a dependency-closed realization by actual arithmetic
counts; neither the mechanism nor the finite-field square-root scale is
claimed as new.
