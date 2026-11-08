# Actual elliptic point configurations and signed cancellation

- **ID:** RIAC-elliptic-stable-orientation
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [Curve orientation counts](../1-in-progress/riac-curve-orientation-square-root.md)
- **Statement:** Actual Frobenius-stable point configurations correspond to squarefree divisors; their intrinsic permutation signs satisfy the curve's square-root bound.

On `Y²Z=X³−XZ²` over `F₃`, let `E/F₃` be the actual extension of
degree `n!`. A configuration is a Frobenius-stable subset `T⊆C(E)`
with `|T|=n`. Its orientation index is the sign `ε(T)` of the actual
Frobenius permutation on `T`; neither a Möbius function nor a signed
divisor count enters this definition.

Every stable subset contains each closed-place fibre it meets. A place
occurs over `E` exactly when its residue degree divides `[E:F₃]`, and its
fibre has that many points. Every place in a degree-`n` squarefree divisor
has positive degree at most `n`, hence embeds in `E`. Full point support
and closed-place support are inverse maps. They identify configurations
with actual squarefree divisors of degree `n`.

For any finite invariant partition, a permutation's sign is the product
of its fibre signs. A nonempty transitive fibre of size `d` contributes
`(-1)^(d+1)`, including `d=1`. Actual Frobenius transitivity therefore gives

`ε(T)=(-1)^(|T|+|support(T)|)`.

Writing `E_n,O_n` for the established even/odd squarefree-divisor counts,
the configuration sum `J_n=Σ_T ε(T)` consequently satisfies

`J_n=(-1)^n(E_n−O_n)`,

`|J_n|≤8(n+1)²(√3)^n`.

The [actual divisor estimate](riac-elliptic-squarefree-divisor-cancellation.md)
supplies the last inequality with its curve root bound already proved.
Infinity and every degree-one fibre remain in both comparisons.

Lean sources:
[FibrePermutationSigns.lean](../../../../formal/GaloisForLFunctions/RenormalizedIntersectionArithmeticCounts/FibrePermutationSigns.lean),
[EllipticStableSubsets.lean](../../../../formal/GaloisForLFunctions/RenormalizedIntersectionArithmeticCounts/EllipticStableSubsets.lean).
Main declarations: `sign_eq_prod_labelledFibrePerm`, `sign_eq_pow_card_add_card`,
`arithmeticEllipticSubsetDivisorEquiv`, `ellipticStablePointPerm_sign`,
`arithmeticEllipticStableOrientationSum_eq`,
`arithmeticEllipticStableOrientationSum_bound`.

Direct final Lean checks passed. All 20 transitive axiom audits across
the two modules use only `propext`, `Classical.choice`, `Quot.sound`.

The original orientation-quotient counts still require their transporter
comparison with `J_n`: collisions cancel, and each distinct-point
configuration contributes its `n!` orderings. This theorem does not assume
or assert that unfinished identification. No integer conductor-height
comparison or estimate for `Σ_p index_p(N)=1−M(N)` follows.
