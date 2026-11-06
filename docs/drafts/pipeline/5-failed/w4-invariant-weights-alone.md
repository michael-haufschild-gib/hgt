# W4 — invariant tensor weights alone do not force purity

- **Stage:** 5-failed
- **Type:** FALSIFIED
- **Scope:** Inference from invariant weights and positive local coefficients to fibre purity. W4 itself remains open.

## Exact obstruction

Let `φ=(1+√5)/2` and `F=diag(√5 φ,√5/φ)`. Then

- `det(F)=5`, `tr(F)=5`, and `det(1−tF)=1−5t+5t²`;
- `F` and `√5 I` act identically on every `SL₂(ℂ)`-invariant multilinear form;
- in degree `2k`, this action is `5^k`, and the invariant space is nonzero;
- every even-tensor local Euler coefficient is nonnegative;
- the normalized spectrum `(φ,φ⁻¹)` is impure.

**Proof.** Scalar multiplication contributes its tensor degree; the remaining determinant-one matrix fixes every invariant. Products of pairwise determinants supply nonzero forms. Even powers of real traces are nonnegative, so Newton–Witt recursion gives nonnegative Euler coefficients. The existing Golden datum supplies `φ>1` and its reciprocal spectrum. Its integer trace recurrence gives the stated Euler polynomial.

Lean: `golden_weight_and_coefficient_countermodel`, `golden_eq_pure_on_invariants`, `golden_euler_polynomial` in `ArithmeticKunnethTheory/WeightFamilies/GoldenInvariantWeights.lean`.

The obstruction survives abstract Frobenius compatibility with full `SL₂` image. The [split group model](../3-formalized/w4-split-weil-model.md) has degree-zero image exactly `SL₂`, degree-one image every determinant-`5` matrix, and a lift of Golden Frobenius. Lean: `splitAction_degree_one_iff`, `splitAction_normalizes`, `goldenFrobenius_has_split_lift`.

## Strongest positive survivor

The invariant action is classified exactly by the determinant character; it detects no eigenvalue-modulus ratio. Separately, for every positive integer `m` and `B≥0`,

`∃ C, ∀ n, |trace(n)|^m ≤ C B^n  ↔  φ^m ≤ B`.

Thus the missing estimate is quantitatively located: the optimal exponential rate grows with tensor degree, although every invariant weight is correct. Coefficient constants cannot reduce that rate.

**Proof.** The general tensor growth theorem bounds every powered eigenvalue modulus by `B`; the largest Golden modulus is `φ`. Conversely the triangle inequality gives the estimate from this maximal modulus. See the [general classification and curve receiver](../3-formalized/w4-invariant-characters-and-tensor-growth.md).

Lean: `golden_tensor_rate_iff`, `golden_no_fixed_base_rate`. All cited modules compile with `lake --old env lean`.

## Remaining arithmetic content

This is an algebraic countermodel, not a sheaf on an arithmetic base. A global cohomological trace identity with controlled poles, or an independent identification of ζ's actual spectrum with a pure invariant restriction, remains additional mathematical content.
