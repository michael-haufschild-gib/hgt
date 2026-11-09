# Sharp logarithmic completion of the full torsion form

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parent:** [RIAC](../1-in-progress/renormalized-intersection-arithmetic-counts.md)

## Exact threshold and completion

For positive conductors put `L(n)=1+log n`. The original torsion matrix
has a bounded extension to arithmetic sequences with finite mass
`Σ_n L(n)^α x_n²` exactly when `α>2`. The extension is unique, symmetric,
and represented by a self-adjoint Hilbert operator. Its pairing is the
absolutely convergent original arithmetic pair series.

For `a=α−1>1`, put `K_a=Σ_t Λ(t)/(t L(t)^a)`. Every finite quadratic
prime interaction is bounded absolutely by `(K_a+1)Σ_n L(n)^α x_n²`.
The full torsion absolute bound has constant `K_a+2`; adding
`(K_a+1)Σ_n L(n)^α x_n²` makes its quadratic form nonnegative, on finite
and completed probes. Existence of either a constant diagonal compensation
or a uniform finite absolute bound is equivalent to `α>2`.

## Proof

Use Schur reference `λ(n)=1/(√n L(n)^a)`. The multiples row is bounded
by `K_a/√n`; the divisor row is at most `log n/√n`, using
`Σ_(t|n)Λ(t)=log n` and `L≥1`. Their sum is bounded by
`(K_a+1)L(n)^α λ(n)`. Weighted square completion gives the prime bound.
The original tame diagonal lies between zero and `log n`, giving the full
absolute bound and the explicit positive correction.

At `α≤2`, restriction to the actual conductor-one prime row has divergent
square mass. Restricting any proposed full compensation to finite prime
stars gives leaf diagonal `d(p)+C L(p)^α`; its eventual growth is at most
`(1+4|C|)(log p)²`. The formalized prime-star classification rules out the
required finite payment, without a sign assumption on `C`.

Normalized coordinates represent every sequence of finite logarithmic mass
faithfully and preserve its mass as squared Hilbert norm. The finite bound
constructs the continuous form and absolute pair series. Density of finite
basis vectors gives uniqueness. Symmetry gives self-adjointness; the
infinite absolute prime bound transfers the same compensation to every
completed probe.

## Scope

The exponent threshold is sharp; the displayed constants need not be minimal.
The added diagonal is a constructed compensation, not an independently
constructed arithmetic height or product-formula count. No positivity of
the uncorrected Weil form or bound for `1−M(N)` follows. The
[spectral branch](riac-logarithmic-torsion-spectrum.md)
concerns this same original completed form.

## Lean statements

- [LogarithmicTorsionBound](../../../../formal/GaloisForLFunctions/RenormalizedIntersectionArithmeticCounts/LogarithmicTorsionBound.lean):
  `spacingLimit_logarithmic_compensation_iff`,
  `spacingLimit_logarithmic_finite_bound_iff`.
- [LogarithmicTorsionCompletion](../../../../formal/GaloisForLFunctions/RenormalizedIntersectionArithmeticCounts/LogarithmicTorsionCompletion.lean):
  `logarithmicTorsion_bounded_extension_iff`, `logarithmicTorsionForm_unique`,
  `logarithmicTorsionForm_absolute`, `logarithmicTorsionOperator_selfAdjoint`,
  `logarithmicTorsionForm_compensated_nonneg`.

Both direct checks pass. All 23 printed axiom audits contain only
`propext`, `Classical.choice`, and `Quot.sound`.
