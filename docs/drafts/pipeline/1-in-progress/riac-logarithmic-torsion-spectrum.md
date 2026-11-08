# Compact logarithmic torsion without Hilbert–Schmidt summability

- **ID:** RIAC-logarithmic-spectrum
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** [Logarithmic completion](riac-logarithmic-torsion-completion.md)
- **Statement:** For every `α>2`, the original logarithmic torsion operator is compact and self-adjoint, but not Hilbert–Schmidt.

## Exact mechanisms

Put `L(n)=1+log n`. Inclusion from logarithmic exponent `α` to `β<α`
multiplies normalized coordinates by `L(n)^((β−α)/2)`. This multiplier is
bounded by one and tends to zero, so the existing diagonal compactness
theorem applies. Inclusion preserves the original arithmetic coefficients.
For `2<β<α`, the torsion form factors through this compact inclusion on
both arguments. Riesz representation preserves compactness.

The normalized diagonal is `d(n)/L(n)^α`. On even prime conductors,
`d(2p)≥log 2`. Choose an integer `N>2α`. Eventually
`L(2p)≤(2+log 2)log p` and hence

`d(2p)²/L(2p)^(2α) ≥ (log 2)²/((2+log 2)^N(log p)^N)`.

The existing theorem `RHTower.prime_log_pow_not_summable` proves divergence
of the right-hand series using only Euler's prime reciprocal divergence.
Thus the diagonal square sum diverges for every real `α`. A Hilbert–Schmidt
operator has summable diagonal squares by Cauchy–Schwarz in its Hilbert
basis, giving the contradiction for the bounded logarithmic operator.

## Prior work and status

HHAC supplies coefficient-preserving conductor inclusions, compact torsion
operators, the lower bound `d(2n)≥log 2`, and the conductor-weight
Hilbert–Schmidt boundary `δ>1/2`. Generic compact diagonal operators and
prime-log divergence already exist. The target here is their exact application
to the logarithmic arithmetic carrier, with its original pair series retained.

Complete Lean drafts exist for both mechanisms. They remain unchecked,
and depend on the unverified logarithmic bounded-completion draft.
No spectral theorem from these drafts is accepted yet.
