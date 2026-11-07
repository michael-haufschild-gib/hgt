# Finite alignment has no last height

- **ID:** SPL-finite-returns
- **Stage:** 5-failed
- **Type:** NO-GO WITH FORMALIZED POSITIVE SURVIVOR
- **Source:** [§2.9, small-arc question](../../../reports/review-0711/obstacles-summary.md)
- **Statement:** For every finite integer set and positive precision, alignment
  recurs at arbitrarily large heights; a meaningful exclusion must let the cutoff grow with height.

## Exact scope

For `Q≥0` and `L>0`, simultaneous Dirichlet applied to
`L log n/(2π)` gives a height in `[L,L(Q+1)^{|A|}]` with every phase
within `2π/(Q+1)` of an integer multiple of `2π`.

Thus a fixed interval, even occupied in full, cannot force every aligned height
below a fixed power of its first return. This refutes that fixed-cutoff reading,
not a bound for a height-dependent cutoff.

## Positive survivor

The scalable return interval `[L,L(Q+1)^{|A|}]` is an explicit multiplicative gap
bound. The surviving question is a lower bound for the **first** return as the
cutoff grows, or exclusion in a specified initial height range. Dependence on
the cutoff cannot be discarded.

The proof applies simultaneous Dirichlet to the scaled frequencies with
denominator parameter `Q+1`. Its integer `q` lies between `1` and
`(Q+1)^{|A|}`; set `t=Lq`. Taking `L>max(T,0)` gives a return above every `T`.
This uses existing simultaneous Dirichlet approximation; it is not a new
Diophantine estimate.

## Lean evidence

`SumProductArithmeticOfTheLogarithm/FiniteAlignmentReturns.lean` passes its
direct Lean check. The positive survivor is
`exists_alignment_in_scaled_interval`; `exists_alignment_above` and
`not_exists_last_alignment` give the no-go. Axiom audits of the interval
theorem and no-go return only `{propext, Classical.choice, Quot.sound}`.

Only the fixed-cutoff, last-height interpretation is retired. The first-return
and growing-cutoff questions remain in
[the core problem](../1-in-progress/sum-product-logarithm-core.md).
