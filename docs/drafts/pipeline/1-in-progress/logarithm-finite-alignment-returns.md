# Finite alignment has no last height

- **ID:** SPL-finite-returns
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** [§2.9, small-arc question](../../../reports/review-0711/obstacles-summary.md)
- **Statement:** For every finite integer set and positive precision, alignment
  recurs at arbitrarily large heights; a meaningful exclusion must let the cutoff grow with height.

## Exact scope

For `Q≥1` and `L>0`, simultaneous Dirichlet applied to
`L log n/(2π)` gives a height in `[L,LQ^{|A|}]` with every phase
within `2π/Q` of an integer multiple of `2π`.

Thus a fixed interval, even occupied in full, cannot force every aligned height
below a fixed power of its first return. This refutes that fixed-cutoff reading,
not a bound for a height-dependent cutoff.

## Positive survivor

The scalable return interval `[L,LQ^{|A|}]` is an explicit multiplicative gap
bound. The surviving question is a lower bound for the **first** return as the
cutoff grows, or exclusion in a specified initial height range. Dependence on
the cutoff cannot be discarded.

The mechanism is existing simultaneous Dirichlet approximation, not a new
Diophantine estimate. Lean formalization is required before closing this card.
