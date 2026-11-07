# Sum-product arithmetic at a single height

- **ID:** SPL-core
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** [Obstacles summary §§2.6, 2.9](../../../reports/review-0711/obstacles-summary.md)
- **Statement:** Produce arithmetic control of logarithmic phases beyond the
  diagonal and polynomial-phase ceilings, with no quadratic-form sign input.

## First quantitative target

Find fixed `K>1`, `c>0`, `T₀` such that, for every `t≥T₀` and
`y=(log t)^{2K}`,

`Σ_{p≤y} p^{-1/2}(1−cos(t log p)) ≥ c Σ_{p≤y} p^{-1/2}`.

This is the all-height proportional-saving question from §2.6. An estimate
on a density-one set of heights does not meet it. A prime-alignment hypothesis
is not an input to assume. No theorem in the new programme proves this estimate.

## Arithmetic information still missing

The translated-product reconstruction theorems bound the occupation of each
**real** logarithmic cell. They do not control the distribution between distinct
winding cells. In particular, inverse-square separation at large height is
consistent with every integer of a fixed interval returning to a small arc.

A useful further estimate must connect integer translation, multiplication,
and the actual prime weights, rather than only count the signatures of a
finite set. It must also avoid a loss proportional to word length that turns
constant prime precision into vanishing precision.

## Independent finite-zero target

Decide whether the exact integer count and its carries contradict the finite
oscillation forced by a nonempty finite right-zero layer. The proportional
saving above concerns growing heights and does not itself exclude a fixed
exceptional zero. Linear floor readings and exact ledgers are already blind
to these modes.

## Full scope still required

* Additive energy of phase level sets past the diagonal.
* Exponential-sum savings when Taylor degree exceeds `(log length)²`.
* A carry argument deciding the finite-oscillation question.
* Effective return bounds in both directions, with cutoff/height dependence explicit.
* Count-distance geometry above the Beurling isolation gap, keeping nonnegative
  generator multiplicities and finite exceptional zero support explicit.

[Bounded-count rigidity](../3-formalized/logarithm-bounded-count-rigidity.md) isolates a concrete
advance on this last question: rational-prime rigidity extends from vanishing
count error to `o(log n)` error at slope one. Collision amplification in the
free label monoid and consecutive-integer cancellation give the
[logarithmic floor](../3-formalized/logarithm-count-distance-floor.md). This does not determine
the smallest distance carrying an exceptional zero.

Finite-field calibration must retain the precise split-hyperelliptic scope
of existing Stepanov results. Any power-saving parity output must include
its zero-free-strip consequence. None of these requirements is discharged
by exact shifted-product reconstruction alone.
