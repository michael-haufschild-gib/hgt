# Geometric depth damping as a new convergence mechanism

**Retired claim:** damping the infinite chronological Fermi repair supplies a
new mechanism for obtaining the bounded-array full L² approximation.
**Now excluded in Lean:** raw Möbius heat convergence and every admissible
vanishing geometric-damping schedule. **Still open:** the original arbitrary
bounded-array RH endpoint.

The damping yields explicit coefficients bounded uniformly by two and a
resummed rational response with squared L² error ≤ε²/4. This looked promising
because finite response powers have unbounded Lambert coefficients.

**Obstruction, proved in Lean:** for every ε_N→0 within [0,1/2], full L²
convergence of the finite damped arrays is equivalent to raw Möbius convergence.
A direct positive-Abel transfer now proves raw heat nonconvergence, so the
resummed-response bound cannot survive arithmetic truncation along any such schedule.

**Positive survivor, paper proof dependency-closed and Lean complete:** the
actual residual difference has norm ≤2ε(1+C) whenever every strict earlier raw
prefix has norm ≤C. A strong-induction argument turns this quantitative estimate
into the exact convergence equivalence. This identifies which information a
replacement repair must change: it must escape this vanishing perturbation of
strict earlier prefixes.

**Stronger positive survivor, paper proof closed and Lean complete:** one c>0
works for every successful arithmetic array: its correction relative to the raw
Möbius residual has L² norm at least c at arbitrarily large cutoffs. This is a
necessary condition for replacement constructions, without a coefficient-budget
premise. [Direct obstruction and persistent-correction certificate](../3-formalized/chronological-raw-heat-obstruction.md).

[Original rigidity certificate](../3-formalized/chronological-damping-convergence-rigidity.md).
[Compact research state](../1-in-progress/chronological-bounded-repair-attack.md).
No numerical observation is used in this result.
