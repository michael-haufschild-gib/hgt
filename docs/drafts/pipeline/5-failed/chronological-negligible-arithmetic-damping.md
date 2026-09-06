# Negligible arithmetic power damping is excluded

**Closed no-go [G0].** No ε_N≥0 with ε_N log N→0 can make
exp(−t)+Σ_(k≤N)μ(k)k^(−ε_N)h(kt) converge to zero in full L²(0,∞).
This retires only the negligible-scale subroute. General arithmetic power
damping [G], positive cutoff averages, and the original arbitrary bounded
array target [R] remain open.

**Failure mechanism.** Finite Abel summation retains R_N with coefficient
exp(−ε_N log N)→1. Dividing by that coefficient leaves a positive combination
of strict earlier residuals with total mass tending to zero. Volterra
induction would force convergence of the raw Möbius sequence, contradicting
the closed raw heat obstruction. No unproved raw boundedness is assumed.

**Positive salvage, paper and Lean complete.** The exact finite Abel
decomposition gives a quantitative earlier-prefix discrepancy bound and
an equivalence of actual L² convergence for all positive decreasing weights
whose terminal value tends to one. Every successful power schedule must have
a cofinally positive ε_N log N floor; equivalently, a fixed positive fraction
of averaging mass must leave the terminal cutoff cofinally. This does not
say how to distribute that mass successfully.

[Complete statement, proof and twelve-declaration certificate](../3-formalized/chronological-arithmetic-averaging-scale.md).
No computation is used in Lean. Finite optimization of ε does not refute
larger-scale power schedules.
