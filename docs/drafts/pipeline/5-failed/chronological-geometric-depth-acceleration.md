# Geometric depth damping as a new convergence mechanism

**Retired claim:** damping the infinite chronological Fermi repair supplies a
new mechanism for obtaining the bounded-array full L² approximation.
**Not retired/disproved:** the original RH endpoint; the possibility that the
raw or damped arrays converge. Their truth is not decided here.

The damping yields explicit coefficients bounded uniformly by two and a
resummed rational response with squared L² error ≤ε²/4. This looked promising
because finite response powers have unbounded Lambert coefficients.

**Obstruction, proved in Lean:** for every ε_N→0 within [0,1/2], full L²
convergence of the finite damped arrays is equivalent to raw Möbius convergence.
The resummed-response bound therefore does not resolve the truncation problem.

**Positive survivor, paper proof dependency-closed and Lean complete:** the
actual residual difference has norm ≤2ε(1+C) whenever every strict earlier raw
prefix has norm ≤C. A strong-induction argument turns this quantitative estimate
into the exact convergence equivalence. This identifies which information a
replacement repair must change: it must escape this vanishing perturbation of
strict earlier prefixes.

[Proof and formal certificate](../3-formalized/chronological-damping-convergence-rigidity.md).
[Compact research state](../1-in-progress/chronological-bounded-repair-attack.md).
No numerical observation is used in this result.
