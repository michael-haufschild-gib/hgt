# Arithmetic averaging after the raw heat obstruction

Original [R] remains fixed and open. Geometric-response damping [A] is excluded;
this card concerns arithmetic weights, a different family.

**Frozen [G].** There exist ε_N≥0 tending to zero for which
exp(−t)+Σ_(k≤N)μ(k)k^(−ε_N)h(kt) tends to zero in full L². Coefficients are
bounded by one. No RH assumption may enter an attempted proof. This is a
classical candidate, not a novelty claim.
[Balazard–de Roton](https://arxiv.org/pdf/0812.1689) explicitly use RH to
control truncation and shifted zeta quotients for these weights in the classical
Nyman–Beurling setting; their rates have not been transferred to this heat norm.

**Frozen finite diagnostic [G-test].** Compare arithmetic power damping with
the entire convex hull of the raw residuals R_1,...,R_N at N=128,512,2048,8192.
Convex averaging gives coefficients μ(k)w_k with
1=w_1≥w_2≥...≥w_N≥0. Find feasible vectors and finite quadrature dual bounds;
validate selected residuals independently, including both end tails. All
mathematical numerical work runs on the authorized Runpod. No computation
enters Lean. This tests whether arithmetic averaging can realize the much
smaller errors of unrestricted box repair at these cutoffs. Finite success,
failure or optimizer stagnation does not decide [G] or [R].

**Hard source issue.** For arithmetic power damping, finite Abel summation is
exactly
D_(N,ε)=N^(−ε)R_N+Σ_(k<N)(k^(−ε)−(k+1)^(−ε))R_k.
Weights are positive and sum to one. This exposes the interaction between
ε_N and log N; passing ε_N→0 without controlling the growing cutoff is invalid.
The target is a full norm estimate for this actual moving average.

**[BRIDGE G0], proved in Lean.** If ε_N≥0 and
ε_N log N→0, arithmetic power damping cannot converge in full L². Finite Abel
summation has terminal weight exp(−ε_N log N)→1; after division by that weight,
the discrepancy is a vanishing positive combination of strict earlier raw
prefixes. Volterra induction forces raw convergence, already excluded. This is a necessary scale condition, not a proof or refutation of [G].
Its positive survivors are the exact convex decomposition, quantitative
earlier-prefix norm estimate, and a cofinal positive ε_N log N floor for
every successful nonnegative power schedule. This is not an eventual floor.
[Proof and twelve-declaration certificate](../3-formalized/chronological-arithmetic-averaging-scale.md).

The finite scalar search uses ε∈[0,4], a mixed linear/logarithmic grid and local
refinement. The convex-hull search uses fully corrective minimum-norm column
generation. Nonstationarity or a time limit is reported as such; all retained
vectors remain feasible. Quadrature dual values are floating-point diagnostics.

**Independent dual attack, currently unproved.** A Hahn–Banach approach to [R]
with bound one asks for |⟨exp(−t),v⟩|≤Σ_k|⟨h(kt),v⟩| for every L² test v.
For compact tests away from zero with ∫v(t)/t dt=0, the Möbius/Lambert identity
gives the inequality directly. Extending this to all tests with summable
correlations requires density in the graph norm, not merely L² density.
Fatou has the wrong direction for that extension. No closure claim is made.

**Finite outcome.** At N=128,512,2048,8192, positive-average errors are
6.55e−7, 1.68e−8, 1.29e−9, 1.02e−9. Best power errors found are
2.52e−3, 6.77e−2, 1.52e−1, 1.71e−1. All average coefficients satisfy C=1,
preserve Möbius signs and vanish at nonsquarefree indices. Shifted quadratures
and 80-digit residual checks agree; no certified optima or asymptotic claim.
At larger cutoffs, dual diagnostics give no positive lower bound.
[Reproducible report and vectors](../2-fully-proven/computations/chronological-arithmetic-averaging-2026-09-06/REPORT.md).

**Current hardest source statement.** Show that zero lies in the closed convex
hull of {R_N:N≥1}. Equivalently, rule out an L² test v and c>0 with
⟨R_N,v⟩≥c for every N. Finite mode cancellation supplies no bound for the
remaining modes as cutoff and rank grow. A uniformly norm-bounded raw
subsequence at unbounded cutoffs, together with local convergence, would
suffice by weak convergence and convexification; cofinal bounded recurrence
is itself unproved. A decreasing minimum over all earlier raw prefixes does
not establish such recurrence. The corpus already has a related bounded-return
Fatou route; this observation is not a new proof architecture.
