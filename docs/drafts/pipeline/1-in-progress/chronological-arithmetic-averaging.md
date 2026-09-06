# Arithmetic averaging after the raw heat obstruction

Original [R] remains fixed and open. Geometric-response damping [A] is excluded;
this card concerns arithmetic weights, a different family.

**Frozen [G].** There exist ε_N≥0 tending to zero for which
exp(−t)+Σ_(k≤N)μ(k)k^(−ε_N)h(kt) tends to zero in full L². Coefficients are
bounded by one. No RH assumption may enter an attempted proof. This is a
classical candidate, not a novelty claim; published conditional approximation
arguments explicitly use RH to control truncation and shifted zeta quotients.

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

**[BRIDGE G0], frozen before formalization.** If ε_N≥0 and
ε_N log N→0, arithmetic power damping cannot converge in full L². Finite Abel
summation has terminal weight exp(−ε_N log N)→1; after division by that weight,
the discrepancy is a vanishing positive combination of strict earlier raw
prefixes. The existing Volterra induction would force raw convergence, already
excluded. This is a necessary scale condition, not a proof or refutation of [G].
Its positive survivor is the exact convex decomposition and quantitative norm
estimate for the earlier-prefix contribution.

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
