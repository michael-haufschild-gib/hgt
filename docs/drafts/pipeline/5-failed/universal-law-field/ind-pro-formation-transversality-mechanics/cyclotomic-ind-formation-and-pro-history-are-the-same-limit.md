# Failed conjecture: cyclotomic ind-formation and pro-history are the same limit

- **Status:** [FAILED] [EXACT COUNTERTHEOREM] [FIELD PIVOT]
- **Positive survivor:** ULF-IPFTM-1

## Conjecture

Because both constructions use the same finite root groups \(\mu_n\), the filtered union of roots
and the inverse system of root observations should be interchangeable presentations of one
cyclotomic limit.

## Failure

Their structure maps have opposite variance and different action:

\[
 i_{n,m}(z)=z,
 \qquad
 r_{m,n}(z)=z^{m/n}.
\]

If a pro-history is represented by one ind-born root \(\xi\) at depth \(d\), then at depths
\(d\) and \(2d\) it has the same ind value \(\xi\).  Pro coherence requires

\[
 \xi=\xi^2,
\]

so \(\xi=1\).  Cofinality forces the entire history to be the identity.

Thus the two limits do not merely differ; their common group-like realization is trivial.

## Positive survivor

Formation and history should be treated as distinct primitives.  Their crossed mismatch
reconstructs integral charge, its regular representation is maximally noncompact, and its
vanishing gives an exact divisor-selection law.  The resulting open problem is a literal source
comparison: whether Euler-shell formation holonomy lands group-like in the rational-Witt
ind-source.

No Lean was written or built in this research pass.
