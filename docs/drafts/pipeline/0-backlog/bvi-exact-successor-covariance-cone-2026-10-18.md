# Exact attainable successor covariance cone

- **ID:** bvi-exact-successor-covariance-cone-2026-10-18
- **Stage:** 0-backlog
- **Type:** CONJECTURE
- **Statement:** At sieve level six, mean-zero weights realize exactly the pairs `(S,B)` satisfying `-S ≤ B` and `2B ≤ S`.

## Mathematical purpose

The unconditional successor bounds constrain the joint same-node and successor forms.
An exact realization theorem would determine whether additional inequalities can hold
without imposing further arithmetic restrictions on the weights. It would also identify
the two exceptional modes generating the full feasible cone.

## Corpus evidence

Local research queries for Selberg coordinates, successor rigidity, parity, and covariance
realization locate the existing simultaneous diagonals and the new rigidity module.
No realization theorem was identified. The broad hybrid query was partial; targeted lexical
queries and source inspection supplied the useful results. Before implementation, search
again for general finite multiples-transform inversion and coordinate surjectivity.

## Candidate proof

Choose Selberg coordinates `Y(1)=0`, `Y(2)=a`, `Y(6)=b`, all others zero.
The required coefficients are

`c(1)=b-a`, `c(2)=2a-2b`, `c(3)=-3b`, `c(6)=6b`, with all other coefficients zero.

These give `S=a²+2b²`, `B=-a²+b²`. Conversely, if `-S≤B` and `2B≤S`,
take `a=√((S-2B)/3)` and `b=√((S+B)/3)`. Both radicands are nonnegative.
Substitution yields the requested pair.

Prefer a symbolic finite-coordinate realization theorem, reused here, over finite numerical
enumeration. The arithmetic content is the successor spectrum `μ(e)/φ(e)` and its
exceptional modes at two and six; the auxiliary triangular transform alone is not a new
field contribution.

## Gates

- [ ] Renew corpus audit for inverse-transform infrastructure.
- [ ] Dependency-closed symbolic paper proof.
- [ ] Unconditional Lean realization equivalence and endpoint witnesses.
- [ ] Named-module verification, axiom audit, wiring, lint.

Not counted toward the 250-contribution goal.
