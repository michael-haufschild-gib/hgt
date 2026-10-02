# TG-C9.9: closed extension of literal mixed-prime theta

- **Stage:** 5-failed
- **Candidate:** original finite prime-dependent theta extends to a closed operator
  in the completed even Fourier-jet graph norm.
- **Status:** disproved for every nonzero parameter as soon as two distinct primes
  are admitted; exact Lean classification in `PrimeBurnolFourierJetThetaClosure`.

The finite action is single-valued. Distinct literal prime-depth graph cores are
algebraically disjoint but dense in the same separately admitted even multiplication
graph. Their two continuous raw theta actions differ by an invertible matrix at every
nonzero parameter. Subtracting the two graph limits gives every vertical direction;
subtracting those from the original graph gives every horizontal direction.

**Strongest positive survivor:** the graph closure is exactly G×G at nonzero parameter,
so every source and response pair in G is simultaneously approximable by the same
literal finite two-prime theta graph. At zero it is exactly the original closed neutral
graph. The finite operator is closable iff its parameter is zero.

Paper proof is dependency-closed and the exact theorem passes the production Lean leaf.
Audit record: `../3-formalized/tg-prime-theta-graph-closure.md`.

This retires closed theta extension in this particular topology, not route TG or the
complete cubic. The balanced single-prime full cubic already proves that cancellation
can survive unbounded factors. Next research keeps the complete varying-prime cubic
and every packet/Gamma term. No RH proof or falsification follows.
