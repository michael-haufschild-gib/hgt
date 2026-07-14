# Finite-boundary one-ended coherence reconstruction

- **ID:** `finite-boundary-one-ended-coherence-reconstruction`
- **Stage:** 3-formalized
- **Type:** `THEOREM (Lean) / GENERAL HT CONSTRAINT GEOMETRY / NOVELTY UNVERIFIED`
- **Parent:** `../2-fully-proven/needs-audit/coherence-end-projective-ht-tail-reconstruction.md`
- **Lean:**
  `formal/GaloisForLFunctions/HTGeometry/CoherenceEndReconstruction.lean`,
  `formal/GaloisForLFunctions/HTGeometry/CoherenceEnds.lean`,
  `formal/GaloisForLFunctions/HTGeometry/CoherenceTailQuotient.lean`,
  `formal/GaloisForLFunctions/HTGeometry/PrimeCoherenceTailReconstruction.lean`

## Theorem

Let `G` be a locally finite graph.  Quotient Boolean vertex orientations by finite change and
global complement, and quotient their edge coherences by finite edge disagreement.  The canonical
coherence readout

```text
D_G : BooleanProjectiveFiniteTail(G) -> BooleanEdgeCoherenceTail(G)
```

is well defined, and for representatives `epsilon,delta` its exact equality kernel is

```text
D_G[epsilon] = D_G[delta]
  <-> boundary_G {v : epsilon(v) != delta(v)} is finite.  (1)
```

Consequently,

```text
D_G is injective
  <-> every finite-boundary vertex set is finite or cofinite. (2)
```

If `G` is infinite and preconnected, the right side of `(2)` is equivalent to

```text
Subsingleton G.end.                                      (3)
```

Thus the conventional one-end condition is exactly the geometry required for projective Boolean
orientation tails to be recovered from pair coherences outside an arbitrary finite defect.

For two infinite preconnected graphs `G,H`, the Cartesian product `G □ H` satisfies this
condition.  Hence its coherence readout is injective even when either factor separately has
several ends.

## Prime-tail consequence

After indexing the vertices by primes, projective finite-tail equivalence is exactly the existing
prime-orientation coefficient-tail dependence relation.  Therefore `(2)` is also the exact
criterion for finite-defect edge coherences to recover the projective prime coefficient-tail
matroid line.  This statement does not identify that line with equality of the actual embedded
differential fields; the latter remains an analytic independence problem in the parent card.

## Formal declarations

- `booleanEdgeDisagreement_eq_edgeBoundary`;
- `coherenceTailMap_class_eq_iff_finite_edgeBoundary`;
- `coherenceTailMap_injective_iff_finiteBoundaryOneEnded`;
- `finiteBoundaryOneEnded_iff_subsingleton_end`;
- `finiteBoundaryOneEnded_boxProd`;
- `coherenceTailMap_boxProd_injective`;
- `finiteBoundaryOneEnded_iff_primeOrientationCoherenceTail_faithful`;
- `exists_coherenceTailEquivalent_not_primeOrientationTailPairDependent_of_not_oneEnded`;
- `primeOrientationCoherenceTail_faithful_boxProd`.

## Gates

- [x] exact domain-wall kernel formalized
- [x] quotient readout and well-definedness formalized
- [x] injectivity classified by the finite-boundary condition
- [x] finite-boundary condition identified with the conventional end type
- [x] Cartesian-product stabilization formalized
- [x] prime coefficient-tail consequence formalized without an analytic field-equality claim
- [x] targeted module builds green
- [x] accepted-axiom audit: only `propext`, `Classical.choice`, and `Quot.sound`
- [x] repository formal lint gate passed
- [ ] independent novelty and significance verdict

## Status

`[FORMALIZED] [NOVELTY UNVERIFIED]` The theorem is unconditional at the graph, quotient, end, and
prime coefficient-tail levels.  It supplies the formal core of the broader coherence-end HT law
while keeping the unresolved topological clopen-algebra presentation and analytic embedded-field
identification outside its claim.
