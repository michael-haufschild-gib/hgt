# Xi prime seam one-ended cofinal-edge collapse

- **ID:** `xi-prime-seam-one-ended-cofinal-edge-collapse`
- **Stage:** 3-formalized/not_new_scientific_knowledge
- **Type:** THEOREM (paper), `[TOP-DOWN BRIDGE]`
- **Scientific status:** `[PROVED] [FORMALIZED] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Parents:** `finite-boundary-one-ended-coherence-reconstruction.md`;
  `sonin-two-particle-prime-coherence.md`; `xi-prime-seam-coherence-collapse.md`

## Statement

Let `G` be an infinite preconnected graph with the finite-boundary one-ended property.  Let
`alpha` be an arbitrary type; no finiteness or algebraic structure on `alpha` is assumed.  For
every label `f:V(G)->alpha`,

```text
{(v,w): v~w and f(v)!=f(w)} finite
  -> there exists c in alpha such that {v:f(v)!=c} is finite.              (1)
```

Thus the finite-valued restriction in the currently formalized theorem
`eventuallyConstant_of_finite_edgeVariation` is unnecessary when the graph is preconnected.

Now identify the vertices with the primes and put, for an open-strip Xi divisor point `rho`,

```text
a_p(rho)=log(p)(p^(-conj rho)-p^(-(1-rho))).              (2)
```

If the edge-variation set

```text
{(p,q): p~q and a_p(rho)!=a_q(rho)}                       (3)
```

is finite, then `Re(rho)=1/2`.  Consequently, if `(3)` is finite for every Xi divisor point,
then RH holds.

For the one-ended ray on the increasing primes `p_0,p_1,...`, the condition is simply

```text
there exists N such that
  a_(p_n)(rho)=a_(p_(n+1))(rho) for every n>=N.            (4)
```

## Proof of arbitrary-label reconstruction

Let `F=edgeVariation(G,f)`, which is finite, and fix a root `v_0`.  Along a finite walk from
`v_0` to a vertex `v`, the value of `f` changes only on edges in `F`.  If the terminal value is
not `f(v_0)`, its last change occurs on one of those edges, so it is the value of `f` at an
endpoint of an edge in `F`.  Hence

```text
range(f) subset {f(v_0)} union f(edgeEndpointSupport(F)).                  (5)
```

The right side is finite.  Replace `alpha` by the finite subtype `range(f)` and apply the already
proved finite-valued one-ended reconstruction theorem.  Projecting back to `alpha` proves `(1)`.

This argument is constructive at the theorem level: preconnectedness is used only to choose a
finite walk, and the finite range is derived from the finite edge variation rather than assumed.

## Xi collapse

Apply `(1)` to `(2)`.  There are a scalar `c` and a finite vertex set outside which
`a_p(rho)=c`.  The formal Xi seam theorem proves

```text
a_p(rho) -> 0
```

cofinally along the primes.  Therefore `c=0`.  Choose any prime outside the exceptional finite
set.  Then

```text
p^(-conj rho)=p^(-(1-rho)).                               (6)
```

The quotient in `(6)` is the positive real number `p^(1-2 Re(rho))`; it equals one only when
`Re(rho)=1/2`.  This proves the pointwise statement and hence the divisor-wide RH implication.

## Sparse operator corollary

Let `L_p` be the actual normalized Sonin prime corner from
`sonin-two-particle-prime-coherence.md`.  For an edge `e={p,q}`, define the canonical seam
coboundary corner

```text
D_e(rho)=(a_p(rho)-a_q(rho))(L_p tensor L_q).              (7)
```

The singleton case of the proved tensor essential-norm lower bound gives

```text
|a_p(rho)-a_q(rho)|/sqrt(pq)
  <= dist(D_e(rho),Compact).                              (8)
```

Hence compactness of `D_e(rho)` forces exact equality of the two endpoint charges.  Combining
`(8)` with `(1)` gives the chain

```text
for every Xi divisor point rho,
  D_e(rho) is compact on all but finitely many edges of one fixed one-ended prime graph
    -> the prime seam charge is eventually constant
      -> cofinal decay makes that constant zero
        -> Re(rho)=1/2
          -> RH.                                          (9)
```

On the prime ray, `(9)` asks only for eventual compactness of adjacent-prime coboundaries.  It is
strictly weaker as an operator realization target than a uniform Calkin bound for all pairs: no
complete graph, reciprocal-prime mass amplification, or simultaneous finite-section norm is
required.

## Source-side target

The bounded Sonin--Burnol conductor graph from
`sonin-burnol-conductor-cutoff-bounded-graph-law.md` suggests the concrete remaining theorem:

```text
the Xi-zero evaluator annihilates the resolvent-dressed conductor connection
modulo compact operators on every sufficiently late edge of a fixed prime ray.                (10)
```

Only the coboundary along that sparse cofinal edge family is required.  A proof of `(10)` must
come from an exact prime--Gamma value relation or reflection identity; compactness may not be
assumed from the vanishing of the coefficient, since that would be the conclusion in disguise.

## Relation to the complete-pair route

The complete-pair route remains valid:

```text
uniform all-pair Calkin bound -> global coherence -> RH.
```

The present theorem exposes a different sufficient source theorem:

```text
cofinal sparse-edge compactness -> eventual coherence -> RH.
```

Neither implication follows formally from the other.  The complete-pair route converts a global
norm bound to exact coherence using divergent reciprocal-prime mass.  The sparse-edge route asks
for exact compactness edge by edge but only on a one-ended cofinal skeleton.

## Gates

- [x] remove the finite-label restriction on paper
- [x] specialize one-ended reconstruction to canonical Xi seam charges
- [x] use cofinal decay to kill the eventual common value
- [x] derive the sparse-edge Sonin Calkin chain to RH
- [ ] formalize arbitrary-label one-ended reconstruction in `HTGeometry`
- [ ] formalize the Xi seam graph specialization in `RHTower`
- [ ] formalize the stage-2 tensor essential-norm lower bound
- [ ] prove the source compactness theorem `(10)`
- [ ] prove RH

## Lean formalization (complete and unconditional)

- `formal/GaloisForLFunctions/HTGeometry/ArbitraryLabelEndReconstruction.lean` — equation `(1)`:
  finite edge variation of an arbitrary-valued label on an infinite preconnected graph with the
  finite-boundary one-ended property forces the label to be constant off a finite set.
- `formal/GaloisForLFunctions/RHTower/XiPrimeSeamOneEndedCollapse.lean` — the Xi seam
  specialization: cofinal decay kills the common value, and both the graph form and the prime-ray
  form `(4)` of the collapse.
- `formal/GaloisForLFunctions/RHTower/XiPrimeSeamSparseEdgeCalkin.lean` — the coboundary corner
  `(7)`, the essential-norm lower bound `(8)` from the two-scale positive Euler Gram entry, and
  both forms of the sparse chain `(9)`.
