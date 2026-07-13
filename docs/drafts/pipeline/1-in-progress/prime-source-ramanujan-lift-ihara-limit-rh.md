# Prime-source Ramanujan lifts, Ihara determinants, and RH

- **ID:** `prime-source-ramanujan-lift-ihara-limit-rh`
- **Stage:** 1-in-progress
- **Type:** `[LARGE OUTLANDISH DETOUR] [CONJECTURE] [FORMALIZED FINITE CONSUMER]`
- **Lean inputs:** `formal/GaloisForLFunctions/IharaBlockSelector.lean`,
  `formal/GaloisForLFunctions/SpectralTorelli.lean`,
  `formal/GaloisForLFunctions/PrimeWordSupportSelector.lean`,
  `formal/GaloisForLFunctions/RHTower/PrimeSupportBoundaryJets.lean`,
  `formal/GaloisForLFunctions/RHTower/PrimeWordEnsembleBoundaryTomography.lean`,
  `formal/GaloisForLFunctions/RHTower/PrimeSupportMultivariateLiftMarker.lean`, and
  `formal/GaloisForLFunctions/RHTower/CCMSharpPrimeWindowDivisorTomography.lean`
- **Statement:** `[CONJECTURE]` The actual completed prime source is the locally uniform determinant
  limit of a cofinal, source-constrained family of finite Ramanujan graph lifts.  The formal Ihara
  selector then puts every finite nontrivial zero on its graph-critical circle, and the determinant
  limit puts every Xi zero on the critical line.

## Goal

Construct the graph family from the Euler--Gamma source before inspecting the Xi divisor.  The
route is admissible only if the graph constraints are explicit prime-word, prime-window, or theta
moments; choosing a graph from desired Xi zeros is forbidden.

The two ends are already exact:

1. the source end has finite Euler words, all support-cardinality boundary jets, and one fixed
   dyadic von-Mangoldt statistic recovering the complete right off-critical Xi divisor;
2. the consumer end has the Lean theorem that every nontrivial Ihara quadratic block has its zeros
   on the critical circle exactly when its adjacency parameter obeys the Ramanujan spectral bound.

The open content is a constrained graph-realisation and cofinal determinant theorem joining them.

## The chain

Fix a degree `q+1`, finite source aperture `P`, and a finite jet/window depth `d`.  Seek a finite
`(q+1)`-regular bipartite graph `G_(P,d)` such that its nonbacktracking closed-walk data are the
prescribed completed prime-source moments at that aperture.  Then:

```text
finite Euler prime words and dyadic prime windows
  -> full marked-support boundary germ                    [PROVED IN LEAN]
  -> prescribed finite nonbacktracking trace packet
       [OPEN CORE A: integral graph-realisation]
  -> a signing/lift satisfying the same source packet
       [OPEN CORE B: conditional interlacing]
  -> Ramanujan adjacency bound |lambda| <= 2 sqrt(q)
  -> every nontrivial Ihara block
       1-lambda*u+q*u^2 has |u|=q^(-1/2)                 [PROVED IN LEAN]
  -> normalized reciprocal Ihara determinant I_(P,d)(z)
       has all zeros on the centered real axis
  -> locally uniform, exhaustion-independent limit
       I_(P,d)(z) -> E(z) Xi(z), E entire and zero-free
       [OPEN CORE C: completed determinant comparison]
  -> Xi is a locally uniform limit of real-rooted polynomials
  -> Xi is Laguerre--Polya
  -> every nontrivial zeta zero lies on Re(s)=1/2
  -> RH.
```

The Möbius/Cayley coordinate used in the limit must send the Ihara circle
`|u|=q^(-1/2)` to the real centered Xi coordinate.  Trivial Ihara factors such as powers of
`1-u^2`, the Perron eigenvalues, and the Gamma/polar completion must be removed explicitly; they
may contribute only the zero-free factor `E`.

## Why interlacing is a possible engine rather than a conclusion

Marcus--Spielman--Srivastava prove that bipartite Ramanujan graphs exist in every degree greater
than two by selecting good lifts through interlacing polynomials.  Their later all-sizes theorem
uses expected characteristic polynomials of unions of random perfect matchings, real-rootedness,
and finite free convolution.  These theorems do not preserve an arbitrary prescribed trace packet.
The required new finite theorem is therefore:

> `[CONJECTURE: SOURCE-CONDITIONAL INTERLACING]` For the affine face of lift signings cut out by the
> completed prime-source nonbacktracking moments through depth `d`, the conditional expected new
> characteristic polynomials form an interlacing family and retain the universal-cover root bound.

If the source constraints are local under graph lifts, this is stronger than ordinary existence
but not visibly equivalent to RH at a fixed finite stage.  It would manufacture the needed finite
positivity through a combinatorial selection theorem rather than assume a Weil-positive kernel.

Primary parent sources:

- Marcus--Spielman--Srivastava, *Interlacing Families I: Bipartite Ramanujan Graphs of All
  Degrees*, <https://annals.math.princeton.edu/2015/182-1/p07>;
- Marcus--Spielman--Srivastava, *Interlacing Families IV: Bipartite Ramanujan Graphs of All Sizes*,
  <https://epubs.siam.org/doi/10.1137/16M106176X>;
- Kotani--Sunada, *Zeta Functions of Finite Graphs*, for the Bass--Ihara determinant and the
  regular-graph factorization,
  <https://www.kurims.kyoto-u.ac.jp/EMIS/journals/JMST/0701/jmst0701-2.pdf>.

## Exact corpus leverage

### Source moments

`PrimeSupportBoundaryJets.lean` proves that the normal jet of order `r` at the Koszul cancellation
boundary detects exactly support size `r+1`, with nonzero factorial weight.
`PrimeWordEnsembleBoundaryTomography.lean` now proves the finite linear extension: for an arbitrary
integer-weighted word ensemble, the `r`th boundary jet is the explicit nonzero signed factorial
times the aggregate weight of the support-`r+1` stratum.  Equality of the full boundary germs
forces equality of every positive support-cardinality aggregate.  Thus the source packet can retain
mixed-prime strata before a graph specialization rather than collapse to independent prime axes.

This cardinality packet is not word-faithful: words with the same number of distinct labels may
still collide.  `PrimeSupportMultivariateLiftMarker.lean` supplies the complementary squarefree
support monomial.  Cyclic order and repeated traversal remain the genuinely graph-specific
coordinates that the multivariate nonbacktracking trace expansion must add.

`CCMSharpPrimeWindowDivisorTomography.lean` supplies a separate orbit-sensitive source coordinate:
one explicit dyadic prime window has a continuation whose poles in `Re(s)>1` are exactly the right
off-critical Xi zeros, with multiplicity.  The graph limit must reproduce this continuation, so a
family matching only formal Euler coefficients but losing the divisor is rejected.

### Finite spectral selector

For

```text
P_lambda(u)=1-lambda*u+q*u^2,
```

`IharaBlockSelector.lean` proves, for `q>0`,

```text
all zeros of P_lambda have |u|^2=q^(-1)
  <-> lambda^2 <= 4q.
```

It also proves the finite-product selector and an explicit no-go: reciprocal functional-equation
symmetry holds for every block and does not imply the spectral bound.

`SpectralTorelli.lean` proves that the full finite spectral polynomial determines the adjacency
eigenvalue multiset.  Thus matching all finite trace moments is not merely statistical; once enough
moments are fixed at each aperture, it identifies the finite determinant.

## Hard attacks and positive successors

1. **Reciprocity attack.**  Bass--Ihara reciprocity alone allows off-circle reciprocal pairs; this
   failure is already formalized.
   **Positive successor:** the missing condition is exactly the adjacency bound
   `lambda^2<=4q`, a finite inequality with no zero ambiguity.
2. **Binary-lift parity attack.**  An ordinary `2`-lift signing sees every edge multiplicity only
   modulo two.  Lean proves that the packets `(1,0)` and `(1,2)` have identical characters for
   every signing although their source support cardinalities are one and two.
   **Positive successor:** replace the raw signing by a multivariate edge-Ihara zeta or a marked
   lift character, extract the squarefree support germ first, and specialize to lift phases only
   afterward.  This repair is now formalized: the canonical squarefree multivariate marker retains
   exact word support and separates the parity-blind pair.  The unmarked binary-lift version is
   closed.
3. **Generic Ramanujan-family attack.**  Existing Ramanujan graphs have the right zero geometry but
   no reason to encode the prime source.
   **Positive successor:** condition the interlacing family on explicit source trace constraints;
   the affine face, not the ambient signing cube, is the object to study.
4. **Moment attack.**  A fixed number of closed-walk moments cannot identify a determinant.
   **Positive successor:** use a triangular cofinal schedule in which aperture, graph size, and
   retained moment depth all tend to infinity, with finite Spectral Torelli at every stage.
5. **Integral-realisation attack.**  Arbitrary real source moments need not be closed-walk counts of
   an unweighted graph.
   **Positive successor:** allow positive rational edge weights first, clear denominators by a
   finite covering construction, and prove that the Ihara selector survives this realization.
   If clearing denominators changes the prescribed determinant, this successor fails.
6. **Trivial-factor attack.**  Graph zeta functions contain topological and Perron factors unrelated
   to Xi; allowing them into the limit can feed zeros.
   **Positive successor:** state and prove an explicit relative determinant identity with a
   separately controlled zero-free factor `E`.
7. **Arbitrary-approximation attack.**  Ramanujan/Ihara polynomials can approximate many real-zero
   configurations; choosing them from Xi zeros would be circular.
   **Positive successor:** every graph must be functorially determined by the finite Euler--Gamma
   source packet, and the comparison to Xi is proved only after the graph tower is constructed.
8. **Lift-locality attack.**  Closed-walk constraints generally change under a lift and can
   destroy the interlacing recursion.
   **Positive successor:** separate old closed walks, which lift deterministically, from new signed
   nonbacktracking cycles.  The conditional theorem need constrain only the new-cycle cumulants.
9. **Limit attack.**  Coefficientwise determinant convergence does not preserve zeros.
   **Positive successor:** require locally uniform convergence after explicit genus-one
   normalization and uniform exponential-type bounds.
10. **Support-cardinality collision attack.**  Even the complete one-variable boundary germ
    aggregates different words having the same number of distinct prime labels.
    **Positive successor:** tensor the now-formal weighted boundary germ with the formal squarefree
    multivariate support marker, then retain nonbacktracking order through cycle variables.  The
    graph input is this three-coordinate packet, not the scalar jet tower alone.

## Concrete finite theorem to test first

Let `G` be a finite edge-labelled bipartite `(q+1)`-regular graph.  Form its multivariate edge-Ihara
determinant before choosing any lift phases.  Apply the marked squarefree-support derivatives that
recover the prime-support boundary jets, and only then specialize the edge variables to a complete
packet of cyclic-lift characters.  For a fixed depth `d`, determine whether the resulting marked
trace constraints are stable under conditional expectation and whether the expected new
characteristic polynomial is real-rooted.

The first decisive calculation is not to approximate Xi.  It is to prove or refute:

```text
the source-conditioned marked lift-character set is nonempty,
and its conditional expected new characteristic polynomial is real-rooted.
```

Failure of real-rootedness retires the proposed interlacing engine but leaves a positive graph
realisation problem: characterize exactly which completed prime-source trace packets lie in the
Ramanujan moment polytope.

## Kill conditions

Retire the route if the finite prime-source packets violate an elementary closed-walk integrality
or positivity condition; if conditioning destroys common interlacing already at low depth; if only
unweighted graph realization is possible by reading Xi zeros; if the required graph degree must
depend on the unknown divisor; if the cofinal determinant differs from Xi by a zero-bearing
factor; or if the limit is only coefficientwise.

## Gates

- [x] 0 -> 1 in-progress: source-pure two-ended chain and non-circularity rules stated
- [x] exact finite critical-circle/Ramanujan selector located in the parent Lean body
- [x] reciprocal-symmetry no-go converted to the positive adjacency-bound target
- [x] exact source moment and divisor-tomography coordinates identified
- [x] ordinary binary lift refuted as support-blind; positive marked multivariate successor isolated
- [x] squarefree multivariate word marker formalized and proved support-faithful
- [x] arbitrary finite weighted word ensembles formalized; every positive support stratum is
  exactly recovered by the complete boundary germ
- [ ] source trace packet expressed as marked multivariate nonbacktracking cycle cumulants
- [ ] first constrained-signing nonemptiness and real-rootedness test
- [ ] source-conditional interlacing theorem
- [ ] compatible Ramanujan lift tower
- [ ] locally uniform relative Ihara determinant limit identified with zero-free factor times Xi
- [ ] RH capstone formalized
