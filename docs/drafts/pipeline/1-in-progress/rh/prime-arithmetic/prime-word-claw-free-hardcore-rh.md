# Prime-word claw-free hard-core gas and RH

- **ID:** `prime-word-claw-free-hardcore-rh`
- **Stage:** 1-in-progress
- **Type:** `[LARGE OUTLANDISH DETOUR] [CONJECTURE] [POSITIVE SUCCESSOR TO MATCHING NO-GO]`
- **Lean inputs:** `formal/GaloisForLFunctions/RHTower/PrimeWordEnsembleBoundaryTomography.lean`,
  `formal/GaloisForLFunctions/RHTower/PrimeSupportMultivariateLiftMarker.lean`,
  `formal/GaloisForLFunctions/RHTower/PrimeWordMatchingIncidenceNoGo.lean`,
  `formal/GaloisForLFunctions/RHTower/PrimeWordClawFreeConflictNoGo.lean`,
  `formal/GaloisForLFunctions/RHTower/EulerSquarefreeWickDefect.lean`, and
  `formal/GaloisForLFunctions/RHTower/XiCTaylorThetaTailTelescope.lean`
- **Statement:** `[CONJECTURE]` The completed prime-word packet admits a cofinal family of
  source-defined positively weighted claw-free conflict graphs whose normalized hard-core
  partition polynomials converge locally uniformly to the square-coordinate centered Xi function.
  Weighted claw-free real-rootedness and Hurwitz then imply RH.

## Why this survives the matching no-go

The monomer--dimer route forces every higher coefficient to be a sum of pairings.  The raw Euler
four-point coefficient violates that Wick law and instead has a nonzero shared-spin fourth
cumulant, already computed in Lean.

An independence polynomial of a general claw-free graph is strictly more expressive.  Line graphs
recover matchings, but claw-free graphs also contain clique strips, circular-arc pieces, and
non-line-graph junctions.  Their weighted independence polynomials retain negative real zeros
without imposing Gaussian pairing closure.  This is therefore a genuine positive successor, not a
renaming of the failed dimer model.

## Finite consumer

For a finite graph `G`, positive vertex weights `w_v`, and activity `u`, put

```text
I_(G,w)(u) = sum_(S independent in G)
               (product_(v in S) w_v) u^|S|.
```

Leake--Ryder's same-phase stability theorem says that the multivariate independence polynomial is
same-phase stable exactly for claw-free graphs.  In particular, if `G` is claw-free and every
`w_v>=0`, then `I_(G,w)` is real-rooted.  Its coefficients are nonnegative and its constant term is
one, so every root is strictly negative.

This weighted theorem is the load-bearing enlargement beyond Heilmann--Lieb.

## The closed chain

Let `A` be the normalized entire square-coordinate function

```text
XiC(z)/XiC(0)=A(-z^2),
A(u)=sum_(n>=0) thetaCuspRawEvenMoment(n)/((2n)! thetaCuspRawEvenMoment(0)) u^n.
```

The proposed route is

```text
finite completed prime-word packets
  -> vertices carrying positive Gamma/theta-completed weights
  -> a source incompatibility relation, before Xi zeros are known
  -> finite claw-free conflict graph G_N                       [OPEN CORE A]
  -> weighted independence polynomial I_N(u)
  -> every zero of I_N is negative real                        [KNOWN]
  -> I_N -> A locally uniformly on every compact set,
     with constant terms normalized to one                     [OPEN CORE B]
  -> Hurwitz: A is nonzero off the closed negative ray
  -> A(0)=1 excludes a zero at the origin
  -> every zero of A is negative real
  -> every XiC zero is real by XiC(z)/XiC(0)=A(-z^2)
  -> RH.
```

Conversely, RH gives the paired product

```text
A(u)=product_gamma (1+u/gamma^2),
```

which is a locally uniform limit of weighted independence polynomials of edgeless graphs.  This
closes the other end but is not an admissible producer because its vertex weights were read from
the Xi divisor.  The new theorem must construct the graphs and weights from the completed source.

## The obvious conflict graph fails, exactly

Take one vertex for every retained prime support and join two vertices when their supports
intersect.  This graph need not be claw-free.  The four supports

```text
C={0,1,2},       L_0={0},       L_1={1},       L_2={2}
```

induce a claw: `C` meets all three leaves, while the leaves are pairwise disjoint.  Thus arbitrary
support intersection is closed as a producer.  Lean proves both this explicit claw and the sharp
general lower bound: any such centered support claw forces at least three distinct labels in its
center.

The no-go has a positive structural statement.  A conflict graph is claw-free exactly when no
packet conflicts with three mutually compatible packets.  A sufficient source-local form is

```text
the conflict neighborhood of every packet is the union of at most two cliques.       (2C)
```

Condition `(2C)` says that every completed packet has two boundary ports and every conflict is
registered at one of those ports.  For pure two-prime supports this collapses to a line graph and
therefore to the failed matching route.  A live construction must use completion-dependent clique
junctions or circular clique strips that satisfy `(2C)` but are not line graphs.  The positive
two-port residue is formalized: a support of cardinality at most two cannot be the center of a raw
intersection claw.

## Candidate completed source construction

Order the finite prime labels by `log p` and retain the full multivariate support marker.  Split a
completed word at its functional-equation seam into two boundary profiles:

```text
left port  = incoming prime/Gamma profile,
right port = reflected outgoing prime/Gamma profile.
```

Packets sharing a port cell form a clique.  Neighboring cells are welded by the graded
completion/parity sector, producing a clique strip.  The intended rules are:

1. every packet has exactly two port cells;
2. every conflict is witnessed at a port cell;
3. same-port conflicts are a clique, proving `(2C)`;
4. completion junctions retain the formal four-point shared-spin interaction, so the graph need
   not be a line graph;
5. deletion of the largest prime aperture induces the preceding graph and preserves weights;
6. independent-set sums equal the completed theta coefficients through the retained depth.

The first decisive object is a finite non-line-graph claw-free gadget for four labels whose
weighted two- and four-support coefficients reproduce the completed source and whose extra clique
junction accounts for the formal Wick defect.  If no such gadget exists, the route is closed before
any limit argument.

## Positive interpretation through frustration graphs

There is an equivalent quantum-spin face.  Treat prime-word packets as Hamiltonian terms and join
two vertices when the terms anticommute.  A claw-free frustration graph has commuting
independent-set charges, and in the even-hole-free subclass the weighted independence polynomial
determines a free-fermion spectrum.  The completed source would then produce

```text
prime/Gamma anticommutation constraints
  -> claw-free frustration graph
  -> commuting higher independent-set charges
  -> real single-particle energies
  -> negative roots of I_N
  -> RH in the source limit.
```

This is a static graded-constraint formulation.  The Hamiltonian language is optional and cannot
replace the coefficient and local-uniform-limit identities.

## Attacks and positive successors

1. **Induced-claw attack.**  Arbitrary support intersection contains the explicit four-vertex
   claw above.
   **Positive successor:** prove the two-clique neighborhood law `(2C)` from a two-port completion
   or record the minimal offending triple as a source frustration coordinate.
2. **Line-graph collapse attack.**  If every packet is only an edge between ports, the construction
   is a matching polynomial and the four-point Wick defect returns.
   **Positive successor:** require and exhibit a finite completion junction that is claw-free but
   not a line graph and carries the higher interaction.
3. **Inverse-graph attack.**  Under RH, edgeless graphs realize the product by using reciprocal
   squared zero ordinates as weights.
   **Positive successor:** define vertices, conflicts, and weights before any Xi divisor or finite
   polynomial factorization is read.
4. **Coefficient-fitting attack.**  Solving finitely many weighted independent-set equations is
   not a source theorem.
   **Positive successor:** derive every coefficient as a direct independent-set sum from the same
   port rule and prove aperture compatibility.
5. **Claw-free-but-wrong-limit attack.**  Finite negative roots do not identify the limit with Xi.
   **Positive successor:** prove locally uniform convergence to the already source-defined theta
   series `A`, not convergence of free energies or a bounded number of coefficients.
6. **Vanishing-limit attack.**  Hurwitz gives no information if the normalized polynomials tend to
   zero.
   **Positive successor:** keep constant term one and establish compact normality from source
   weight bounds.
7. **Signed-weight attack.**  Same-phase stability gives real roots only after specializing along
   a common nonnegative phase.
   **Positive successor:** move all orientation into the global square-coordinate rotation and
   keep each vertex activity nonnegative; otherwise retain a signed frustration invariant and
   retire this consumer.
8. **Origin attack.**  Forced monomer factors can create an origin zero in matching
   normalizations.
   **Positive successor:** independence polynomials already have constant term one; preserve this
   normalization cofinally.

## Primary parent results

- J. Leake and N. Ryder, *Generalizations of the Matching Polynomial to the Multivariate
  Independence Polynomial*, <https://arxiv.org/abs/1610.00805>;
- M. Chudnovsky and P. Seymour, *The roots of the independence polynomial of a clawfree graph*,
  J. Combin. Theory Ser. B 97 (2007), 350--357,
  <https://doi.org/10.1016/j.jctb.2006.06.001>;
- S. J. Elman, A. Chapman, and S. T. Flammia, *Free fermions behind the disguise*,
  <https://arxiv.org/abs/2012.07857>, for the weighted frustration-graph spectral face.

## Formal certificate

`PrimeWordClawFreeConflictNoGo.lean` proves:

- `supportConflict_claw_forces_three_le_card`;
- `not_isSupportConflictClaw_of_card_le_two`;
- `primeWordSupportConflict_explicit_claw`;
- `primeWordSupportConflict_no_claw_of_center_card_le_two`.

The exact module build is green.  Axiom audits report only `propext`, `Classical.choice`, and
`Quot.sound`.  The formal theorem has its own stage-3 card at
`../../../3-formalized/not_new_scientific_knowledge/prime-support-conflict-claw-threshold.md`.

## Kill conditions

Retire the direct support graph because of the explicit claw.  Retire the two-port repair if it
collapses to a line graph, if the first four-label completed gadget cannot reproduce the source
interaction with nonnegative weights, or if a source-canonical aperture creates an induced claw.
Retire the limit if graph data are reconstructed from Xi zeros, if only finite coefficient/free
energy convergence is available, or if the compact limit is not exactly `A`.  Preserve any
source-derived claw-free subfamily, commuting independent-set charge, or minimal induced-claw
frustration as a positive theorem.

## Gates

- [x] weighted claw-free finite consumer verified
- [x] two-ended limit-to-RH chain closed
- [x] direct prime-support conflict graph killed by an explicit formalized claw
- [x] sharp support-cardinality lower bound and positive two-port no-claw theorem formalized
- [x] positive two-clique-neighborhood repair isolated
- [x] strict enlargement beyond line graphs/matchings specified
- [ ] first completion-sensitive non-line-graph claw-free gadget constructed
- [ ] four-label source coefficient identity and nonnegative weights verified
- [ ] cofinal claw-free port rule proved
- [ ] locally uniform hard-core partition limit identified with `A`
- [ ] RH capstone formalized
