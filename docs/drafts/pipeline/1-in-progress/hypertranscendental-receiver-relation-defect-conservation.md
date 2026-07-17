# Hypertranscendental receiver-relation defect conservation

- **ID:** ht-receiver-relation-defect-conservation
- **Stage:** 1-in-progress
- **Type:** SUBORDINATE VERTICAL-CHART CONJECTURE
- **Source:** hypertranscendental-source-face-vanishing-cycle-conservation.md
- **Statement:** A regular source-minimal hypertranscendental object carries a canonical self-dual
  scale-indexed field of closed receiver relations and a universal defect section which cannot be
  destroyed by finite algebraic-differential or source-derived refinement, but can be transported
  among kernel, domain, multivalued, range-strictness, orientation, and monodromy components by a
  genuinely transverse receiver.

## Goal

Identify what constrains hypertranscendental functions themselves.  The proposed law is not a flow
and not reconstruction from a bare source.  It is conservation of a receiver-independent defect:
changing how an HT object is observed may move the obstruction between representations, but a
source-derived change cannot erase information already forgotten by the source.

This is the proposed mathematical object behind the recurrent obstruction classes, not an RH
claim.  An RH application is admissible only after the object and its conservation law have been
constructed for HT families independently of zeta.

## Scope correction

This card is not a second foundational field.  Its scale-indexed receiver relations are the
vertical analytic chart of
`hypertranscendental-polarized-strict-descent-field.md`.  Horizontal fracture, orientation, and
source-face descent remain in that parent object.  The purpose here is narrower: construct and
classify the vertical relation/cocone rigorously enough that its defect can be transported into
the parent field.  If it cannot be absorbed there, this card is an epicycle and must be retired.

## Gates

- [x] 0 -> 1 in-progress: exact source no-go, graph chart, Gamma variance discriminator, and
  falsifiable construction target
- [ ] 1 -> 2 fully-proven: canonical construction, conservation theorem, and nontrivial HT example
- [ ] 2 -> 3 formalized: core relation field and conservation theorem in Lean
- [ ] 3 -> 4 publication-ready: independent novelty review and a cross-family theorem

## Candidate generation and decisive discriminator

Four candidate carriers were compared.

1. **One source-derived completion.**  This fails the bare-source theorem: every endogenous
   reporter retains the source-fixed gauge in its joint kernel.
2. **One Hilbert or Tate completion with opposite lattices.**  This fails already for Gamma.
   Every nonconstant periodic Fourier derivative tail lies in the maximal cyclic Gamma-conormal
   domain but outside the factorial reporter `l2`; only the constant mode lies in both.
3. **A cofinal Hilbert scale with bounded reporter operators on every pivot.**  Gamma now supplies
   this exactly on finite nonnegative-frequency packets.  A packet enters precisely when all active frequencies
   lie below the pivot; the coefficient filtration jumps at the actual frequencies; strict bonds
   are compact and injective; and the factorial reporters form a compatible cocone with dense
   proper range at every scale.  Bounded operators alone still cannot encode non-domain,
   nonclosability, or multivalued continuation beyond that one-sided finite-packet chart.
4. **A self-dual scale-indexed field of closed linear relations.**  This is the surviving carrier.
   A relation records domain, range, kernel, and multivalued part without pretending that all
   gauge directions and reporters occupy one variance space.  A family or stack of such relations
   can also carry scale transition, monodromy, determinant orientation, and boundary
   specialization.

The decisive discriminator is whether one construction represents all exact Gamma phenomena
without identifying the actual periodic gauges with the factorial Hilbert pivot.  Candidate 3 is
now the proved one-sided finite-packet vertical chart; candidate 4 is the only surviving completion beyond
that chart.

## Proposed object

Let `S` be a source-minimal HT system, `G_S` its source-fixed gauge tangent, and `Rec_perp(S)` the
category of genuinely transverse receivers together with admissible scale parameters.  For each
`(R,rho)` the theory must construct, functorially and without using a target solution as data, a
closed linear relation

```text
Lambda_(S,R,rho) subset G_S' x H_(R,rho).
```

Its defect package is

```text
D(Lambda) = (
  kernel,
  multivalued part of the closure,
  complement of the closed domain,
  complement of the closed range,
  closure(range) / range,
  determinant orientation and holonomy
).
```

The package distinguishes failures that a bounded operator graph conflates.  In particular:

- a source ambiguity is a kernel component;
- a continuation or admissibility failure is a domain component;
- nonclosability creates a multivalued component in the closure;
- spectral incompleteness is a cokernel or nonclosed-range component;
- positivity failure is failure to orient the self-dual determinant line;
- monodromy is holonomy of that line or of the relation field;
- noncanonical boundary conditions are nonunique transverse selections of the same relation.

## Main conjecture

> **[CONJECTURE -- HT DEFECT CONSERVATION]** For every regular source-minimal HT system `S`, the
> relations `Lambda_(S,R,rho)` assemble into a canonical self-dual field over `Rec_perp(S)` with a
> nonzero universal section `delta_S` of its defect package.  Receiver transition maps may exchange
> the components of `delta_S`, but every finite algebraic-differential refinement and every
> receiver factoring through the bare source preserves a nonzero image of `delta_S`.  The section
> can vanish only on a source-effectively normalized stratum where the normalized joint-fixed
> gauge is trivial.

The bold strengthening to test is:

> **[CONJECTURE -- RECEIVER CHARACTERIZATION OF HT]** A germ is hypertranscendental exactly when
> its source-natural receiver field has no finite algebraic-differential stage on which the
> universal defect becomes both zero and stably split.  Differential-algebraic germs are precisely
> those for which such a finite conservative stable stage exists.

This characterization is not asserted as proved.  It is the point at which the proposal either
becomes a new theory of hypertranscendence or collapses into standard functional-analysis
vocabulary.

## Exact evidence already proved

1. **Source data processing.**  Source-derived reporters cannot distinguish a source-fixed gauge;
   joint reconstruction is equivalent to triviality of the normalized common reporter kernel.
2. **Linear relative-position chart.**  For a reporter `A`, its graph and the horizontal lattice
   have intersection `ker A`, sum equal to the product with `range A`, whole sum exactly when `A`
   is surjective, and closed sum exactly when its range is closed.
3. **Gamma variance seam.**  The maximal cyclic Gamma-conormal domain has no coordinate-preserving
   realization in the factorial `l2`, and pure Fourier tails meet that pivot only in the constant
   mode.
4. **Gamma finite-packet horizon.**  A finite nonnegative-frequency packet enters radial pivot `rho` exactly when every
   active frequency lies below `rho`; no cancellation changes the wall.  Every such finite packet
   enters cofinally, and crossing a frequency strictly enlarges the coefficient space.
5. **Gamma compact radial system.**  Strict pivot transitions are compact and injective, compose
   exactly, and are unital.
6. **Gamma reporter cocone.**  `D_sigma T_(rho,sigma)=D_rho`, `D_1` is the factorial reporter, and
   every positive-scale `D_rho` is compact injective with dense proper nonclosed range.
7. **Gamma normalization horizon.**  Every finite horizon admits nontrivial normalized gauges,
   while the cofinal intersection is trivial.

Items 3--6 are now one exact vertical diagram rather than separate analogies.  Item 7 is not yet
proved to be another realization of the same `delta_Gamma`; that comparison, plus extension beyond
the current one-sided finite Fourier chart, is the next substantive theorem.

## Gamma theorem target

Extend the proved radial Hilbert cocone to compatible closed reporter relations
`Lambda_(Gamma,rho)` such that:

```text
domain-entry threshold of every packet in the one-sided finite chart = its wall;        [PROVED]
kernel at every pivot = 0;                                                             [PROVED]
closure(range) / range carries the factorial strictness class compatibly;              [PROVED]
the cofinal Hilbert system contains every packet in that one-sided chart;               [PROVED]
the projective dual contains the factorial conormal and its shifted family;
self-duality exchanges the domain boundary with the multivalued/cokernel boundary;
the nonlinear normalization horizon is a conservative nonlinear receiver of the same class.
```

The first four lines are proved.  The remaining three are the Fields-scale comparison.

## Novelty gate

Known parent theories include rigged Hilbert spaces, Silva/LS spaces, Köthe echelon and co-echelon
spaces, weighted spaces of entire functions, closed and multivalued linear relations, Fredholm
pairs, determinant lines, Maslov index, Tate objects, solution torsors, parameterized difference
Galois theory, and classical Gamma uniqueness conditions.  The Gamma mode-growth and
geometric-series arguments are also parent analysis.

Exact parent references checked include Chiba's rigged-Hilbert spectral theory
(`arXiv:1107.5858`), Celeghini--Gadella--del Olmo on special functions in rigged Hilbert spaces
(`arXiv:1907.01281`), and Hassi--Sebestyen--de Snoo--Szafraniec on the canonical decomposition of
linear relations (`arXiv:math/0611045`).

Targeted searches found these ingredients separately, including rigged-Hilbert treatments of
special functions and the canonical regular/singular decomposition of linear relations.  They did
not identify an HT-specific receiver category, a source-natural scale-relation assignment, a
universal defect section conserved across receiver changes, or the proposed receiver
characterization of hypertranscendence.  This is an absence finding and remains
`[NOVELTY PRELIMINARY]` pending specialist review.

The one-sided finite-packet wall, compact bonds, and diagonal cocone use parent Vandermonde, Silva, and
Hilbert--Schmidt mechanisms and are not isolated novelty claims.  The novelty candidate is exactly
the source-presentation-invariant HT assignment and a conservation theorem comparing two
independently constructed realizations.  Merely renaming standard kernels, cokernels, riggings,
relations, or indices fails the gate.

## Anti-theatre and kill criteria

Kill the main conjecture if any of the following occurs.

1. A natural HT example admits a finite, source-derived, total, conservative, stably split, and
   self-dual reporter, contradicting persistence of `delta_S`.
2. Two genuinely natural receiver realizations of the same HT source have no functorial common
   defect class beyond dimensions or zero sets.
3. The proved one-sided finite-packet Gamma cocone fails to extend to the full periodic gauge relation, and
   the maximal extension has no nontrivial conservative subcategory.
4. The proposed `delta_S` reduces to an ordinary Fredholm index and loses the source gauge,
   variance horizon, or orientation data.
5. The receiver characterization labels a known differential-algebraic germ as HT or a classical
   HT germ as finitely stably split.

Every kill has a required positive successor: determine the maximal receiver subcategory on which
the class is conservative, classify the exact singular or multivalued part, and state which defect
component fails to transport.

## RH pressure test, not an RH result

Different RH proof chains are representations of one object only if they construct conservative
receivers of the same `delta_S` before reading the Xi divisor.  Under that condition, spectral
incompleteness, continuation failure, positivity failure, monodromy, and noncanonical boundary
conditions can be different components of one self-dual relation defect.  The critical zeros would
then be the common self-dual degeneracy support of that field.

Even if this identification succeeds, RH still requires a new orientation theorem forcing that
support onto the fixed locus.  Neither the relation field nor its zeros may be inserted from RH as
defining data.

## Next proof obligations

- [x] falsify the single-pivot Gamma identification
- [x] formalize the exact pure-mode variance horizon and no-terminal-pivot theorem
- [x] classify the radial `l2` intersection of every finite nonnegative-frequency packet, not only pure modes
- [x] construct compositional radial pivot transitions with compact-injective strict bonds
- [x] prove factorial reporter strictness is coherent across the radial scale through an exact
      reporter cocone
- [ ] construct the projective/inductive limits and identify their universal topology
- [ ] construct the Gamma reporter as a compatible closed relation on that scale
- [ ] compute its kernel, multivalued part, domain, range, and singular closure
- [ ] compare its defect section with the nonlinear normalization horizon
- [ ] formulate the receiver characterization in differential-algebraic jet language
- [ ] test it on one differential-algebraic family and one non-Gamma HT family
- [ ] obtain an independent specialist novelty audit

## DA-control falsifier and corrected receiver conjecture

The receiver characterization stated above is false on the bare source category.  The pointed DA
exponential pair has the same periodic-gauge source inertia and admits the same source-symbol
kinematics as the Gamma pair.  Thus a receiver field assigned before DA neutralization can carry a
nonzero kernel, nonclosed range, or horizon defect on a DA object; that cannot characterize HT.

The exact positive correction is to build receiver relations on the DA-relative cyclic module

```text
q=[f] in M/M_DA,
G_S^HT=G_S/(G_S intersect M_DA),                            (R1)
```

and to require joint conservativity only on `(R1)`.  The Lean quotient theorem says this is
precisely the condition that every source-fixed common-reporter gauge be DA.

> **[CONJECTURE -- CORRECTED RECEIVER CHARACTERIZATION OF HT]** A regular finitely sourced germ is
> HT exactly when its pointed DA-relative cyclic class is nonzero and its source-natural receiver
> relation field has no finite algebraic-differential stage at which that nonzero class becomes
> zero and stably split.  For conormally integrable systems, the universal defect section is the
> image of the oriented derived conormal class of the independently given source law.

This is falsified by any DA control with a nonzero post-DA defect, or by an HT example whose
nonzero DA-relative class admits a finite conservative stable source-natural realization.  The
positive theorem after either failure is the exact maximal quotient receiver category and the
classification of which non-DA classes it loses.
