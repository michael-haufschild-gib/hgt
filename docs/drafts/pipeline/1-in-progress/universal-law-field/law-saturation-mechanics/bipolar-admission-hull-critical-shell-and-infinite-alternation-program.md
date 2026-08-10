# Bipolar admission hull, critical shell, and infinite-alternation programme

- **ID:** ULF-LSM-7-PROGRAM
- **Stage:** 1-in-progress
- **Type:** MECHANISM CONJECTURE / HOSTILE PROOF LANE
- **Status:** [PAPER CORE CLOSED IN ULF-LSM-7] [LEAN MECHANISM CORE CLOSED]
  [DOCTRINE-RELATIVE EXTENSION OPEN]
  [MECHANISM NOT OBJECT] [NOT RH]

## 1. Exact frontier

ULF-LSM-6 closes finite endogenous interference: source operations generate both the
identifications and the exchange reporter that their joint unitization erases.  ULF-GTM-3 proves
that finite continuous formation depth commutes with compact Hausdorff completion.  Neither theorem
answers Target 3 of Bipolar Law Formation:

> can every finite admission problem be continuously realizable, and the global set-theoretic
> problem remain realizable, while analytic admission alone kills the canonical reporter?

The required mechanism must name the analytic property that fails.  Bare compactness, an arbitrary
topology on a conflict graph, or a declared discontinuous observer does not count.

## 2. Competing conjectures and hostile verdicts

### Conjecture A — closed unitizations are closed under joint saturation

If `E` and `F` are closed equivalence relations on a compact Hausdorff space, their algebraic join
`Eq(E union F)` is closed.

**Verdict:** [FALSIFIED].  On the two-ended compactification of the integers, let `E` pair
`2k` with `2k+1` and let `F` pair `2k-1` with `2k`, leaving both ends fixed.  Each relation is
closed.  Their join has one class containing every integer and two singleton end classes.  The
integer class is dense, so the join is not closed.

**Exact why:** every bounded alternating path relation is closed, but required path lengths diverge
towards the two ends.

### Conjecture B — finite analytic realizability plus global algebraic realizability implies global
analytic realizability

**Verdict:** [FALSIFIED] by finite truncations of the same two-ended system.  At every truncation,
the endpoint conflict has an exact continuous `[0,1]` observer.  At the cofinal limit, the set
quotient still distinguishes the ends, but every continuous observer unitizing both limiting
relations is constant.

**Exact why:** the algebraic join is not analytically effective.  Its least admitted closed
equivalence enlargement crosses the conflict edge.

### Stronger conjecture C — bipolar admission theorem

For compact Hausdorff `X` and primitive relation `R`, put

`R^perp = {f in C(X,R) : R(x,y) implies f(x)=f(y)}`

and

`R^perp-perp = {(x,y) : every f in R^perp has f(x)=f(y)}`.

Conjecture:

1. `R^perp-perp` is the least closed equivalence relation containing `R`;
2. the algebraic quotient is conflict-lossless exactly off `Eq(R)`;
3. a continuous Hausdorff observer is conflict-lossless exactly off `R^perp-perp`;
4. the **analytic critical shell**
   `R^perp-perp \ Eq(R)` is therefore the exact admission-only loss;
5. every Dirac conflict in the shell has source total variation one and observed total variation
   zero under every admitted unitizing observer.

**Preliminary verdict:** SURVIVES CORRECTNESS ATTACK; parent machinery is occupied.  The closed
relation lattice and its dual invariant-function algebra are classical.  The claimed field delta
is only the exact conjunction with source-generated conflict, cofinal finite realizability,
formation depth, and reporter loss.  It must produce a dependency-closed theorem and a withheld
response before promotion.

## 3. Proposed geometric mechanism

The primitive is a pair of polar operations, not a new stored object:

1. **formation:** generate equality paths from executable source operations;
2. **admission:** close equality under every continuous scalar reporter;
3. **criticality:** intersect the admission increment with declared/source-generated distinctions.

Joint formation acts contravariantly on reporters:

`(R join S)^perp = R^perp intersect S^perp`.

Thus a mixed analytic term can appear even when each primitive relation is already admitted: the
intersection of their reporter algebras may lose a distinction that each algebra retained.

## 4. Paper core closure

All five obligations below are closed in the companion Stage-2 card
`bipolar-admission-hull-critical-shell-and-infinite-alternation-law.md`:

1. prove the bipolar equality with the least closed equivalence hull without assuming metrizability;
2. prove the exact conflict-realizability equivalences and TV response;
3. close the two-ended cofinal countermodel, including closedness of both limiting primitive
   relations and uniform finite-stage observers;
4. prove the unbounded alternating-depth law near the critical pair;
5. audit against Hausdorff reflection, Shilov closed-equivalence duality, de Vries duality, closed
   relation allegories, and continuous chromatic-number theory.

The remaining Stage-1 open core is doctrine-relative: replace continuous real reporters by
positive, holomorphic, smooth, bounded-domain, or differential reporter doctrines and determine
when their bipolar hulls exchange or produce genuinely different critical shells from one source.

Lean certification now covers the coordinate-free scalar bipolar theorem and a one-ended cofinal
critical shell with continuous source operations, exact finite margin one, pointwise escape from the
admitted reporter space, and exact global half-gap.  General closed-equivalence minimality,
measure-theoretic Dirac-TV, the two-ended paper model, and bounded alternation remain paper-only.

## 5. Parent mathematics and collision boundary

- closed equivalence relations and compact Hausdorff quotients are classical;
- Shilov/Gelfand duality identifies closed equivalences with invariant self-adjoint subalgebras of
  `C(X)`;
- Abbadini--Bezhanishvili--Carai, *A generalization of de Vries duality to closed relations between
  compact Hausdorff spaces*, arXiv:2206.05711, supplies the modern closed-relation/allegory parent;
- Lecomte, *Continuous 2-colorings and topological dynamics*, arXiv:2307.00851, shows that
  continuous coloring already has rich topological-dynamical obstructions;
- lattices of closed quasiorders/equivalences were studied long before this programme.

Therefore neither the hull nor its reporter algebra may be advertised as new mathematics.  The
lane survives only if the interference theorem forces a new exact source-to-admission prediction.

## Log

- 2026-08-10 — Target 3 isolated after ULF-LSM-6.
- 2026-08-10 — closed-join and finite-to-global analytic conjectures falsified by the two-ended
  alternating chain; bipolar admission theorem selected as stronger survivor.
- 2026-08-10 — survivor closed on paper as ULF-LSM-7; doctrine-relative extension remains live.
- 2026-08-10 — scalar bipolar mechanism and one-ended cofinal critical shell certified in Lean;
  Target 3 mechanism core closed, doctrine-relative admission selected as next lane.
