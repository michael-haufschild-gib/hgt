# Noninvertible events require a complementary record

- **ID:** `noninvertible-event-complementary-record-boundary`
- **Stage:** 2-fully-proven
- **Type:** EXACT LINEAR-ALGEBRA NO-GO / MINIMAL-RECORD CLASSIFICATION / PHYSICS BRIDGE
- **Status:** `[PAPER-PROVED] [LEAN-PROVED] [REDISCOVERED] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Parent:** `../../1-in-progress/actuality-creates-future-law.md`
- **Physics target:** `../../1-in-progress/purity-boundary-theory-of-everything.md`
- **Lean target:** `formal/GaloisForLFunctions/HTGeometry/EventComplementaryRecord.lean`

## Exact theorem

Let \(K\) be a field and let \(V,W,E\) be finite-dimensional \(K\)-vector spaces.  Let
\[
T:V\longrightarrow W
\]
be an event map.

### 1. Postcomposition cannot recover an event kernel

For every future linear continuation \(F:W\to X\),
\[
\ker T\subseteq\ker(F\circ T).                                    \tag{1}
\]
Consequently, if a family of future continuations \(\{F_i\}\) jointly separates all source
vectors through the reports \(F_iT\), then \(T\) is injective.

### 2. Every faithful record must contain the event kernel

Let \(R:V\to E\) be an additional record channel and define
\[
D=(T,R):V\longrightarrow W\oplus E.
\]
If \(D\) is injective, then the restriction
\[
R_K:=R|_{\ker T}:\ker T\longrightarrow E                         \tag{2}
\]
is injective.  Hence
\[
\dim E\geq\dim\ker T.                                             \tag{3}
\]

### 3. The minimal same-parent record pairs kernel and cokernel

Assume \(\dim V=\dim W\), and put
\[
C=\operatorname{coker}T=W/\operatorname{im}T.
\]
Rank--nullity gives
\[
\dim C=\dim\ker T.                                                \tag{4}
\]
Therefore, if \(R:V\to C\) makes \((T,R)\) injective, then
\[
R_K:\ker T\xrightarrow{\;\sim\;}C                               \tag{5}
\]
is a linear isomorphism.

In particular, if \(V\) and \(W\) both have dimension ten and \(T\) has rank six, then
\[
\dim\ker T=\dim\operatorname{coker}T=4,                           \tag{6}
\]
and every faithful record using only the cokernel is exactly four-dimensional and pairs all four
lost source directions with all four created target directions.

### 4. A bare event map cannot canonically choose the pairing

Suppose \(K=\mathbb C\), \(\ker T\neq0\), and \(\operatorname{coker}T\neq0\).  Choose a splitting
\[
V=\ker T\oplus L.
\]
For every \(\lambda\in\mathbb C^\times\), the automorphism
\[
a_\lambda=\lambda\,\operatorname{id}_{\ker T}\oplus
\operatorname{id}_L
\]
satisfies \(T a_\lambda=T\).  It changes no bare event-map datum on \(W\) or its cokernel.

If a proposed canonical map
\[
\beta_T:\ker T\longrightarrow\operatorname{coker}T
\]
were natural under every automorphism of the bare event map, then
\[
\beta_Ta_\lambda|_{\ker T}=\beta_T.
\]
Choosing \(\lambda\neq1\) and using linearity gives
\[
(\lambda-1)\beta_T=0,
\]
hence \(\beta_T=0\).  Thus no nonzero, and therefore no invertible, kernel--cokernel record pairing
is selected by \(T\) alone.

## Proof

If \(v\in\ker T\), then
\[
(F\circ T)(v)=F(0)=0,
\]
which proves `(1)`.  If the composites \(F_iT\) jointly separate points and \(Tv=Tv'\), every
report agrees on \(v,v'\); joint separation gives \(v=v'\), so \(T\) is injective.

Now suppose \(D=(T,R)\) is injective.  If \(v\in\ker T\) and \(R_K(v)=0\), then
\[
D(v)=(Tv,Rv)=(0,0).
\]
Injectivity gives \(v=0\).  Therefore \(R_K\) is injective, proving `(2)`.  Finite-dimensional
dimension monotonicity under injective linear maps proves `(3)`.

Rank--nullity and quotient dimension give
\[
\dim V=\dim\operatorname{im}T+\dim\ker T,
\qquad
\dim W=\dim\operatorname{im}T+\dim\operatorname{coker}T.
\]
Subtracting and using \(\dim V=\dim W\) proves `(4)`.  The injective map `(2)` is between spaces
of equal finite dimension, so it is bijective, proving `(5)`.  Substituting
\(\dim V=\dim W=10\) and \(\dim\operatorname{im}T=6\) proves `(6)`.

The scaling argument above proves item 4.  \(\square\)

## Sharpness and existence

The dimension bound is sharp but not canonical.  Choose complements
\[
V=\ker T\oplus L,\qquad W=\operatorname{im}T\oplus C_0.
\]
The restriction \(T|_L:L\to\operatorname{im}T\) is an isomorphism.  When
\(\dim V=\dim W\), choose any isomorphism \(q:\ker T\to C_0\), identify \(C_0\) with
\(\operatorname{coker}T\), and define \(R\) to equal \(q\) on \(\ker T\) and zero on \(L\).
Then \((T,R)\) is injective and `(3)` is equality.

Changing the complements or \(q\) changes the record.  Existence is ordinary finite-dimensional
linear algebra; physical selection is the entire open problem.

## Hostile novelty audit

`[NOT NEW MATHEMATICS]`

Equations `(1)`--`(6)` are rank--nullity, quotient dimension, and observability of a linear map.
The quantum analogue is occupied much more strongly:

1. Stinespring dilation represents every quantum channel by an isometry into a larger
   system--environment carrier.
2. Minimal Stinespring representations are unique only up to an environment isometry/unitary,
   matching the noncanonicity exposed above.
3. Braunstein--Pati's no-hiding theorem shows that quantum information removed from a subsystem
   cannot be hidden only in correlations; under its hypotheses it resides in the rest of the
   system.
4. Information--disturbance and complementary-channel theorems classify when information lost to
   one channel is available to its complement.

Primary sources:

- W. F. Stinespring, *Positive functions on \(C^*\)-algebras*, Proc. AMS **6** (1955).
- D. Kretschmann, D. Schlingemann, and R. F. Werner,
  *The information-disturbance tradeoff and the continuity of Stinespring's representation*,
  arXiv:quant-ph/0605009.
- S. L. Braunstein and A. K. Pati,
  *Quantum information cannot be completely hidden in correlations: implications for the
  black-hole information paradox*, arXiv:gr-qc/0603046.

No novelty may be claimed for the linear record bound, kernel--cokernel equality, dilation,
complementary channels, no-hiding, or environment records.

## Exact consequence for the universal future-creation law

The candidate universal clause

> every real distinction has a future consequence

has two bad readings:

1. after quotienting source states by equality of all future reports, it is true by definition;
2. for an independently defined source and an ordinary noninjective event map, it is false by
   `(1)`.

The \(4/6/4\) exceptional event cannot escape this boundary.  If its four-dimensional kernel
contains genuine pre-event physical distinctions, no history formed only by postcomposing the
rank-six map can ever observe them.  Calling its four-dimensional cokernel “created spacetime”
does not repair the loss because \(T\) supplies no map from kernel to cokernel.

The strongest positive survivor is:

> **A noninvertible actuality law needs a source-derived complementary record channel.  At the
> minimal rank-six ten-to-ten boundary, that record is necessarily four-dimensional and must pair
> the lost event kernel with the created event cokernel.**

This does not identify that record with spacetime.  It identifies the precise extra datum without
which “spacetime records ruled-out possibilities” is mathematically false.

## Stronger physical conjecture exposed by the no-go

`[CONJECTURE; NOT PROVED BY THIS CARD]`

> **CANONICAL COMPLEMENTARY-RECORD LAW.** Every elementary physical actualization carries a
> source-derived minimal complementary channel that re-encodes every quantum distinction removed
> from its local continuation process into newly created causal comparison data.  The complete
> history of these records is spacetime.  Gravitational curvature is the nonintegrability of
> comparing the complementary records between events; the three internal gauge curvatures are the
> irreducible automorphism curvatures of the retained source data; and their mixed curvature is the
> Higgs--soldering conversion.

Public law:

> **Spacetime is the record every quantum event leaves behind.**

Stronger headline:

> **Every event writes the quantum possibility it destroys into spacetime.**

This conjecture survives the exact kernel no-go because the physical event is no longer the bare
map \(T\); it includes the complementary record.  It survives fixed-carrier and Grothendieck
totalization attacks only if the record pairing and its gluing curvature are source-natural
physical invariants, not arbitrary mathematical dilations.

## New open core

`[OPEN CORE: SOURCE-NATURAL COMPLEMENTARY EVENT RECORD]`

Construct, or prove impossible, one event-source structure that:

1. canonically breaks the independent kernel/cokernel automorphism gauge and selects the
   nondegenerate pairing `(5)`;
2. promotes the linear record to a completely positive, probability-preserving quantum
   complementary channel without assuming a background environment;
3. derives the four-dimensional created record as Lorentzian causal data, not an ancilla label;
4. derives exactly \(S(U(2)\times U(3))\) on the retained/internal data and no peer factors;
5. makes one gluing curvature yield gravity and all three gauge forces;
6. recovers unitary quantum mechanics, objective actualization, and
   Einstein--Dirac--Yang--Mills--Higgs dynamics in their tested regimes;
7. handles horizons, topology, cosmology, and baby-universe sectors; and
8. fixes one finite dimensionless observable beyond GR plus the Standard Model.

The exceptional cubic norm, compatible pure pair, event orientation, determinant line, or a
source-derived duality are candidate selectors.  None currently closes item 1.

## Lean boundary

Items 1--3 and the rank-six specialization have complete paper proofs and should be formalized
unconditionally.  Item 4's naturality no-go may be formalized as the exact scaling-invariance
lemma after its automorphism interface is fixed.

The physical complementary-record law is not ready for Lean.  No physical assumption may be
introduced as a Lean axiom or hypothesis and then advertised as proof.

The exact boundary is now formalized in
`formal/GaloisForLFunctions/HTGeometry/EventComplementaryRecord.lean` through:

- `eventKernel_le_postReportKernel`;
- `eventRecordOnKernel_injective`;
- `eventRecord_finrank_lower_bound`;
- `eventKernel_finrank_eq_coker_of_equal_finrank`;
- `eventRecordOnKernel_bijective_of_combined_injective`;
- `rankSixEvent_recordOnKernel_bijective`; and
- `linearRecord_eq_zero_of_scaling_invariant`.

The module contains no physical axioms.  Its declarations use only Lean's standard logical
foundations.

## Gates

- [x] exact statement and dependency-closed paper proof
- [x] sharpness and noncanonicity proved
- [x] hostile novelty audit: standard linear/quantum information mathematics
- [x] positive survivor and stronger physical conjecture extracted
- [x] exact mathematical theorem formalized unconditionally in Lean
- [ ] source-natural physical record constructed
- [ ] four-response continuum and finite prediction derived

## Log

- 2026-07-29 — future-completeness versus noninvertible-event contradiction isolated.
- 2026-07-29 — proved the minimal record bound and exact kernel--cokernel pairing at equal parent
  dimension.
- 2026-07-29 — proved that a bare event map cannot naturally select a nonzero pairing because of
  independent kernel scaling.
- 2026-07-29 — no-hiding and Stinespring audits classified the mathematical mechanism as occupied;
  retained “spacetime is the complementary event record” as the stronger physical conjecture.
- 2026-07-29 — formalized the complete linear boundary and scaling noncanonicity theorem in Lean;
  targeted module build, formal lint, and axiom audit passed.
