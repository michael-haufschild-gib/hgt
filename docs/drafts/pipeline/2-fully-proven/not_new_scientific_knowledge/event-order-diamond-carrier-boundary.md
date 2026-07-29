# Typed event-order diamonds are gauge-covariant but select no force

- **ID:** `event-order-diamond-carrier-boundary`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / CARRIER CLASSIFICATION / NO-SELECTION BOUNDARY
- **Parent:** `../../1-in-progress/actuality-order-curvature-law.md`
- **Scientific status:** `[PAPER-PROVED] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Statement:** A two-history defect through different intermediate event types is covariant under
  arbitrary vertex-frame changes and needs no inverse event, but every linear map occurs as such a
  defect; only a derived event law can give it physical content.

## Goal

Identify the weakest background-free algebraic carrier that can compare two complete event
histories without:

1. pretending that noninvertible actualizations have inverses;
2. collapsing every order comparison to one finite-dimensional commutator;
3. losing the Abelian channel by trace cyclicity; or
4. inserting a spacetime manifold before event order is defined.

This card proves a carrier theorem, not the frozen physical conjecture. It also proves the exact
no-selection boundary: typed order diamonds are flexible enough to carry curvature but too
flexible to derive any force.

## Typed event diamond

Let \(R\) be a commutative ring and let \(S,A,B,T\) be \(R\)-modules. A typed event diamond is

\[
\begin{array}{ccccc}
 & & S & &\\
 & {}^{a}\swarrow & & \searrow^{b} &\\
 A & & & & B\\
 & {}_{b_a}\searrow & & \swarrow_{a_b} &\\
 & & T. & &
\end{array}
\]

The subscripts matter. The operation available after \(a\) is a map
\(b_a:A\to T\), while the operation available after \(b\) is
\(a_b:B\to T\). Primitive actualization is allowed to change the type and the admissible future.
Define

\[
  \Delta(a,b_a;b,a_b):=b_a a-a_b b\in\operatorname{Hom}_R(S,T).       \tag{1}
\]

No event map in `(1)` is assumed invertible.

## Theorem A: endpoint covariance and intermediate-gauge cancellation

Choose arbitrary linear equivalences at all four vertices,

\[
g_S:S\overset{\sim}{\longrightarrow}S',\quad
g_A:A\overset{\sim}{\longrightarrow}A',\quad
g_B:B\overset{\sim}{\longrightarrow}B',\quad
g_T:T\overset{\sim}{\longrightarrow}T',
\]

and transform an edge \(f:X\to Y\) by

\[
  f^g:=g_Y f g_X^{-1}.                                               \tag{2}
\]

Then

\[
\Delta(a^g,b_a^g;b^g,a_b^g)
  =g_T\,\Delta(a,b_a;b,a_b)\,g_S^{-1}.                               \tag{3}
\]

Consequently \(\Delta=0\) is independent of every vertex frame. The two intermediate gauges
\(g_A,g_B\) cancel completely; only endpoint covariance remains.

### Proof `[PROVED HERE]`

Along the upper-left path,

\[
  b_a^g a^g
  =(g_Tb_ag_A^{-1})(g_Aag_S^{-1})
  =g_T(b_aa)g_S^{-1}.
\]

The same cancellation gives \(a_b^g b^g=g_T(a_bb)g_S^{-1}\). Subtraction proves `(3)`.
Since \(g_S\) and \(g_T\) are equivalences, `(3)` vanishes exactly when `(1)` vanishes. No inverse
of \(a,b,b_a,\) or \(a_b\) is used.

## Theorem B: common history attachment

For any \(p:P\to S\) and \(q:T\to Q\),

\[
\begin{aligned}
\Delta(ap,b_a;bp,a_b)&=\Delta(a,b_a;b,a_b)\,p,\\
\Delta(a,qb_a;b,qa_b)&=q\,\Delta(a,b_a;b,a_b).
\end{aligned}                                                       \tag{4}
\]

### Proof `[PROVED HERE]`

Both identities follow by associativity and distributivity of linear-map composition:
\[
b_a(ap)-a_b(bp)=(b_aa-a_bb)p,
\quad
(qb_a)a-(qa_b)b=q(b_aa-a_bb).
\]

Thus adjoining the same earlier or later history cannot create an independent order term.

## Theorem C: the fixed-type reduction loses the central channel

Suppose all four vertices are one finite free module and the two events ignore their history:
the map called \(a\) is the same before and after \(b\), and likewise for \(b\). Then

\[
  \Delta=B A-A B.                                                     \tag{5}
\]

For finite matrices over a commutative ring,

\[
  \operatorname{tr}\Delta=0.                                        \tag{6}
\]

### Proof `[PROVED HERE / LEAN SOURCE AVAILABLE]`

Equation `(5)` is definitional. Equation `(6)` is trace cyclicity. Its unconditional Lean theorem
is `LieAlgebra.matrix_trace_commutator_zero` in
`Mathlib/Algebra/Lie/Classical.lean`; the event specialization is included in the formal module
for this card.

Therefore a continuous central \(U(1)\) curvature cannot be recovered from a plain finite matrix
commutator. A viable actuality-order carrier must retain context-dependent edges, nontrivial
gluing, relative boundary data, or an amplitude line.

## Theorem D: universality and no-selection

Every linear map \(D:S\to T\) is a typed event-order defect. Indeed, take

\[
  A=B=S,\qquad a=\operatorname{id}_S,\qquad b_a=D,\qquad b=0,\qquad a_b=0.
\]

Then

\[
  \Delta(\operatorname{id}_S,D;0,0)=D.                               \tag{7}
\]

### Proof `[PROVED HERE]`

Substitution into `(1)` gives \(D\operatorname{id}_S-0\cdot0=D\).

## Theorem E: every finite typed diamond has a fixed-carrier dilation

Let

\[
  W:=S\oplus A\oplus B\oplus T.
\]

Embed the source as \(\iota_S(s)=(s,0,0,0)\) and project the target by
\(\pi_T(s,a,b,t)=t\). Define four endomorphisms of \(W\):

\[
\begin{aligned}
\widehat a(s,a',b',t)&=(0,a(s),0,0),\\
\widehat b_a(s,a',b',t)&=(0,0,0,b_a(a')),\\
\widehat b(s,a',b',t)&=(0,0,b(s),0),\\
\widehat a_b(s,a',b',t)&=(0,0,0,a_b(b')).
\end{aligned}                                                       \tag{8}
\]

Then

\[
\begin{aligned}
\pi_T\widehat b_a\widehat a\iota_S&=b_aa,\\
\pi_T\widehat a_b\widehat b\iota_S&=a_bb,\\
\pi_T\big(\widehat b_a\widehat a-\widehat a_b\widehat b\big)\iota_S
  &=\Delta(a,b_a;b,a_b).                                            \tag{9}
\end{aligned}
\]

### Proof `[PROVED HERE]`

Each identity follows by direct substitution into the block maps `(8)`. No dimension,
invertibility, or field hypothesis is used.

Thus one finite typed diamond, including its complete linear order defect, is exactly reproducible
inside one larger fixed carrier. Typed notation by itself cannot establish physical carrier
change. A discriminating theory must add at least one structure that the block dilation does not
preserve: a canonical minimality/resource bound, positivity and normalization across all
interventions, locality, an all-history coherence law, an unbounded obstruction, or a
parameter-reducing continuum prediction.

## Exact boundary

The typed diamond closes three mathematical gaps:

1. it compares complete paths with common endpoints rather than pretending that individual
   noninvertible events can be inverted;
2. it is invariant at the level of vanishing and covariant at the level of the full defect under
   arbitrary vertex-frame changes; and
3. it permits a central component because the two paths need not form one endomorphism
   commutator.

Theorem D simultaneously kills the claim that this carrier itself explains a force. Without an
independently derived event object, allowed-edge rule, positivity/probability law, and continuum
limit, \(\Delta\) can be chosen to equal any desired curvature. Writing Einstein and
Standard-Model curvatures into four components of \(\Delta\) would be insertion, not unification.

Theorem E also kills a naive experiment claim. Observing one nonzero typed diamond cannot by
itself show that actualization changes the physical possibility carrier, because the complete
diamond admits the fixed-space block realization `(8)`. The finite-prediction frontier is now an
obstruction to every physically admissible fixed-carrier dilation, not merely detection of
\(\Delta\ne0\).

The correct open core is therefore:

> Derive the typed diamond and its admissible edges from one physical actualization law; then prove
> that its stable gauge-covariant orbit has exactly one external Lorentzian and three internal
> \(S(U(2)\times U(3))\) projections.

## Interchange pressure test

In a strict symmetric monoidal process theory, sequential and parallel composition obey exact
interchange. Coecke and Lal explicitly interpret these two compositions as temporal and spatial.
If two unital compositions live on the same carrier and satisfy strict interchange, the
Eckmann--Hilton theorem forces them to coincide and become commutative. Mathlib formalizes this as
`EckmannHilton.mul` and `EckmannHilton.mul_comm`.

Thus the frozen conjecture cannot identify gravity with failure of ordinary associative gluing or
with an arbitrary violation of categorical coherence. A viable physical structure needs typed
partial composition or a coherent nontrivial comparison between histories. Premonoidal and
bicategorical structures show that such mathematics exists, but no audited source derives
Einstein gravity and the exact Standard Model group from its comparison cell.

## Relation to amplitude calibration

Ordinary channel data is too coarse for the central phase. Araújo--Feix--Costa--Brukner show that
an unknown unitary supplied only as a black-box circuit is phase-blind, while a physical
implementation can carry extra subspace information that makes coherent control possible.
Determinant-line formulations of fermionic amplitudes likewise retain gluing data beyond a
projective state: Dai--Freed prove a determinant-line gluing and holonomy law, and
Mickelsson--Scott derive fermionic sewing from Dirac-determinant pasting.

These results support one requirement but do not close it: the event theory must derive the
amplitude calibration. Choosing a determinant/Pfaffian trivialization by hand would merely move
the \(U(1)\) insertion.

## Hypertranscendence boundary

Hypertranscendence is not local curvature. The arithmetic corpus already contains flat connections
with infinite holonomy, so differential-algebraic nonclosure cannot be equated with gravity.

The viable role is global and conditional:

\[
\text{local typed diamonds}
\longrightarrow \text{gauge-covariant history accumulation}
\longrightarrow \text{possible HT obstruction to finite global closure}.
\]

The missing theorem must first derive a canonical accumulated-history reporter. Only then may one
ask whether its Hypertranscendence is equivalent to irreducible interaction. No such reporter is
proved here.

## Literature boundary

- B. Coecke and R. Lal, *Causal categories: relativistically interacting processes*,
  <https://arxiv.org/abs/1107.6019>.
- H. Paquet and P. Saville, *Effectful Semantics in 2-Dimensional Categories: Premonoidal and
  Freyd Bicategories*, <https://arxiv.org/abs/2312.14964>.
- U. Schreiber and K. Waldorf, *Parallel Transport and Functors*,
  <https://arxiv.org/abs/0705.0452>.
- J. Baez and U. Schreiber, *Higher Gauge Theory: 2-Connections on 2-Bundles*,
  <https://arxiv.org/abs/hep-th/0412325>.
- M. Araújo, A. Feix, F. Costa, and Č. Brukner, *Quantum circuits cannot control unknown
  operations*, <https://arxiv.org/abs/1309.7976>.
- X. Dai and D. Freed, *Eta-Invariants and Determinant Lines*,
  <https://arxiv.org/abs/hep-th/9405012>.
- J. Mickelsson and S. Scott, *Functorial QFT, Gauge Anomalies and the Dirac Determinant Bundle*,
  <https://arxiv.org/abs/hep-th/9908207>.

The inspected sources establish process composition, weakened interchange, manifold-based
transport, higher holonomy, implementation-sensitive phase, and determinant-line gluing. They do
not establish the frozen physical identification. This is a preliminary collision audit, not a
priority certificate.

## Gates

- [x] 0 → 1: typed source/target data, gauge action, and exact hostile tests specified
- [x] 1 → 2: endpoint covariance, attachment laws, commutator boundary, and universality proved
- [x] 2 → 3: `EventOrderDiamond.lean`; focused build, axiom audit, and formal lint passed
- [ ] 3 → 4: not publication-ready; carrier theorem is standard algebra and no physics follows

## Log

- 2026-07-29 — extracted typed noninvertible diamond after plain-commutator, closed-debt, and
  strict-interchange pressure tests. Proved gauge covariance and exact no-selection theorem.
- 2026-07-29 — formalized the complete paper statement in
  `HTGeometry/EventOrderDiamond.lean`; focused module build passed 2954/2954, with only standard
  Mathlib axioms.
- 2026-07-29 — proved the fixed-carrier block-dilation theorem for every single typed diamond.
  Tightened the finite-prediction frontier: nonzero order defect alone cannot witness physical
  carrier change.
