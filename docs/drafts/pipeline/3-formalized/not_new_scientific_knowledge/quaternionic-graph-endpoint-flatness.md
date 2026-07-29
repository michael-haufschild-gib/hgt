# Event-selected quaternionic frames have canonically flat endpoint transport

- **ID:** `quaternionic-graph-endpoint-flatness`
- **Stage:** 3-formalized
- **Type:** EXACT NO-GO / POSITIVE CLASSIFICATION / NOT NEW SCIENTIFIC KNOWLEDGE
- **Parent:** `../../1-in-progress/actuality-conservation-boundary-colligation-law.md`
- **Status:** `[PAPER-PROVED] [LEAN-PROVED] [BRIDGE]`

## Question

The parent conjecture lets a unit quaternion \(q\) selected by an event determine its graph
stabilizer
\[
\Delta_q=\{(u,q^\ast u q):u\in\mathbb U\}
\subset \mathbb U_L\times\mathbb U_R,
\]
where
\[
\mathbb U=\{u\in\mathbb H:\lVert u\rVert^2=1\}
\]
and
\[
(u,v)\cdot x=uxv^\ast.                                     \tag{1}
\]
Can disagreement between endpoint-selected graph stabilizers itself carry gravitational
holonomy?

The answer is no for the point-derived comparison alone. The event directions admit an exact
canonical flat transport. Any nontrivial holonomy requires additional edge or history data not
contained in the endpoints.

## Canonical endpoint transport

For unit quaternions \(q,r\), define the right-factor transport
\[
\tau(q,r)=r^\ast q.                                         \tag{2}
\]
The corresponding pair is \((1,\tau(q,r))\).

### Theorem 1 — exact endpoint action

\[
\lVert\tau(q,r)\rVert^2=1,
\qquad
(1,\tau(q,r))\cdot q=r.                                     \tag{3}
\]

### Proof

Multiplicativity and conjugation invariance of quaternion norm give
\[
\lVert r^\ast q\rVert^2
=\lVert r\rVert^2\lVert q\rVert^2
=1.
\]
Also
\[
(1,r^\ast q)\cdot q
=q(r^\ast q)^\ast
=q q^\ast r
=r.
\]
\(\square\)

## Flatness theorem

### Theorem 2 — pair-groupoid cocycle

For unit \(q,r,s\),
\[
\begin{aligned}
\tau(q,q)&=1,\\
\tau(r,q)&=\tau(q,r)^\ast,\\
\tau(r,s)\tau(q,r)&=\tau(q,s).                              \tag{4}
\end{aligned}
\]
Consequently every closed endpoint loop has identity transport. In particular,
\[
\tau(s,q)\tau(r,s)\tau(q,r)=1.                              \tag{5}
\]

### Proof

Using \(q^\ast q=r^\ast r=s^\ast s=1\),
\[
\tau(q,q)=q^\ast q=1
\]
and
\[
\tau(q,r)^\ast=(r^\ast q)^\ast=q^\ast r=\tau(r,q).
\]
For composition,
\[
\tau(r,s)\tau(q,r)
=(s^\ast r)(r^\ast q)
=s^\ast(rr^\ast)q
=s^\ast q
=\tau(q,s).
\]
Equation (5) is the specialization \(s\to q\) of the same law. \(\square\)

## Classification of every pair transporter

The flat right-factor choice is not the only pair-group element mapping \(q\) to \(r\). The
remaining freedom is exactly the source stabilizer.

### Theorem 3 — transporter torsor classification

For unit \(u,v,q,r\),
\[
(u,v)\cdot q=r
\quad\Longleftrightarrow\quad
v=r^\ast u q.                                               \tag{6}
\]
Every such transporter has the unique factorization
\[
\boxed{
(u,r^\ast u q)
=
(1,r^\ast q)(u,q^\ast u q).
}                                                           \tag{7}
\]
The first factor is the flat endpoint transport. The second lies in \(\Delta_q\), the exact
stabilizer of the source event direction.

### Proof

If \(u q v^\ast=r\), right multiplication by \(v\) gives
\[
u q=rv.
\]
Left multiplication by \(r^\ast\) gives \(v=r^\ast u q\). Conversely,
\[
\begin{aligned}
u q(r^\ast u q)^\ast
&=u q q^\ast u^\ast r\\
&=u u^\ast r\\
&=r.
\end{aligned}
\]
Finally,
\[
\begin{aligned}
(r^\ast q)(q^\ast u q)
&=r^\ast(qq^\ast)u q\\
&=r^\ast u q,
\end{aligned}
\]
which proves (7). Uniqueness follows because the left component of the stabilizer factor is
already \(u\). \(\square\)

## Stabilizer transport

The flat endpoint pair conjugates the source graph stabilizer to the target graph stabilizer:
\[
(1,\tau(q,r))\Delta_q(1,\tau(q,r))^{-1}=\Delta_r.           \tag{8}
\]
Indeed, on the right component,
\[
(r^\ast q)(q^\ast u q)(q^\ast r)
=r^\ast u r.
\]
Thus all graph stabilizers selected by event directions are canonically isomorphic along this
flat endpoint skeleton.

## Exact no-go

`[FALSIFIED]`

> Event directions \(q\) and their graph stabilizers alone generate gravitational curvature.

They do not. Equations (4)--(5) provide a canonical endpoint comparison whose loop holonomy is
identically trivial. Varying the selected direction without adding path-dependent comparison data
is a pure-gauge Higgs/observer field.

This does not prove that every connection compatible with the graph reduction is flat. It proves
the sharper source-selection boundary:

> Nonzero curvature cannot be reconstructed from the endpoint directions alone. It must live in
> the extra stabilizer/history factor in (7), or in still richer connection and soldering data.

## Strongest positive survivor

`[PAPER-PROVED] [BRIDGE]`

Every unit pair transporter is uniquely:

1. a canonical flat endpoint transmutation; followed by
2. a source-stabilizer-valued history residue.

This is the exact local decomposition needed to distinguish event-created frame **kinematics**
from gravitational **history**. The endpoint factor says which causal direction became actual.
The residual factor records information not recoverable from the two event directions.

The result is ordinary homogeneous-space and principal-bundle mathematics. Its value is as a
no-go and design constraint for the stronger physical conjecture, not as new scientific
knowledge.

## External collision boundary

The result is adjacent to established theory:

- a Higgs field is a section of a quotient bundle and selects a reduction to an exact symmetry
  subgroup;
- a reduced bundle still needs connection data;
- Cartan gravity combines an independent spin connection and soldering form in one Cartan
  connection; and
- Maurer--Cartan transport is flat, while physical curvature belongs to a non-flat connection.

Primary sources include Sardanashvily,
[*Geometry of classical Higgs fields*](https://arxiv.org/abs/hep-th/0510168), Wise,
[*The geometric role of symmetry breaking in gravity*](https://arxiv.org/abs/1112.2390), and
Catren,
[*Geometrical Foundations of Cartan Gauge Gravity*](https://arxiv.org/abs/1407.7814).

## Physical consequence for the parent programme

The slogan

> gravity is clocks disagreeing about which moment comes first

is incomplete. Endpoint disagreement is flatly integrable. A viable law needs an irreducible
comparison history selected by the full objective event, not merely two clock directions.

The failure-driven replacement hunch is:

> **Gravity is reality remembering how quantum possibility became fact.**

Mathematically, the parent theory must derive the stabilizer/history factor in (7) from the full
actuality colligation, prove that it is presentation invariant, and show that its continuum
curvature is Einstein gravity rather than an arbitrary supplied gauge field.

## No-go closure

- **Exact killing mechanism:** canonical endpoint transport obeys the strict cocycle law (4), so
  closed endpoint holonomy is identity.
- **Strongest positive survivor:** the transporter torsor factorization (7) isolates the unique
  history residue beyond endpoint frame selection.
- **New insight:** event directions create frame kinematics; gravity, if present, must be memory
  of the event morphisms joining them.
- **Lean status:** Theorems 1--3, loop flatness, transporter factorization, and stabilizer
  conjugation are unconditional in
  [`QuaternionicGraphEndpointFlatness.lean`](../../../../formal/GaloisForLFunctions/HTGeometry/QuaternionicGraphEndpointFlatness.lean).

## Gates

- [x] internal graph-lock and connection corpus audited
- [x] exact endpoint transport theorem dependency-closed on paper
- [x] flat-loop no-go proved
- [x] strongest positive transporter classification proved
- [x] parent Cartan/Higgs literature collision recorded
- [x] exact statements formalized unconditionally in Lean
- [ ] history residue derived from source-complete actualization
- [ ] Lorentzian soldering and Einstein dynamics derived

## Log

- 2026-07-29 — endpoint-only gravity claim killed by exact pair-groupoid flatness. Extracted the
  unique flat-endpoint times source-stabilizer transporter factorization as positive survivor.
- 2026-07-29 — formalized the endpoint unit/action laws, identity/reverse/composition cocycle,
  triangle flatness, complete transporter classification, flat-times-stabilizer factorization, and
  graph-stabilizer conjugation in Lean. Focused build and axiom audit passed.
