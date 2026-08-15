# Every global possibility-wall map is exactly flat

- **ID:** `global-actuality-wall-cocycle-flatness`
- **Stage:** 3-formalized
- **Formalized companion:** `global-actuality-wall-cocycle-flatness-formalized.md`
- **Type:** THEOREM (paper) / EXACT NO-GO / POSITIVE CLASSIFICATION
- **Status:** `[PAPER-PROVED] [LEAN-PROVEN] [REDISCOVERED] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Parent:** `../../1-in-progress/actuality-distinction-spacetime-law.md`
- **Statement:** Relative orientations of any one globally defined family of binary event walls
  form an exact Boolean coboundary. Their holonomy around every loop is identically zero, and they
  recover physical states exactly up to wall-indistinguishability.

## Setup

Let \(X\) be any set of possible physical states or complete continuations, let \(W\) be any set of
event-wall labels, and assign to each wall \(w\in W\) one of its two sides

\[
H_w\subseteq X.
\]

No topology, probability, order, metric, finiteness, or dynamics is assumed.

For a base actuality \(b\in X\) and a state \(x\in X\), define the relative wall profile

\[
P_b(x)
  :=\{w\in W:\mathbf 1_{H_w}(x)\ne \mathbf 1_{H_w}(b)\}.
\tag{1}
\]

Thus \(P_b(x)\) is the set of event boundaries separating \(b\) from \(x\). For subsets
\(A,B\subseteq W\), write

\[
A\mathbin{\triangle}B
  :=\{w\in W:\mathbf 1_A(w)\ne\mathbf 1_B(w)\}
\tag{2}
\]

for symmetric difference.

Define wall-indistinguishability by

\[
x\sim_W y
\quad\Longleftrightarrow\quad
\forall w\in W,\ 
\bigl(x\in H_w\Longleftrightarrow y\in H_w\bigr).
\tag{3}
\]

The walls **separate points** when \(x\sim_W y\) implies \(x=y\).

## Theorem

For every \(a,b,c,x,y\in X\):

1. \(P_b(b)=\varnothing\).
2. \(P_b(x)=P_b(y)\) if and only if \(x\sim_W y\).
3. The map \(P_b:X\to\mathcal P(W)\) is injective if and only if the walls separate points.
4. \(P_b(x)=P_x(b)\).
5. Relative profiles obey the exact difference law
   \[
   P_b(x)\triangle P_b(y)=P_x(y).
   \tag{4}
   \]
6. Changing the actual basepoint is a Boolean translation:
   \[
   P_c(x)=P_b(x)\triangle P_b(c).
   \tag{5}
   \]
7. The profiles form an exact cocycle:
   \[
   P_a(b)\triangle P_b(c)=P_a(c).
   \tag{6}
   \]
8. Every triangular loop has zero holonomy:
   \[
   P_a(b)\triangle P_b(c)\triangle P_c(a)=\varnothing.
   \tag{7}
   \]

Consequently \(X/{\sim_W}\) embeds canonically, after choosing a basepoint, into the Boolean group
\((\mathcal P(W),\triangle)\). Different basepoints change that embedding only by translation.

## Proof

Fix \(w\in W\), and abbreviate

\[
\epsilon_z=\mathbf 1_{H_w}(z)\in\{0,1\}.
\]

Membership of \(w\) in \(P_b(x)\) is the Boolean value

\[
\epsilon_x\oplus\epsilon_b,
\tag{8}
\]

where \(\oplus\) is addition modulo two.

1. For \(x=b\), equation (8) is
   \(\epsilon_b\oplus\epsilon_b=0\), proving \(P_b(b)=\varnothing\).

2. For fixed \(b\),
   \[
   \epsilon_x\oplus\epsilon_b
   =
   \epsilon_y\oplus\epsilon_b
   \quad\Longleftrightarrow\quad
   \epsilon_x=\epsilon_y.
   \]
   This holds for every wall exactly when \(x\sim_W y\), proving clause 2.

3. Clause 2 says that every fiber of \(P_b\) is precisely one
   \(\sim_W\)-equivalence class. Therefore \(P_b\) is injective exactly when every such class is a
   singleton, which is exactly point separation.

4. Commutativity of \(\oplus\) gives
   \(\epsilon_x\oplus\epsilon_b=\epsilon_b\oplus\epsilon_x\), proving profile symmetry.

5. At \(w\), the left side of (4) is
   \[
   (\epsilon_x\oplus\epsilon_b)
   \oplus
   (\epsilon_y\oplus\epsilon_b)
   =
   \epsilon_x\oplus\epsilon_y,
   \]
   since the two copies of \(\epsilon_b\) cancel. This is membership in \(P_x(y)\).

6. Apply clause 5 with the common basepoint \(b\) to \(x\) and \(c\):
   \[
   P_b(x)\triangle P_b(c)=P_x(c)=P_c(x),
   \]
   using clause 4 in the final equality.

7. At \(w\), the left side of (6) is
   \[
   (\epsilon_b\oplus\epsilon_a)
   \oplus
   (\epsilon_c\oplus\epsilon_b)
   =
   \epsilon_c\oplus\epsilon_a,
   \]
   which is membership in \(P_a(c)\).

8. By clause 7, the left side of (7) is
   \[
   P_a(c)\triangle P_c(a).
   \]
   Clause 4 makes the two sets equal, and the symmetric difference of a set with itself is empty.

All equalities hold wall by wall, so extensionality completes the proof. No excluded physical
case, finiteness assumption, or choice of path is used.

## Hostile novelty audit

**Verdict:** `[REDISCOVERED] [BRIDGE]`.

Equations (4)--(7) are the elementary coboundary identities of a Boolean group. Wallspaces, median
graphs, CAT(0) cube complexes, and event-structure domains already use separating hyperplanes and
halfspace orientations. In particular:

- CAT(0) cubical hyperplanes separate the complex into two convex halfspaces, and its vertices form
  a discrete median algebra: <https://arxiv.org/abs/0909.0968>;
- domains of prime event structures correspond to pointed median graphs and pointed CAT(0) cube
  complexes, with events represented by hyperplanes:
  <https://arxiv.org/abs/1605.08288>.

This theorem is not new mathematics and supplies no evidence that physical reality is a wallspace.
Its value is exact obstruction and classification.

## No-go closure

- **Exact killing theorem/mechanism:** In one globally defined binary event-wall system, relative
  actuality profiles are differences of global coordinates. Every comparison cocycle is exact and
  every loop holonomy is zero by (7). Merely changing which side of fixed global walls is actual
  cannot produce curvature.
- **Strongest positive survivor:** A source-complete separating wall family recovers states exactly
  up to a Boolean translation of basepoint. Event boundaries can therefore encode complete
  relative configuration data while carrying no preferred actuality or time orientation.
- **New insight:** The parent conjecture cannot identify gravity with wall crossing, Hamming
  distance, basepoint choice, or orientation change inside one global possibility map. If its
  event--boundary identity is true, gravity must be the obstruction to the existence of that
  global map: path-dependent descent among local distinction systems, or a genuinely non-Boolean
  replacement. Local event--boundary duality may remain exact while global comparison is curved.
- **Status:** Complete paper proof above. Exact Boolean-coordinate form is formalized
  unconditionally in `ActualityWallFlatness.lean`; the formalization also proves zero holonomy on
  every finite closed graph walk, not only triangular loops. It now also defines the literal
  quotient by wall-indistinguishability and proves its basepoint-dependent profile embedding is
  injective and changes only by the stated Boolean translation.

## Physical boundary

The theorem does **not** prove:

- that physical events define binary walls;
- that source-complete counterfactual data separate physical states;
- that local wall charts exist;
- that failure of global wall coordinates is gravity;
- Lorentzian geometry, Einstein dynamics, quantum amplitudes, or any gauge force;
- \(S(U(2)\times U(3))\), matter representations, or Hypertranscendence.

It proves only that the simplest global realization of the frozen actuality-distinction law is
necessarily flat in its own comparison coordinates.

## Lean formalization

`formal/GaloisForLFunctions/HTGeometry/ActualityWallFlatness.lean` formalizes all eight displayed
profile clauses. In addition to the pointwise identities, it defines
`wallIndistinguishableSetoid` and proves:

1. `actualityWallProfileQuotient_injective`: after choosing a basepoint, the exact quotient
   \(X/{\sim_W}\) embeds in \(W\to\mathrm{Bool}\);
2. `actualityWallProfileQuotient_changeBase`: changing that basepoint translates the embedding by
   the fixed profile \(P_b(c)\).

Thus the final consequence of the paper theorem is a literal Lean declaration, rather than an
inference left to the reader.

## Gates

- [x] exact claim stated without physical overloading
- [x] dependency-closed paper proof
- [x] primary parent-theory collision audit
- [x] classified as rediscovered Boolean/wallspace mathematics
- [x] strongest positive survivor and representation lesson recorded
- [x] exact theorem formalized unconditionally in Lean
- [x] formal lint passed
- [x] axiom audit passed with only standard Lean foundations

## Log

- 2026-07-29 — extracted from the first hostile attack on
  `actuality-distinction-spacetime-law.md`. Global event walls solve relative orientation only by
  making its cocycle exact; nonzero gravitational comparison must therefore be a descent
  obstruction rather than a global wall-coordinate difference.
- 2026-07-29 — formalized the exact profile identities, separation classification, and arbitrary
  closed-walk flatness in `HTGeometry/ActualityWallFlatness.lean`.
- 2026-08-15 — formalized the exact wall-indistinguishability quotient embedding and its
  basepoint-translation law; direct source check, focused build, and axiom audit passed.
