# Spacetime is what remains when nature forgets colour

- **ID:** `color-blind-event-gram-spacetime-law`
- **Stage:** 1-in-progress
- **Type:** UNIVERSAL PHYSICAL CONJECTURE / SPACETIME / GRAVITY / FOUR FORCES
- **Freeze date:** 2026-07-29
- **Status:** `[CONJECTURE FROZEN] [PROOF ROUTE UNKNOWN] [NOVELTY UNVERIFIED]`
- **Statement:** Physical spacetime is the colour-orbit space of the mixed exceptional actuality
  tensor selected by a quantum event.

## Public law

> **Spacetime is what remains when nature forgets colour.**

Operational version:

> **One quantum alternative makes a light ray. A complete quantum event makes a future. Gravity
> is the failure of those futures to fit together.**

## Frozen physical conjecture

`[CONJECTURE; DO NOT RESHAPE FOR PROVABILITY]`

> **COLOUR-BLIND EVENT GRAM LAW.** Every elementary physical event couples the three complex
> agreement directions of a compatible exceptional pure-state pair to its two complex
> actuality-normal directions, producing a mixed event tensor
> \[
> X\in A\otimes B\cong M_{3,2}(\mathbb C).
> \]
> Colour is the unobservable left frame of this tensor. The complete colour-blind event is its
> Gram element
> \[
> G_X=X^\dagger X\in H_2(\mathbb C).
> \]
> The positive Gram cone is the local causal future: rank-one events are null, full-rank events
> are timelike, and \(\det G_X\) is their Lorentz interval. Composable events solder these cones
> into spacetime. The curvature of one exceptional event connection descends as gravitational
> curvature on the Gram quotient and as the strong, weak, and hypercharge curvatures on its
> vertical and residual frame sectors. No spacetime, Lorentz metric, force group, or separate
> Einstein--Yang--Mills action is supplied independently.

This statement is an evidence-informed truth-hunch. Its provability and every candidate
construction begin only after the freeze.

## Why this is a genuine jump

The conjecture does not say merely that a Hermitian \(2\times2\) matrix represents a Minkowski
vector. It says that the physically real causal carrier is forced by forgetting the colour frame
of the exact exceptional Standard Model event triple.

The proposed ontology is:

```text
exceptional compatible quantum pair
  selects A ≅ C³ and B ≅ C²

actual event
  couples them into X ∈ A ⊗ B ≅ M₃,₂(C)

forget unobservable colour frame
  leaves G = X†X ∈ H₂(C)₊

rank one
  is light

rank two
  is a timelike future

failure of neighbouring Gram futures to glue
  is gravity
```

If true, four-dimensional Lorentzian causal geometry is neither inserted as a manifold nor
obtained by reinterpreting four gauge directions. It is the complete invariant left after the
three colour directions of one exceptional quantum event are contracted.

## Evidence at freeze

### `[LITERATURE]` Exceptional source

Baez--Bokor--Boyle,
[*Jordan Pair Quantum Theory and the Standard Model*](https://arxiv.org/abs/2607.10833), prove
that two collinear minimal tripotents in the bi-Cayley triple select the common Peirce-half triple
\[
W''\cong M_{3,2}(\mathbb C)
\]
whose real inner automorphism group is exactly
\[
G_{\rm SM}=S(U(3)\times U(2))
\cong (SU(3)\times SU(2)\times U(1))/\mathbb Z_6.
\]
They identify the corresponding \((\mathbf3,\mathbf2)_{1/6}\) component with the left quark
doublet. They do not propose a Gram spacetime, Lorentzian metric, gravity law, or continuum
construction.

### `[LOCAL-RESEARCH]` First-order obstruction and mixed survivor

`../2-fully-proven/pure-pair-normal-actuality-fracture.md` proves that at the compatible
Spin(10) pair:

- pure tangential motion reports only \(A\cong\mathbb C^3\);
- the colour-preserving actuality-normal channel is \(B\cong\mathbb C^2\);
- pure tangential motion has zero \(B\)-reporter.

Thus neither \(A\) nor \(B\) alone supplies a nondegenerate event spacetime. Their mixed carrier
\(A\otimes B\cong M_{3,2}(\mathbb C)\) is independently selected by the exceptional Jordan-triple
literature. The conjectural step is that actual event composition physically creates this mixed
tensor.

### `[BRIDGE]` Exact Gram-cone kinematics

For \(X=(u\ v)\in M_{3,2}(\mathbb C)\),
\[
G_X=
\begin{pmatrix}
\lVert u\rVert^2 & \langle u,v\rangle\\
\langle v,u\rangle & \lVert v\rVert^2
\end{pmatrix}
\]
is positive semidefinite and
\[
\det G_X
=\lVert u\rVert^2\lVert v\rVert^2-|\langle u,v\rangle|^2.
\]
Therefore:

- \(\det G_X>0\) exactly when \(X\) has complex rank two;
- \(\det G_X=0\) exactly on the rank-at-most-one boundary;
- \(G_{UX}=G_X\) for \(U\in U(3)\);
- every positive semidefinite Hermitian \(2\times2\) matrix is \(X^\dagger X\);
- equal Gram matrices are exactly equal \(U(3)\)-orbits.

Under the Pauli-coordinate identification
\[
\begin{pmatrix}
t+z & x-iy\\
x+iy & t-z
\end{pmatrix}
\longleftrightarrow (t,x,y,z),
\]
the determinant is
\[
t^2-x^2-y^2-z^2,
\]
and the positive-semidefinite cone is the closed Minkowski future cone. Hence
\[
M_{3,2}(\mathbb C)/U(3)\cong H_2(\mathbb C)_{\ge0}
\]
as an orbit space. This mathematics is classical polar-decomposition, Gram, and spinor
geometry; it is not the conjecture's claimed scientific novelty.

The exact algebraic core is now unconditionally Lean-proven in
`../../../../../../formal/GaloisForLFunctions/HTGeometry/ColorGramMinkowskiCone.lean` and recorded in
`../../../3-formalized/color-gram-minkowski-cauchy-binet-law.md`. In particular, Lean proves the
Lorentz quadratic form is the sum of the three squared maximal minors, the Gram rank equals the
event rank, left \(U(3)\) is invisible, and the right \(2\times2\) frame acts covariantly. The
orbit classification, positive-cone surjectivity, and quotient homeomorphism are now also
unconditionally Lean-proven in
`../../../../../../formal/GaloisForLFunctions/HTGeometry/ColorGramMinkowskiOrbit.lean`.

## Hostile attack

### 1. The mathematical quotient is known

`[REDISCOVERED]`

Gram-orbit classification, positive Hermitian cones, and the identification of
\(H_2(\mathbb C)_{\ge0}\) with the Minkowski future cone are standard. Only the exceptional
physical selection and dynamical claim could be new.

### 2. The weak-isospin lock is not solved

`[FINITE LOCK LEAN-PROVEN] [SEPARATION OPEN]`

The right \(U(2)\) action sends
\[
G_X\longmapsto V G_XV^\dagger.
\]
Its \(SU(2)\) subgroup therefore acts like compact spatial-frame rotation on the Gram cone.
Baez--Bokor--Boyle identify the same abstract factor as weak isospin. Declaring these actions
identical would lock weak and gravitational transport, contradicting their observed physical
roles and the local obstruction already recorded in
`formal/GaloisForLFunctions/HTGeometry/WeakLorentzOverlap.lean`.

The strengthened colour-Gram witness is now unconditional in
`../../../../../../formal/GaloisForLFunctions/HTGeometry/ColorGramWeakLorentzLock.lean` and recorded in
`../../../3-formalized/color-gram-weak-lorentz-lock-no-go.md`. The special-unitary half-turn
\(\operatorname{diag}(i,-i)\) moves the genuine positive future-null Gram ray
\((1,1,0,0)\) to the distinct future-null ray \((1,-1,0,0)\). Thus the weak action rotates the
actual event future, not merely an indefinite extension of the Hermitian corner.

The conjecture survives only if the exceptional event law uses the two nonconjugate Standard
Model reductions already found in the corpus to separate:

- the matter-side weak connection that remains an internal force; and
- the observer-side compact Lorentz-frame action on the Gram cone.

No such separation theorem exists.

### 3. A cone is not a spacetime

`[OPEN CORE]`

The orbit theorem creates a local causal carrier, not:

- event incidence or locality;
- a tangent bundle;
- a nondegenerate tetrad;
- differentiability;
- a Lorentz connection;
- Einstein dynamics;
- universal free fall;
- quantum probabilities;
- a finite prediction.

### 4. The dynamics are not selected

`[OPEN CORE]`

No known exceptional invariant has yet been shown to produce one low-energy
Einstein--Dirac--Yang--Mills--Higgs action. Assigning separate familiar actions to the quotient
and vertical sectors would be a collage, not unification.

## First exact open core

`[OPEN CORE: EXCEPTIONAL GRAM DESCENT]`

Construct or kill an exceptional event category satisfying all of the following:

1. its objects or elementary arrows canonically produce the mixed
   \(X\in A\otimes B\cong M_{3,2}(\mathbb C)\), rather than assume it as a field on spacetime;
2. its physical equivalence relation is exactly the left colour-frame orbit;
3. the resulting Gram cones compose into a locally finite causal order and reconstruct the same
   four-dimensional tangent carrier;
4. the two nonconjugate \(SU(2)\) reductions separate weak isospin from Lorentz-frame rotation;
5. one exceptional connection and one invariant action descend to Einstein gravity and exactly
   the Standard Model force dynamics;
6. the descent gives a finite parameter-reducing observable.

## Kill conditions

Retire the conjecture if any survives a serious repair:

1. the physically correct exceptional event equivalence quotients the right weak frame as well,
   leaving only the two eigenvalues of \(G_X\) rather than a four-carrier;
2. the weak \(SU(2)\) and Lorentz-frame \(SU(2)\) cannot be separated without inserting a second
   unrelated gauge group or tetrad;
3. no source-selected event law produces a full-rank mixed tensor;
4. event composition cannot reconstruct causal locality or a nondegenerate soldering;
5. every descended action is merely GR plus the Standard Model written in Gram variables;
6. the construction predicts extra long-range forces, wrong chirality, gauge anomalies, Lorentz
   violation, equivalence-principle violation, or no finite discriminator.

Failure to see a proof route is not a kill condition.

## Gates

- [x] 0 → 1: proof-route-blind conjecture, evidence, incompatible world, and kill conditions frozen
- [ ] 1 → 2: exceptional Gram descent, continuum, dynamics, and finite prediction
  dependency-closed on paper
- [ ] 2 → 3: every mathematical claim formalized unconditionally in Lean
- [ ] 3 → 4: independent priority, physics, experiment, and hostile Nature review passed

Current Nature verdict: `[DO NOT WRITE MANUSCRIPT]`.

## Log

- 2026-07-29 — frozen after the first-order pure-path no-go. The obstruction leaves complementary
  \(A\cong\mathbb C^3\) tangent and \(B\cong\mathbb C^2\) normal channels; their mixed tensor is
  exactly the exceptional \(M_{3,2}(\mathbb C)\) triple selected independently by two compatible
  pure states. The colour Gram map exposes a four-dimensional Lorentz future cone, while hostile
  attack isolates weak/Lorentz separation and causal composition as the first unproved physics.
- 2026-07-29 — formalized the complete Gram/Lorentz/Cauchy--Binet algebraic core and strengthened
  the weak/Lorentz lock to a positive future-null event. The right weak half-turn provably rotates
  the actual Gram light cone. The primary conjecture now requires a source-selected doubled action
  or noninvertible weak-kernel/Lorentz-cokernel interface.

## Post-freeze dimension-selection attack

`[CORRECTION] [STRONGER SURVIVOR]`

The Gram quotient does not derive four dimensions from color dimension three. For every
\(n\ge2\), the same standard orbit argument gives
\[
M_{n,2}(\mathbb C)/U(n)\cong H_2(\mathbb C)_{\ge0}.
\]
Thus the four real public coordinates come from the surviving two-dimensional complex alternative
space. Hidden carrier dimension does not determine them.

The stronger surviving headline is:

> **The universe has four dimensions because an elementary objective fact has two complex quantum
> alternatives.**

The exceptional source remains necessary because it selects the simultaneous
\(\mathbb C^3\otimes\mathbb C^2\) carrier and exact Standard Model group. A Nature-level theorem
must derive binary complex public alternatives, hidden color three, and their common dynamics
from one source law. Assuming the \(3\times2\) event tensor is not enough.

The complete `3 × 2` orbit classification, positive-cone surjectivity, and quotient topology are
now unconditionally formalized in
`../../../../../../formal/GaloisForLFunctions/HTGeometry/ColorGramMinkowskiOrbit.lean`.
The broader physical interpretation has been sharpened in
`event-generated-identity-curvature-law.md`.
