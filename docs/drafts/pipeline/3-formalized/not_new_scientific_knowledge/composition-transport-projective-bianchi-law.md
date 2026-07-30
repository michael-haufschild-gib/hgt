# Composition transport and path holonomy obey one projective Bianchi law

- **ID:** `composition-transport-projective-bianchi-law`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / COMPOSITION-CURVATURE BRIDGE / NOT NEW MATHEMATICS
- **Scientific status:** `[PROVED HERE] [LEAN-FORMALIZED] [PARENT ALGEBRA]`
  `[NOT NEW SCIENTIFIC KNOWLEDGE] [NO PHYSICS PROVED]`
- **Parent conjecture:** `../../1-in-progress/composition-curvature-universal-law.md`
- **Earlier linear parent:** `event-descent-transgression-bianchi.md`
- **Lean:** `formal/GaloisForLFunctions/HTGeometry/CompositionTransportBianchi.lean`
- **Statement:** On every triangle of linear comparisons, failure to transport a bilinear
  composition law and failure of the comparison path to close satisfy one exact nonlinear
  identity. Its projective form forces central-weight balance at every nonzero composition.

## Setup

Let \(V\) be a module and let

\[
\mu_i:V\times V\longrightarrow V,\qquad i=0,1,2,
\]

be bilinear composition laws at three event labels. Let

\[
T_{01},T_{12},T_{02}:V\longrightarrow V
\]

be linear comparisons.

Define the composition-transport defect

\[
Q_{ij}(x,y)
=T_{ij}\mu_i(x,y)-\mu_j(T_{ij}x,T_{ij}y)
\tag{CB.1}
\]

and comparison-path defect

\[
K=T_{12}T_{01}-T_{02}.
\tag{CB.2}
\]

## Exact coupled triangle law

### Theorem 1

`[PROVED HERE]`

\[
\begin{aligned}
&T_{12}Q_{01}(x,y)
+Q_{12}(T_{01}x,T_{01}y)
-Q_{02}(x,y)\\
&\quad=
K\mu_0(x,y)
-\mu_2(Kx,T_{02}y)
-\mu_2(T_{02}x,Ky)
-\mu_2(Kx,Ky).
\end{aligned}
\tag{CB.3}
\]

### Proof

Substitute `(CB.1)` into the left side. The two terms containing
\(T_{12}\mu_1(T_{01}x,T_{01}y)\) cancel, leaving

\[
(T_{12}T_{01}-T_{02})\mu_0(x,y)
-\mu_2(T_{12}T_{01}x,T_{12}T_{01}y)
+\mu_2(T_{02}x,T_{02}y).
\]

Use \(T_{12}T_{01}=T_{02}+K\), expand the middle term by bilinearity, and cancel the
\(\mu_2(T_{02}x,T_{02}y)\) term. The result is `(CB.3)`. \(\square\)

The quadratic term \(-\mu_2(Kx,Ky)\) is part of exact finite transport. It is lost by a
first-order linearization.

### Corollary 1: flat comparison

If \(K=0\), then

\[
T_{12}Q_{01}
+Q_{12}\circ(T_{01},T_{01})
=Q_{02}.
\tag{CB.4}
\]

Thus composition-transport defects obey a cocycle law only on a flat comparison triangle.

## Projective coupled triangle law

Let \(a\) be a scalar and define

\[
K_a=T_{12}T_{01}-aT_{02}.
\tag{CB.5}
\]

### Theorem 2

`[PROVED HERE]`

\[
\begin{aligned}
&T_{12}Q_{01}(x,y)
+Q_{12}(T_{01}x,T_{01}y)
-aQ_{02}(x,y)\\
&\quad=
K_a\mu_0(x,y)
+(a-a^2)\mu_2(T_{02}x,T_{02}y)\\
&\qquad
-a\mu_2(K_ax,T_{02}y)
-a\mu_2(T_{02}x,K_ay)
-\mu_2(K_ax,K_ay).
\end{aligned}
\tag{CB.6}
\]

The new term

\[
(a-a^2)\mu_2(T_{02}x,T_{02}y)
\tag{CB.7}
\]

is unavoidable. A phase acts once on the output comparison but twice through the two inputs of a
bilinear composition.

## Phase rigidity

### Theorem 3

`[PROVED HERE]`

Work over a field. Suppose:

1. \(T_{12}T_{01}=aT_{02}\);
2. all three composition defects in `(CB.6)` vanish at \(x,y\); and
3. \(\mu_2(T_{02}x,T_{02}y)\ne0\).

Then

\[
a=0\quad\text{or}\quad a=1.
\tag{CB.8}
\]

In particular, a nonzero scalar path phase must be trivial.

### Proof

Under the three assumptions, every term in `(CB.6)` vanishes except `(CB.7)`. Hence

\[
(a-a^2)\mu_2(T_{02}x,T_{02}y)=0.
\]

Faithfulness of scalar multiplication over a field and nonvanishing of the composed vector give
\(a-a^2=0\), so \(a(1-a)=0\). \(\square\)

This is a no-go for **neutral** binary composition on the same projective carrier. It does not
forbid projective phase. It says the composition tensor must carry compensating central weight.

## Central-weight balance

### Theorem 4

`[PROVED HERE]`

Let \(\mu(x,y)\ne0\). If the two inputs transform with scalar weights \(a,b\), the output with
weight \(c\), and composition is covariant:

\[
c\,\mu(x,y)=\mu(ax,by),
\tag{CB.9}
\]

then

\[
\boxed{c=ab.}
\tag{CB.10}
\]

### Proof

Bilinearity gives \(\mu(ax,by)=ab\,\mu(x,y)\). Since \(\mu(x,y)\ne0\), faithful scalar
multiplication gives `(CB.10)`. \(\square\)

For unit phases written additively, `(CB.10)` is

\[
q_{\rm out}=q_{\rm in,1}+q_{\rm in,2}
\tag{CB.11}
\]

modulo the phase period. Thus additive charge conservation is the character-balance condition
for a nonzero composition vertex.

## What this adds to the research direction

The corpus had three separate ideas:

1. source order produces projective phase;
2. event succession may transport the rule of composition; and
3. physical interactions conserve charge.

Theorems 1--4 place them on one exact finite algebraic surface:

```text
projective comparison holonomy
  + nonzero composition
  -> central arity mismatch
  -> composition needs central weight
  -> input and output weights balance.
```

This does not derive electromagnetism, hypercharge, a gauge group, a particle spectrum, or any
physical charge. It supplies a falsifiable design constraint: a source-completion theory cannot
add projective quantum phase and neutral interaction composition independently.

The higher open target is an \(n\)-ary and higher-categorical version in which:

- central characters multiply with input arity;
- all allowed composition vertices determine a charge lattice;
- comparison-path curvature and composition curvature obey one coherence identity; and
- the resulting lattice and global quotient are forced to be those of the Standard Model rather
  than inserted.

## Novelty boundary

The identities are expansions of bilinearity, functorial transport, and central-character
covariance. Charge balance at an intertwining vertex is standard representation theory. No new
mathematics or physics is claimed.

The corpus already formalized the linear seam--triangle identity in
`event-descent-transgression-bianchi.md`. The present theorem is its bilinear-composition
specialization and extension: it exposes the finite quadratic path-defect term and the projective
central arity term. Those terms are new to this local theorem surface, not new mathematics.

Potential new mathematics would begin with an endogenous positive anchored completion whose
allowed operations and comparison 2-morphisms are reconstructed from raw source consequences,
and whose full higher Bianchi identity forces a unique charge lattice.

## Lean status

Lean proves:

- `compositionTransportDefect_triangle_bianchi`;
- `compositionTransportDefect_flat_triangle`;
- `compositionTransportDefect_projective_triangle_bianchi`;
- `projectiveComposition_phase_idempotent`; and
- `nonzeroComposition_centralWeight_balance`.

No `sorry`, `admit`, new `axiom`, `opaque`, `unsafe`, or computation is used. `#print axioms`
reports only `propext`, `Classical.choice`, and `Quot.sound`.

## Log

- 2026-07-30 — Derived and Lean-formalized exact finite and projective triangle identities.
- 2026-07-30 — Extracted phase-idempotence no-go and central-weight-balance positive survivor.
