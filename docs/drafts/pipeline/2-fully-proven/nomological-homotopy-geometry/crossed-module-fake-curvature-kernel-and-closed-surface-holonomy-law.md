# Crossed-module fake curvature, homotopy kernel, and closed-surface holonomy law

- **ID:** `nhg-crossed-module-surface-holonomy`
- **Stage:** 2 — fully proven on paper
- **Status:** `[PAPER-PROVED] [UNIVERSAL FIELD THEOREM] [STRICT 2-GROUP SECTOR]`
  `[NO ROUTE INPUT] [NOT RH] [NO LEAN WRITTEN OR BUILT]`

## 1. Crossed modules

Let

\[
 t:H\longrightarrow G
\tag{CM.1}
\]

be a Lie-group crossed module with action `G act H`, satisfying

\[
 t(g\triangleright h)=gt(h)g^{-1},
\qquad
 t(h)\triangleright h'=hh'h^{-1}.
\tag{CM.2}
\]

Its homotopy groups are

\[
 \pi_1=G/\operatorname{im}t,
 \qquad
 \pi_2=\ker t.
\tag{CM.3}
\]

### Lemma 1.1 — the higher kernel is central

\[
 \boxed{\ker t\subseteq Z(H).}
\tag{CM.4}
\]

Hence `pi_2` is abelian, and the `G`-action descends to an action of `pi_1` on `pi_2`.

#### Proof

For `k in ker t`, the second Peiffer identity gives

\[
 khk^{-1}=t(k)\triangleright h=e\triangleright h=h
\]

for every `h in H`. Thus `k` is central. Elements of `im t` act trivially on `ker t` by the same
identity, so the action factors through `G/im t`. QED.

## 2. Strict 2-connection

Let `(t:mathfrak h->mathfrak g,triangleright)` be the differential crossed module. On a manifold
`M`, a local strict 2-connection is

\[
 A\in\Omega^1(M;\mathfrak g),
 \qquad
 B\in\Omega^2(M;\mathfrak h).
\tag{CM.5}
\]

Define

\[
 F_A=dA+{1\over2}[A,A],
\tag{CM.6}
\]

the fake curvature

\[
 \mathcal F=F_A-t(B),
\tag{CM.7}
\]

and the 3-curvature

\[
 H_3=d_AB=dB+A\triangleright B.
\tag{CM.8}
\]

## 3. Higher Bianchi law

### Theorem 3.1 — fake-curvature transgression

\[
 \boxed{d_A\mathcal F=-t(H_3).}
\tag{CM.9}
\]

Consequently, fake flatness implies

\[
 \boxed{\mathcal F=0\Longrightarrow
 H_3\in\Omega^3(M;\ker t).}
\tag{CM.10}
\]

If `t` is injective, every fake-flat strict 2-connection has `H_3=0`.

#### Proof

Ordinary Bianchi gives `d_AF_A=0`. Equivariance of `t` gives

\[
 d_A t(B)=t(d_AB)=t(H_3).
\]

Apply `d_A` to `(CM.7)` to get `(CM.9)`. Equation `(CM.10)` and the injective case follow. QED.

This is a hard algebraic restriction: nonzero fake-flat higher curvature requires a nontrivial
homotopy kernel.

## 4. Closed-surface holonomy

Assume the fake-flat 2-connection integrates to a smooth strict transport 2-functor. A based closed
surface is a 2-morphism from the identity path at the base point to itself. In the crossed-module
2-group, a 2-morphism labelled by `h in H` has target one-arrow multiplied by `t(h)`.

### Theorem 4.1 — closed surface holonomy lands in the abelian kernel

For every based closed surface `Sigma`,

\[
 \boxed{\operatorname{Hol}_2(\Sigma)\in\ker t=\pi_2.}
\tag{CM.11}
\]

Any two such closed-surface holonomies commute. Changing base path acts through the induced
`pi_1`-action on `pi_2`.

#### Proof

The source and target one-arrows of a closed-surface 2-morphism are both the identity. Therefore its
label `h` must satisfy `t(h)=e`, proving `(CM.11)`. Lemma 1.1 gives commutativity. Equivariance of
2-transport under whiskering by a path gives the `G`-action, which factors through `pi_1` by Lemma
1.1. QED.

## 5. Consequences for graded holonomy

1. Closed two-dimensional holonomy is abelian even when the ambient strict 2-group is nonabelian.
2. Nonabelianity survives in path transport, the `pi_1` action on `pi_2`, open-surface composition,
   and Postnikov extension data.
3. Local fake-flat 3-curvature and global closed-surface holonomy live in the same coefficient
   system `ker t`, making an Ambrose--Singer comparison well-typed there.
4. If `ker t=0`, no nonzero fake-flat 3-curvature or closed-surface charge exists; any proposed
   higher effect must come from ordinary holonomy or non-fake-flat transport.
5. The abelian differential-character theorem is not an accident: fixed higher homotopy groups are
   abelian, while the full higher groupoid retains nonabelian coupling across degrees.

## 6. Hostile boundary

- Fake flatness is load-bearing for thin-homotopy-invariant strict surface transport.
- The theorem does not say all surface transport is abelian; open surfaces and base-path changes are
  nonabelian.
- `H_3` does not by itself determine global surface holonomy; flat `pi_2` characters remain.
- No higher Ambrose--Singer generation theorem is proved here.
- Semistrict and fully weak higher groups require coherent replacements of the crossed-module
  formulas.

