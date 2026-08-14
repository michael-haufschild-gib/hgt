# Asymptotic law-core formation, affine exchange, recovery, and exactification law

- **ID:** ULF-ALCM-1
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Status:** `[PROVED HERE] [DEPENDENCY-CLOSED] [ROUTE-INDEPENDENT]`
  `[LEAN FORMALIZED] [NOT A SELECTOR] [NOT RH]`
- **Lean:** `GaloisForLFunctions.HTGeometry.ConstitutiveAsymptoticLawCore`
- **Parent programme:**
  `../../../1-in-progress/universal-law-field/asymptotic-law-core-mechanics/field-programme.md`
- **Statement:** Compact-convex tail formation commutes exactly with every continuous affine
  reporter. A common affine recovery reconstructs the complete formed core, an involutive
  functional-equation action lifts information-neutrally through that recovery, and every
  asymptotically vanishing affine law becomes exact on the core.

## 1. Mechanism

Let `E` be a Hausdorff real topological vector space and let `x : N -> E` be a formation history
contained in a compact convex set `K`. Define

\[
 \operatorname{Core}(x)
 =\bigcap_{N\ge 0}\overline{\operatorname{co}}
   \{x_n:n\ge N\}.
 \tag{ALC.1}
\]

This is not a selected limit, invariant mean, ultrafilter, or route endpoint. It is the complete
family of laws that remain formable after deletion of every finite prefix.

The theorem concerns one mechanism:

> form all asymptotically persistent convex laws first; then compare, recover, or impose a law.

## 2. Formation theorem

### Theorem 2.1 -- compact-convex existence

Under the hypotheses above, `Core(x)` is nonempty, compact, closed, convex, and contained in `K`.

### Proof

Put

\[
 C_N=\overline{\operatorname{co}}\{x_n:n\ge N\}.
\]

Each `C_N` is nonempty, closed, convex, and contained in `K`; moreover
`C_{N+1} subset C_N`. Since `C_0` is compact, the nested compact-intersection theorem gives
`intersection_N C_N != empty`. Closedness and convexity are preserved by intersections, and the
intersection is a closed subset of compact `K`. QED.

## 3. Exact affine exchange

Let `F` be another Hausdorff real topological vector space and let `f : E -> F` be continuous
affine.

### Theorem 3.1 -- tail-hull exchange

For every `N`,

\[
 f(C_N)=
 \overline{\operatorname{co}}\{f(x_n):n\ge N\}.
 \tag{ALC.2}
\]

### Proof

The right side contains the image of the raw tail. Its inverse image under `f` is closed and
convex, so minimality of the closed convex hull gives the forward inclusion. Conversely `f(C_N)`
is convex. It is compact, hence closed, because `C_N` is a closed subset of compact `K`; it contains
the image tail. Minimality gives the reverse inclusion. QED.

### Theorem 3.2 -- formation exchange

\[
 \boxed{f(\operatorname{Core}(x))=\operatorname{Core}(f\circ x).}
 \tag{ALC.3}
\]

### Proof

The forward inclusion follows from `(ALC.2)` for every tail. For the reverse inclusion, fix
`y` in the right side and consider compact fibres

\[
 D_N=C_N\cap f^{-1}\{y\}.
\]

By `(ALC.2)`, every `D_N` is nonempty. They are closed, nested, and contained in compact `C_0`, so
their intersection is nonempty. Any point in that intersection lies in `Core(x)` and maps to `y`.
QED.

This fibre argument is load-bearing. The general identity
`f(intersection C_N)=intersection f(C_N)` is false without compact nested fibres.

## 4. Common recovery is formation-neutral

Let

\[
 E\mathop{\longrightarrow}^{R}F
 \mathop{\longrightarrow}^{Q}E,
 \qquad Q R=\operatorname{id}_E,
 \tag{ALC.4}
\]

where `R,Q` are continuous affine.

### Theorem 4.1 -- exact joint recovery

\[
 \boxed{
 R(\operatorname{Core}(x))=\operatorname{Core}(R\circ x),
 \qquad
 Q(\operatorname{Core}(R\circ x))=\operatorname{Core}(x).}
 \tag{ALC.5}
\]

### Proof

Apply `(ALC.3)` to `R`, then to `Q` on the compact convex image `R(K)`. The second formed history is
`Q R x=x`. QED.

Thus a common left-invertible reporter family neither creates nor destroys asymptotic law
multiplicity. This is set-level reconstruction, not a KL or entropy claim.

## 5. Functional-equation action and neutral lift

Let `J : E -> E` be a continuous affine involution:

\[
 J^2=\operatorname{id}_E.
 \tag{ALC.6}
\]

### Theorem 5.1 -- formed involution

\[
 \boxed{
 J(\operatorname{Core}(x))=\operatorname{Core}(Jx),
 \qquad
 J(\operatorname{Core}(Jx))=\operatorname{Core}(x).}
 \tag{ALC.7}
\]

This is `(ALC.3)` applied twice, using compactness of `J(K)` and `J^2x=x`.

Now let `Jhat : F -> F` be a continuous affine lift satisfying

\[
 \widehat J R=R J.
 \tag{ALC.8}
\]

### Theorem 5.2 -- information-neutral lifted action

\[
 \boxed{
 \begin{aligned}
 \widehat J\bigl(\operatorname{Core}(Rx)\bigr)
   &=\operatorname{Core}(RJx),\\
 Q\widehat J\bigl(\operatorname{Core}(Rx)\bigr)
   &=J\bigl(\operatorname{Core}(x)\bigr),\\
 Q\widehat J^2Rz&=z\qquad(z\in E).
 \end{aligned}}
 \tag{ALC.9}
\]

### Proof

Apply `(ALC.3)` to `Jhat` on the history `Rx` and use the intertwining identity `(ALC.8)`; this
gives the first line. Apply exact recovery `(ALC.5)` to the transformed history `Jx`, then use
`(ALC.7)`; this gives the second. Finally

\[
 Q\widehat J^2Rz
 =Q\widehat J R(Jz)
 =QR(J^2z)=z.
\]

QED.

This is the requested functional-equation action on packet formation. Its exact conclusion is
neutrality: the lift transports the complete source core and reconstructs it, but supplies no
selection equation.

## 6. Asymptotic laws exactify on the core

Assume now that `E,F` are real normed spaces.

### Theorem 6.1 -- convergent histories have singleton core

If `x_n -> a`, then

\[
 \operatorname{Core}(x)=\{a\}.
 \tag{ALC.10}
\]

### Proof

For any `y != a`, eventually the tail lies in the closed ball
`closedBall(a,dist(y,a)/2)`. The ball is closed and convex, so its closed convex hull remains in the
ball and cannot contain `y`. Hence every core point is `a`. Conversely `a` belongs to the closure
of every tail and therefore to every tail hull. QED.

### Theorem 6.2 -- approximate-kernel exactification

For a continuous affine map `A : E -> F`,

\[
 A(x_n)\longrightarrow0
 \quad\Longrightarrow\quad
 A(y)=0\quad\text{for every }y\in\operatorname{Core}(x).
 \tag{ALC.11}
\]

### Proof

By affine exchange,
`A(Core(x))=Core(Ax)`. The latter is `{0}` by Theorem 6.1. QED.

### Corollary 6.3 -- approximate-fixed exactification

For a continuous affine endomorphism `T`,

\[
 T(x_n)-x_n\longrightarrow0
 \quad\Longrightarrow\quad
 T(y)=y\quad\text{for every }y\in\operatorname{Core}(x).
 \tag{ALC.12}
\]

Apply Theorem 6.2 to `T-id`.

## 7. Relation to existing common-kernel packet mechanics

`ConstitutiveFunctionalEquationPacketLift` already proves that common Markov-kernel formation
preserves KL and Jeffreys information. Theorem 5.2 is not presented as a rediscovery of that
metric result. It extends the grammar in a different direction:

- the input is an entire open/cofinal history, not one probability packet;
- formation is canonical intersection of all compact convex tail hulls;
- the output retains every persistent asymptotic law simultaneously;
- asymptotic equations become exact on every retained law.

The neutral-lift clause is a compatibility check. The new leverage is `(ALC.11)`--`(ALC.12)`:
route-specific approximate symmetries, conservation laws, and null constraints can now be moved to
an exact common carrier without choosing an ultrafilter or invariant mean.

## 8. Sharp limits and selection gate

1. Compactness is essential for the reverse affine-exchange inclusion.
2. Convexification loses non-affine and phase-sensitive structure unless those are represented by
   affine coordinates in a larger law space.
3. A left inverse is essential for exact recovery.
4. Functional-equation compatibility transports the core; it does not make the core a singleton.
5. Selection requires an additional global formation/properness law forcing either
   `Core(x)={critical law}` or all noncritical core points to have infinite source cost.
6. No arithmetic source history, Xi specialization, or RH conclusion occurs here.

## 9. Lean correspondence

The Lean module certifies:

- `asymptoticLawCore_nonempty`;
- `asymptoticLawCore_convex`;
- `asymptoticLawCore_isCompact`;
- `continuousAffine_image_lawTailHull`;
- `continuousAffine_image_asymptoticLawCore`;
- `commonRecovery_asymptoticLawCore`;
- `continuousAffine_involution_asymptoticLawCore`;
- `liftedFunctionalEquation_informationNeutral`;
- `asymptoticLawCore_eq_singleton_of_tendsto`;
- `continuousAffine_vanishes_on_asymptoticLawCore`;
- `continuousAffine_fixed_on_asymptoticLawCore`.

All statements are unconditional implications from their explicit typed hypotheses. No `sorry`,
`admit`, new axiom, `opaque`, or `unsafe` declaration occurs.

## 10. Log

- 2026-08-14 -- compact-convex formation and affine exchange proved on paper.
- 2026-08-14 -- recovery and functional-equation lift closed; existing Markov packet result recorded
  as parent rather than claimed as new.
- 2026-08-14 -- exactification survivor proved and formalized scratch-first in Lean.
