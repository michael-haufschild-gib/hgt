# Quadratic anchors and hidden transport obey one triangle law

- **ID:** `anchored-transport-bianchi-law`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / ANCHORED-CURVATURE BRIDGE / NOT NEW MATHEMATICS
- **Scientific status:** `[PROVED HERE] [LEAN-FORMALIZED] [PARENT ALGEBRA]`
  `[NOT NEW SCIENTIFIC KNOWLEDGE] [NO GRAVITY PROVED]`
- **Parent conjecture:** `../../1-in-progress/composition-curvature-universal-law.md`
- **Sibling:** `composition-transport-projective-bianchi-law.md`
- **Earlier linear parent:** `event-descent-transgression-bianchi.md`
- **Lean:** `formal/GaloisForLFunctions/HTGeometry/AnchoredTransportBianchi.lean`
- **Statement:** Failure to transport a quadratic public anchor around a comparison triangle is
  exactly coupled to both hidden-carrier path holonomy and public-carrier path holonomy.

## Setup

Let \(V\) be a hidden event carrier and \(W\) a public-report carrier. At event \(i\), let

\[
\beta_i:V\times V\longrightarrow W
\]

be bilinear and define its quadratic public anchor

\[
\Gamma_i(x)=\beta_i(x,x).
\tag{AB.1}
\]

Let

\[
T_{ij}:V\to V,\qquad L_{ij}:W\to W
\]

be hidden and public comparisons. Define the anchor-transport defect

\[
A_{ij}(x)
=\Gamma_j(T_{ij}x)-L_{ij}\Gamma_i(x).
\tag{AB.2}
\]

The two path defects are

\[
K^V=T_{12}T_{01}-T_{02},\qquad
K^W=L_{12}L_{01}-L_{02}.
\tag{AB.3}
\]

## Exact anchored triangle law

### Theorem 1

`[PROVED HERE]`

\[
\begin{aligned}
&A_{12}(T_{01}x)+L_{12}A_{01}(x)-A_{02}(x)\\
&\quad=
\beta_2(K^Vx,T_{02}x)
+\beta_2(T_{02}x,K^Vx)
+\beta_2(K^Vx,K^Vx)
-K^W\Gamma_0(x).
\end{aligned}
\tag{AB.4}
\]

### Proof

Substitute `(AB.2)`. The two intermediate terms
\(L_{12}\Gamma_1(T_{01}x)\) cancel. The remaining expression is

\[
\Gamma_2(T_{12}T_{01}x)-\Gamma_2(T_{02}x)
-(L_{12}L_{01}-L_{02})\Gamma_0(x).
\tag{AB.5}
\]

By `(AB.3)`,

\[
T_{12}T_{01}x=T_{02}x+K^Vx.
\]

Expand \(\beta_2(T_{02}x+K^Vx,T_{02}x+K^Vx)\) by bilinearity and cancel
\(\beta_2(T_{02}x,T_{02}x)\). The result is `(AB.4)`. \(\square\)

The term \(\beta_2(K^Vx,K^Vx)\) is a finite nonlinear holonomy term. A first-order treatment
keeps only the two cross terms and therefore does not state the exact law.

### Corollary 1: flat hidden and public triangles

If \(K^V=0=K^W\), then

\[
A_{12}\circ T_{01}+L_{12}\circ A_{01}=A_{02}.
\tag{AB.6}
\]

Thus anchor-transport defects form a cocycle only when both comparison levels are flat.

## What this tells the programme

The candidate universal law distinguishes:

- hidden/coherent event transport;
- public causal transport; and
- failure to intertwine the public anchor.

Theorem 1 proves these cannot be chosen independently even in the first finite quadratic model.
The anchor defect around a triangle is sourced exactly by the mismatch between hidden and public
path closure:

```text
hidden comparison holonomy
  + public comparison holonomy
  -> forced anchor-transport defect.
```

This is the finite algebraic shadow sought by the phrase “gravity is failure to glue neighboring
causal reports.” It does not identify \(W\) with spacetime, \(\Gamma\) with a metric, or \(A\) with
gravity. Those identifications remain conjectural and require positivity, Lorentz signature,
dynamics, and an equivalence-principle limit.

Together with the sibling composition theorem, the corpus now has two parallel exact laws:

\[
\begin{array}{c|c}
\text{transported structure} & \text{forced coupling}\\
\hline
\text{bilinear composition }\mu
& \text{composition defect couples to hidden path holonomy}\\
\text{quadratic public anchor }\Gamma
& \text{anchor defect couples to hidden and public path holonomy}.
\end{array}
\]

The next theorem must place both rows inside one typed higher coherence identity rather than merely
listing them.

## Novelty and physics boundary

Equation `(AB.4)` is an elementary expansion of a quadratic map under a finite additive defect.
It belongs to standard parent algebra. No mathematical novelty is claimed.

The earlier corpus theorem `event-descent-transgression-bianchi.md` proves a linear covariant
seam--triangle Leibniz identity. Equation `(AB.4)` is the quadratic-anchor extension on two typed
carriers; its extra cross and quadratic hidden-holonomy terms are exactly what linear seam algebra
does not display.

No result here proves:

- an endogenous public carrier;
- positivity or the Lorentz cone;
- a spacetime manifold;
- the equivalence principle;
- Einstein curvature or field equations; or
- coupling to stress-energy.

The research target is a source-generated positive anchored comparison object in which `(AB.4)`
is forced as one projection of higher coherence and whose continuum limit uniquely yields the
gravitational Bianchi identity and sourced Einstein equation.

## Lean status

Lean proves:

- `anchorTransportDefect_triangle_bianchi`; and
- `anchorTransportDefect_flat_triangle`.

No `sorry`, `admit`, new `axiom`, `opaque`, `unsafe`, or computation is used. `#print axioms`
reports only `propext`, `Classical.choice`, and `Quot.sound`.

## Log

- 2026-07-30 — Derived and Lean-formalized exact finite anchor triangle law and flat cocycle
  corollary.
