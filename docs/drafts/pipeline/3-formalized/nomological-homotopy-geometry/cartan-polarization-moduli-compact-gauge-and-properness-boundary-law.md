# Cartan polarization moduli, compact gauge, and properness-boundary law

- **ID:** `nhg-cartan-polarization-moduli`
- **Stage:** 3 — formalized in Lean 4
- **Lean gate:** [LEAN-PROVED] [AXIOM AUDITED] [UMBRELLA BUILD PASSED] (2026-08-13)
- **Status:** `[PAPER-PROVED] [UNIVERSAL FIELD THEOREM] [POLARIZATION MODULI]`
  `[COMPACT GAUGE REDUCTION] [PROPER NORM AFTER CHOICE] [NO CANONICAL POSITIVITY]`
  `[NO ROUTE INPUT] [NOT RH] [LEAN-PROVED]`

## 1. Indefinite cyclic law sector

Let `E` be a finite-dimensional real vector space with a nondegenerate symmetric bilinear form

\[
 B:E\otimes E\longrightarrow\mathbb R
\tag{CP.1}
\]

of signature `(p,q)`. A **Cartan polarization** is a linear map `theta:E->E` satisfying

\[
 \theta^2=1,
 \qquad
 B(\theta x,\theta y)=B(x,y),
 \qquad
 g_\theta(x,y)=B(x,\theta y)>0.
\tag{CP.2}
\]

Write `Pol(B)` for the space of all such polarizations.

## 2. Polarization is a moduli space

### Theorem 2.1

The orthogonal group `O(B)` acts transitively on `Pol(B)`. For every `theta`, its stabilizer is

\[
 K_\theta\cong O(p)\times O(q),
\tag{CP.3}
\]

and therefore

\[
 \boxed{
 \operatorname{Pol}(B)
 \cong O(p,q)/(O(p)\times O(q)).}
\tag{CP.4}
\]

This space is contractible. If `pq>0`, it is noncompact and has more than one point.

### Proof

The `+1` and `-1` eigenspaces of `theta` are `B`-orthogonal; `B` is positive on the first and
negative on the second because `(CP.2)` makes `g_theta` positive. Thus a polarization is equivalent
to a decomposition

\[
 E=E_+\oplus E_-
\tag{CP.5}
\]

into positive and negative subspaces of dimensions `p` and `q`. Witt's theorem makes `O(p,q)`
transitive on these decompositions. The stabilizer preserves both summands and is
`O(p) times O(q)`, proving `(CP.4)`. The quotient is the standard noncompact symmetric space; its
Cartan decomposition identifies it diffeomorphically with a Euclidean space of dimension `pq`,
hence it is contractible and noncompact when `pq>0`. QED.

### Corollary 2.2 — no invariant positive observer

If `pq>0`, the indefinite pairing `B` does not canonically select a positive metric. More strongly,
there is no point of `Pol(B)` fixed by the full group `O(B)`.

### Proof

A fixed point would have stabilizer `O(B)`, contradicting `(CP.3)` because
`O(p) times O(q)` is proper in `O(p,q)` when `pq>0`. QED.

Thus cyclicity or self-duality alone cannot define the positive observer used in a norm, Gram,
probability, or cost construction.

## 3. Compact gauge after polarization

### Theorem 3.1

Choosing `theta` reduces the pairing-preserving gauge group from `O(B)` to the compact group

\[
 \boxed{
 O(B)\cap O(g_\theta)=K_\theta.}
\tag{CP.6}
\]

The positive radius

\[
 R_\theta(x)=g_\theta(x,x)
\tag{CP.7}
\]

is `K_theta`-invariant and proper on `E`. It descends to a proper function on the Hausdorff orbit
space `E/K_theta`.

### Proof

An element preserving both `B` and `g_theta(x,y)=B(x,theta y)` commutes with `theta`, hence preserves
the decomposition `(CP.5)`; this gives `(CP.6)`. The group is compact. Positive definiteness makes
closed `R_theta`-sublevels compact in finite dimension. A compact group action is proper and closed;
the image of each compact sublevel in the quotient is compact, proving properness of the descended
radius. QED.

This is a genuine analytic gain, but it is conditional on a chosen polarization. It does not make
the homotopy Chern--Simons/master action coercive.

## 4. No uniform metric across polarization space

Even in dimension two, the family of positive metrics is not uniformly equivalent.

### Counterexample 4.1

On `E=R^2` take

\[
 B=\begin{pmatrix}1&0\\0&-1\end{pmatrix},
 \qquad
 h_t=\begin{pmatrix}\cosh t&\sinh t\\\sinh t&\cosh t\end{pmatrix}
 \in O(1,1),
\tag{CP.8}
\]

and `theta_t=h_t theta_0 h_t^(-1)` for `theta_0=diag(1,-1)`. Then the condition number of
`g_(theta_t)` relative to `g_(theta_0)` is `e^(4|t|)`.

Hence a family escaping in `Pol(B)` can have bounded algebraic cyclic data but unbounded positive
observer distortion. In an infinite or cofinal system this can create inequivalent completions.

## 5. Native dual-number specialization

The Frobenius pairing in the native dual-number NHG chart is

\[
 \begin{pmatrix}0&1\\1&0\end{pmatrix},
\tag{CP.9}
\]

which has signature `(1,1)`. Therefore its positive real forms constitute

\[
 O(1,1)/(O(1)\times O(1)),
\tag{CP.10}
\]

not one canonical metric. The sourced cyclic algebra law selects the indefinite pairing but does
not select a point of `(CP.10)`.

This is an exact native no-go: completing the dual-number law chart in a positive norm requires an
additional polarization section. Once selected, the remaining linear gauge is compact and the
positive radius is proper.

## 6. Field geometry

An analytic NHG field with indefinite cyclic pairing must therefore be enlarged from law space
`Law` to a polarization bundle

\[
 \boxed{
 \operatorname{Pol}(\mathcal E)
 \longrightarrow \operatorname{Law},
 \qquad
 \operatorname{Pol}(\mathcal E)_\alpha
 =O(p_\alpha,q_\alpha)/(O(p_\alpha)\times O(q_\alpha)).}
\tag{CP.11}
\]

A positive observer is a section, local section, or reduction of this bundle. Its singularities,
monodromy, and failure to extend are **polarization horizons**. They are distinct from curvature,
component, holonomy, and completion horizons.

### Theorem 6.1 — ordinary existence versus source-natural reduction

If the law base is paracompact and the signature is constant, `(CP.11)` has an ordinary continuous
section because its fibre is contractible. Such a section depends on auxiliary choices.

For a gauge group `G` acting on the pairing bundle, a `G`-equivariant polarization exists exactly
when the orthogonal structure group admits a `G`-equivariant reduction to
`O(p) times O(q)`. In particular, over a point with the full group `G=O(p,q)` and `pq>0`, no
equivariant section exists.

### Proof

A bundle with contractible fibre over a paracompact base admits a section by standard obstruction
theory. A polarization section is the same as a reduction of the orthogonal frame bundle to the
stabilizer `(CP.3)`; adding `G`-equivariance on either side gives the stated equivalence. The final
claim is Corollary 2.2. QED.

Thus the finite constant-signature horizon is not ordinary section existence. It is failure of a
source-natural, gauge-equivariant, parallel, or uniformly controlled section.

### Theorem 6.2 — holonomy criterion for parallel positivity

Let `nabla` be a connection preserving `B` on a connected law base, and fix `x`. A global
`nabla`-parallel Cartan polarization exists exactly when the holonomy group fixes a point of
`Pol(B_x)`:

\[
 \boxed{
 \nabla\theta=0
 \quad\Longleftrightarrow\quad
 \operatorname{Hol}_x(\nabla)
 \subseteq K_{\theta_x}
 \text{ for some }\theta_x.}
\tag{CP.12}
\]

When this holds, `nabla` preserves the positive metric `g_theta` and its holonomy lies in a compact
group.

### Proof

If `theta` is parallel, parallel transport commutes with it, so every holonomy element fixes
`theta_x`; Theorem 3.1 identifies the stabilizer with `K_(theta_x)`. Conversely, if holonomy fixes
`theta_x`, transport `theta_x` to any point along a path. Two paths give the same result because
their difference is a holonomy loop fixing `theta_x`. The transported section is parallel and
positive. QED.

## Lean formalization status

- **Module:** `GaloisForLFunctions.HTGeometry.NomologicalHomotopyGeometry.FlatCartanHolonomy`
- **Exact promoted theorem:** `polarConditionNumber_eq` formalizes the native two-dimensional
  polarization specialization `(CP.8)` with exact value `exp (4 * |u|)`;
  `polarConditionNumber_diverges` proves its nonuniformity consequence.
- **Verification:** NHG umbrella build and scratch `#print axioms` audit passed on 2026-08-13.

## 7. Scope

1. Finite-dimensional constant-signature fibres are assumed. Signature jumps require a stratified
   polarization stack.
2. Contractibility gives ordinary sections over paracompact constant-signature bases, but not a
   source-natural, equivariant, parallel, or uniformly controlled section.
3. Compact residual gauge and proper norm do not imply the sourced master action is bounded below
   or coercive.
4. Infinite-dimensional Krein/Tate versions need a declared restricted group and topology.
5. No physical metric, probability measure, source normalization, or RH statement follows.

The homogeneous-space description is classical Cartan symmetric-space geometry. NHG uses it as a
load-bearing field layer: positivity is a choice of polarization over law moduli, while cyclic
self-duality is the prior indefinite structure.
