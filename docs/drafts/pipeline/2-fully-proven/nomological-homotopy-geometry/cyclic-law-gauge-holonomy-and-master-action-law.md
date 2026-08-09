# Cyclic law gauge holonomy and master-action law

- **ID:** `nhg-cyclic-law-gauge-holonomy-master-action`
- **Stage:** 2 — fully proven on paper
- **Status:** `[PAPER-PROVED] [LEAN FORMALIZED — DOCUMENTED IN PLACE] [LEAF CHECK CLEAN]`
  `[NATIVE NHG DYNAMICS] [STRUCTURED GAUGE INTEGRATION] [STABILIZER HOLONOMY]`
  `[MASTER ACTION] [NO ROUTE INPUT] [NOT RH]`

## 1. Native cyclic law chart

Retain the cyclic coderivation Lie algebra

\[
 \mathfrak g=\operatorname{Coder}_{\mathrm{cyc}}(\widehat T^c(sV))
\tag{GH.1}
\]

with complete positive-arity filtration. Let

\[
 \mathcal G=\exp(F^1\mathfrak g^0)
\tag{GH.2}
\]

be the pronilpotent group of filtered cyclic formal coordinate changes. It acts on sourced laws by

\[
 F\cdot Q=FQF^{-1}.
\tag{GH.3}
\]

Fix a cyclic law `Q` with `Q^2=0`.

## 2. Integrated gauge transport

### Theorem 2.1 — gauge paths integrate the anchor

For every filtration-continuous path `xi_t in F^1 g^0`, the formal differential equation

\[
 \dot F_t=\xi_tF_t,
 \qquad F_0=1,
\tag{GH.4}
\]

has a unique coefficientwise convergent solution `F_t in G`. The transported law

\[
 Q_t=F_tQF_t^{-1}
\tag{GH.5}
\]

satisfies

\[
 \boxed{
 \dot Q_t=[\xi_t,Q_t],
 \qquad Q_t^2=0.}
\tag{GH.6}
\]

If every `F_t` is cyclic and filtration-preserving, then the pairing and arity filtration are
preserved along the path.

### Proof

The Picard series for `(GH.4)` converges in every nilpotent filtration quotient, hence in the
complete inverse limit. Differentiate `(GH.5)` and use
`d(F_t^{-1})/dt=-F_t^{-1}xi_t` to obtain the first identity in `(GH.6)`. The second follows from

\[
 Q_t^2=F_tQ^2F_t^{-1}=0.
\tag{GH.7}
\]

Cyclic filtered automorphisms preserve their defining structures by construction. QED.

Thus the infinitesimal anchor `xi mapsto [Q,xi]` in the native chart is integrable, not merely a
formal tangent assignment.

## 3. Gauge covariance of the full local law geometry

### Theorem 3.1

For `Q'=FQF^{-1}`, conjugation gives an isomorphism of sourced deformation complexes

\[
 \boxed{
 \operatorname{Ad}_F:
 (\mathfrak g,[Q,-])
 \xrightarrow{\sim}
 (\mathfrak g,[Q',-]).}
\tag{GH.8}
\]

It preserves the arity filtration and cyclic structure. Consequently it transports:

1. tangent, automorphism, and obstruction cohomology;
2. transferred minimal operations;
3. partial-flattening spaces and curvature obstruction spectra;
4. every invariant constructed functorially from the cyclic filtered deformation complex.

### Proof

For every coderivation `eta`,

\[
 \operatorname{Ad}_F[Q,\eta]
 =[FQF^{-1},F\eta F^{-1}]
 =[Q',\operatorname{Ad}_F\eta].
\tag{GH.9}
\]

This proves `(GH.8)`. The remaining claims are functoriality under a strict structured
isomorphism. QED.

This is the exact native gauge principle required by NHG. Equality of scalar observers is neither
necessary nor sufficient for `(GH.8)`.

## 4. Stabilizer holonomy of a closed law orbit

Let

\[
 \mathcal G_Q=\{F\in\mathcal G:FQF^{-1}=Q\}
\tag{GH.10}
\]

be the structured stabilizer.

### Theorem 4.1 — law-loop lift endpoint

If the projected law path `(Q_t)` in the gauge orbit closes, `Q_1=Q_0=Q`, then

\[
 \boxed{F_1\in\mathcal G_Q.}
\tag{GH.11}
\]

Conversely, every stabilizer element connected to the identity by a path in `G` is the endpoint of
a lifted closed law-orbit path. Concatenation multiplies endpoints.

Hence the principal fibration

\[
 \mathcal G_Q\longrightarrow\mathcal G
 \longrightarrow\mathcal G/\mathcal G_Q
\tag{GH.12}
\]

realizes closed observer projection with a possibly nonclosed marked gauge history. Its
homotopy-fibre component boundary records the component of `F_1`; the full element `F_1` is the
chosen transport holonomy and can be nontrivial even in the identity component.

### Proof

Closedness and `(GH.5)` give `F_1QF_1^{-1}=Q`, proving `(GH.11)`. For the converse, choose a path
from `1` to `F in G_Q` and project it to the orbit. Endpoint multiplication follows from path
concatenation and the group law. The final distinction follows from the long exact sequence of
`(GH.12)`. QED.

Local deformation cohomology does not determine this stabilizer element. It determines the
infinitesimal law germ; global gauge history remains additional integrated data.

## 5. Cyclic Hamiltonian and master equation

The fixed nondegenerate cyclic pairing gives the pointed noncommutative formal manifold on `sV` a
constant formal symplectic form. Cyclic coderivations are Hamiltonian. Normalize the Hamiltonian of
`Q=sum m_n` to have zero constant term and write

\[
 \mathcal S_Q(x)=
 \sum_{n\geq1}\frac1{n+1}
 \langle x,m_n(x,\ldots,x)\rangle,
\tag{GH.13}
\]

with the standard shifted cyclic signs.

### Theorem 5.1 — source-derived master action

The variational derivative of `(GH.13)` is the `A_infinity` Maurer--Cartan vector field:

\[
 \boxed{
 \delta\mathcal S_Q(x)[h]
 =\left\langle h,
 \sum_{n\geq1}m_n(x,\ldots,x)\right\rangle.}
\tag{GH.14}
\]

Under the Hamiltonian/coderivation correspondence,

\[
 \boxed{
 Q^2=0
 \quad\Longleftrightarrow\quad
 \{\mathcal S_Q,\mathcal S_Q\}=0.}
\tag{GH.15}
\]

For a cyclic coordinate change `F`,

\[
 \mathcal S_{FQF^{-1}}
 =\mathcal S_Q\circ F^{-1}
\tag{GH.16}
\]

under the zero-constant normalization.

### Proof

Vary the `n`th summand of `(GH.13)`. Cyclicity identifies its `n+1` contributions, cancelling the
denominator and giving `(GH.14)`. The Hamiltonian vector field of `S_Q` is therefore `Q`.
Commutators of Hamiltonian vector fields correspond to Poisson brackets of normalized Hamiltonians,
so `[Q,Q]=0` is equivalent to `(GH.15)`. A symplectic formal coordinate change transports
Hamiltonian vector fields and pulls back their normalized Hamiltonians, proving `(GH.16)`. QED.

The native law chart therefore derives its formal action from the same sourced coderivation that
defines its field equation and gauge transport.

## 6. What remains analytic

The master action does not imply:

1. convergence beyond the declared formal filtration;
2. a positive real form or lower bound;
3. coercivity on gauge-reduced histories;
4. properness of the stabilizer action;
5. absence of a global gauge anomaly;
6. finite cost for any specified path.

These are analytic or global field questions. Adding an arbitrary norm or cost would not close
them.

## 7. Field consequence

One native object now supplies the exact chain

\[
 \boxed{
 Q^2=0
 \Longleftrightarrow
 \{\mathcal S_Q,\mathcal S_Q\}=0,
 \qquad
 \dot Q=[\xi,Q],
 \qquad
 Q_1=Q_0\Rightarrow F_1\in\mathcal G_Q.}
\tag{GH.17}
\]

Field equation, gauge anchor, integrated history, stabilizer holonomy, and formal action are thus
different faces of one cyclic law geometry. Observer topology, positivity, and properness remain
separate structures with typed comparison maps.

## 8. Parent boundary

Coderivation integration, cyclic `A_infinity` Hamiltonians, and the master equation are established
formal noncommutative geometry. See Kontsevich--Soibelman,
<https://arxiv.org/abs/math/0606241>, and Cho--Lee,
<https://arxiv.org/abs/1002.3653>. The role here is exact field closure: the native NHG chart now has
structured gauge covariance, integrated gauge history, stabilizer holonomy, and a source-derived
formal action without importing any proof route.

## 9. Lean formalization status

Formalized without moving this card:

- `CyclicGaugeHolonomyMasterAction.lean` constructs an explicit coefficientwise Picard recursion
  for a time-dependent formal gauge generator and proves existence and uniqueness of the completed
  formal solution.
- It proves conjugation preserves composition squares and intertwines both parity pieces of the
  deformation differential, proves closed lifted law paths have stabilizer-valued endpoints, and
  formalizes projected closure for stabilizer paths.
- It proves cyclic action covariance at every finite arity quotient and formalizes an injective
  Hamiltonian/coderivation correspondence under which the Poisson master equation is equivalent to
  `Q^2 = 0`. Foreground `lake env lean <file>` passes with no warnings or errors. Umbrella import is
  wired; aggregate build and axiom audit remain in final all-card audit.
