# Arbitrary-graph quantum temporal-curvature law

- **ID:** `arbitrary-graph-quantum-temporal-curvature-law`
- **Stage:** 2-fully-proven
- **Type:** UNIVERSAL FINITE QUANTUM NETWORK THEOREM / PROJECTIVE SPECTRAL
  RANK / RECURRENCE / INTERACTION GEOMETRY
- **Date:** 2026-07-30
- **Paper-proof status:** `[DEPENDENCY-CLOSED]`
- **Formal status:** `[PARTIAL — DO NOT MOVE TO STAGE 3]`
- **Novelty status:** `[EXTERNAL PRIORITY AUDIT INCOMPLETE]`
- **Manuscript rule:** no statement from this card enters the manuscript
  until its exact dependency chain is unconditionally formalized.

## Theorem

Let \(G=(V,E)\) be any finite undirected graph. Give each vertex \(v\) a
complex Hilbert space \(\mathcal H_v\) of arbitrary dimension \(q_v\ge2\).
Let \(\mathcal L_G\) be the real vector space of Hermitian Hamiltonians
containing arbitrary one-site terms and arbitrary two-site terms on the
edges of \(G\).

For \(H\in\mathcal L_G\), let
\(\lambda_1(H),\ldots,\lambda_D(H)\) be its eigenvalues, counted with
multiplicity, and define
\[
  \tau(H)
  =
  \dim_{\mathbb Q}
  \operatorname{span}_{\mathbb Q}
  \{\lambda_j(H)-\lambda_1(H):2\le j\le D\}.
  \tag{1}
\]
For each connected component \(C\) of \(G\), put
\[
  D_C=\prod_{v\in C}q_v.
\]

Then a dense, full-Lebesgue-measure \(G_\delta\) subset of
\(\mathcal L_G\) satisfies
\[
  \boxed{
  \tau(H)=\sum_{C\in\pi_0(G)}(D_C-1).
  }
  \tag{2}
\]

The statement holds already on the real-symmetric local Hamiltonian slice.

## Corollary 1 — interaction multiplication

For a connected graph,
\[
  \tau(H)+1=\prod_{v\in V}q_v.
  \tag{3}
\]
If one edge joins previously disconnected components \(A,B\), generic
temporal dimension changes from
\[
  \tau_{\rm before}=(D_A-1)+(D_B-1)
\]
to
\[
  \tau_{\rm after}=D_AD_B-1.
\]
Therefore
\[
  \boxed{
  \tau_{\rm after}
  =
  \tau_A+\tau_B+\tau_A\tau_B,
  \qquad
  \Delta\tau=\tau_A\tau_B.
  }
  \tag{4}
\]

The connecting interaction may be arbitrarily small. Every neighborhood of
the zero-edge Hamiltonian in the enlarged connected parameter space contains
maximal-rank Hamiltonians. Such a Hamiltonian must have a nonzero connecting
term because the zero-edge subspace obeys the strict upper bound in `(2)`.

## Corollary 2 — temporal curvature reconstructs the supplied interaction graph

For every vertex subset \(S\subseteq V\), retain the one-site terms in \(S\)
and the edge terms of the induced graph \(G[S]\). There is one dense,
full-measure \(G_\delta\) set of coefficient assignments for which all
finitely many induced restrictions satisfy `(2)` simultaneously. Define
\[
  \tau(S)
  =
  \sum_{C\in\pi_0(G[S])}
  \left(\prod_{v\in C}q_v-1\right).
  \tag{5}
\]

For distinct vertices \(u,v\), define temporal curvature
\[
  \kappa(u,v)
  =
  \tau(\{u,v\})-\tau(\{u\})-\tau(\{v\}).
  \tag{6}
\]
Then
\[
  \boxed{
  \kappa(u,v)
  =
  \begin{cases}
  (q_u-1)(q_v-1),&\{u,v\}\in E,\\
  0,&\{u,v\}\notin E.
  \end{cases}
  }
  \tag{7}
\]

Hence
\[
  \boxed{\{u,v\}\in E\iff\kappa(u,v)>0.}
  \tag{8}
\]
The complete two-body interaction graph, its connected components, graph
metric, cycles and topology are therefore determined by the set function
\(\tau\), relative to the supplied subsystem decomposition. This does not
derive physical space from temporal data: the vertex factors and their
induced restrictions are inputs. “Space is temporal curvature” is therefore
not an authorized interpretation of `(8)`.

## Corollary 2b — exact temporal factorization lattice

For every nonempty \(S\subseteq V\) and every set partition \(\Pi\) of
\(S\), define partition curvature
\[
  \mathcal K_\Pi(S)
  =
  \tau(S)-\sum_{B\in\Pi}\tau(B).
  \tag{8a}
\]
Then
\[
  \boxed{\mathcal K_\Pi(S)\ge0,}
  \qquad
  \boxed{
  \mathcal K_\Pi(S)=0
  \iff
  \text{every component of \(G[S]\) lies in one block of \(\Pi\)}.
  }
  \tag{8b}
\]
Consequently \(G[S]\) is connected exactly when every nontrivial partition
has strictly positive curvature. Pair curvature `(6)` is the two-vertex
case; the full zero-partition lattice gives a cancellation-free
factorization classifier.

To prove `(8b)`, fix a component \(C\) of \(G[S]\). Intersect the blocks of
\(\Pi\) with \(C\), refine those intersections into induced connected
fragments \(F_1,\ldots,F_m\), and put
\[
  d_j=\prod_{v\in F_j}q_v\ge2.
\]
The contribution of \(C\) to the block-rank sum is
\(\sum_j(d_j-1)\); its contribution to \(\tau(S)\) is
\(\prod_jd_j-1\). For \(d_j\ge2\),
\[
  \prod_jd_j-1\ge\sum_j(d_j-1),
\]
with equality exactly when \(m=1\). Summing over \(C\) proves nonnegativity.
Equality holds exactly when no component is split between partition blocks.

## Corollary 3 — exact generic recurrence law

For connected \(G\), maximal projective rank makes the phase orbit dense in
\(\mathbb T^{D-1}\). A positive exact global projective return would give a
nonzero common period and hence a nontrivial rational relation, so no such
return exists. Approximate returns remain recurrent.

For \(0<\varepsilon<2\), the operator-norm projective return set has
asymptotic time density
\[
  \boxed{
  \left(
    \frac{2\arcsin(\varepsilon/2)}{\pi}
  \right)^{D-1}.
  }
  \tag{9}
\]
Thus interaction multiplication and recurrence scarcity are the same rank
law, not separate results.

## Proof

### 1. Real all-vertex-good Hamiltonians

For a simple real-symmetric local Hamiltonian \(H\) and a vertex \(u\),
form the transition graph \(\mathcal G_u(H)\) on energy eigenstates. Join
\(\alpha\ne\beta\) when some real-symmetric one-site operator \(A_u\)
satisfies
\[
  \psi_\alpha^T A_u\psi_\beta\ne0.
  \tag{10}
\]
Call \(H\) **all-vertex good** when every \(\mathcal G_u(H)\) is connected
and non-bipartite.

This property is open on the simple-spectrum locus: finitely many selected
nonzero matrix elements, spanning edges and odd-cycle edges survive small
real-symmetric perturbations.

### 2. Two-site base

For a two-vertex graph the allowed edge term is the full real-symmetric
matrix space on \(\mathcal H_u\otimes\mathcal H_v\).

Fix a spectral pair \(\alpha\ne\beta\) and endpoint \(u\). On the orthogonal
eigenbasis group, failure of every real-symmetric local probe is the
vanishing of the symmetric part of
\[
  \operatorname{Tr}_{\bar u}
  |\psi_\beta\rangle\langle\psi_\alpha|.
  \tag{11}
\]
It is a proper real-algebraic condition: send the two columns to product
basis vectors \(|0,z\rangle,|1,z\rangle\); the symmetric exchange probe has
nonzero matrix element. A column sign change moves this witness between the
two determinant components of the orthogonal group without changing
nonvanishing. Therefore the failure set has empty interior and measure zero
in each component.

There are finitely many pairs and two endpoints. One orthogonal eigenbasis
makes both endpoint transition graphs complete. Choose a real eigenvalue
list of maximal projective rank. The resulting allowed real-symmetric
Hamiltonian is simple, maximally projective and all-vertex good.

### 3. Leaf attachment preserves every old transition graph

Assume a tree \(T\) has a simple, maximally projective, real-symmetric,
all-vertex-good Hamiltonian \(H_T\). Attach a leaf \(v\) at \(u\), with
arbitrary \(q_v\ge2\), and start from
\[
  H_0
  =
  H_T\otimes I+
  I\otimes\sum_{a=0}^{q_v-1}s_a|a\rangle\langle a|,
  \tag{12}
\]
where the real shifts make all product energies distinct.

Fix any old observer vertex \(r\). Pick an old spectral label \(\gamma\).
Connectedness supplies neighbors
\[
  \alpha-\gamma\in\mathcal G_u(H_T),
  \qquad
  \gamma-\beta\in\mathcal G_r(H_T).
  \tag{13}
\]
The neighbors may coincide; no simple length-two path is required. Choose
real-symmetric local probes \(A_u,B_r\) witnessing `(13)`.

For two new-site layers \(a\ne b\), perturb by
\[
  W_{ab}
  =
  A_u\otimes
  (|a\rangle\langle b|+|b\rangle\langle a|).
  \tag{14}
\]
The first derivative at zero coupling of the physical matrix element
between \((\alpha,a)\) and \((\beta,b)\) of \(B_r\otimes I\) is, apart from
the two nonzero adjugate normalizations,
\[
\begin{aligned}
R_{r,ab}(z)
={}&
\sum_\delta
\frac{
  (A_u)_{\alpha\delta}(B_r)_{\delta\beta}
}{
  z+E_\alpha-E_\delta
}\\
&+
\sum_\delta
\frac{
  (B_r)_{\alpha\delta}(A_u)_{\delta\beta}
}{
  -z+E_\beta-E_\delta
},
\qquad z=s_a-s_b.
\tag{15}
\end{aligned}
\]
All matrices and eigenbranches are real on the real coupling line, so the
bilinear adjugate derivative is exactly the physical sesquilinear bra--ket
derivative.

The selected \(\delta=\gamma\) term in the first sum has nonzero residue at
\[
  z=E_\gamma-E_\alpha.
  \tag{16}
\]
No other first-sum term shares this pole by simple spectrum. No second-sum
term shares it: equality with a pole \(E_\beta-E_\delta\) would give
\[
  E_\gamma-E_\alpha=E_\beta-E_\delta.
\]
Maximal projective rank makes nonzero oriented gaps injective. The only
possible identical ordered transition would force
\(\gamma=\beta\), contradicting `(13)`; the zero-gap case would force
\(\gamma=\alpha\), also contradicting `(13)`.

Thus \(R_{r,ab}\) is a nonzero rational function. It is nonzero for all but
finitely many real \(z\).

At zero coupling, each new layer contains the old connected non-bipartite
graph \(\mathcal G_r(H_T)\). Choose shifts avoiding, simultaneously, the
finite product-collision and response-zero sets for every old \(r\) and
every layer pair \((0,b)\). Each old layer graph persists under a small
perturbation, and one generated cross-layer edge from layer \(0\) to every
other layer connects them. The old odd cycle persists. Hence every old
vertex remains good.

### 4. The new leaf becomes good

Apply the endpoint-extension construction at \(u\).

- If \(q_v\ge3\), the real-symmetric local algebra on \(v\) gives a complete
  \(K_{q_v}\) inside each fixed-old-state block, including a triangle.
  Cross-block transitions generated along a spanning tree of
  \(\mathcal G_u(H_T)\) connect all blocks.
- If \(q_v=2\), persistent vertical exchanges plus the generated cross-block
  and same-layer transitions form a triangle for every selected old tree
  edge and connect both layers.

Each required transition is a nonzero real-analytic function of the finite
real edge-coefficient vector. The complement of its zero set is dense in
every small ball. Finitely many old-vertex and new-leaf requirements
therefore hold simultaneously for one arbitrarily small real-symmetric edge
perturbation. The extended tree has an all-vertex-good witness.

### 5. Coupled tree induction gives maximal rank

Induct simultaneously on every finite heterogeneous tree:

1. maximally projective real-symmetric local Hamiltonians form a dense,
   full-measure \(G_\delta\);
2. all-vertex-good simple real-symmetric Hamiltonians form a nonempty open
   set.

The two-site base was proved above. Remove a leaf \(v\) with parent \(u\).
By induction, the dense maximal-rank set on \(T-v\) intersects its nonempty
open all-vertex-good set. Choose \(H_{T-v}\) in the intersection.

Sections 3--4 give an all-vertex-good witness on \(T\).

For maximal rank on \(T\), suppose a labelled analytic eigenbranch relation
were universal near the product extension `(12)`. Vary one real-symmetric
exchange coupling between two new layers. The exact second-order eigenvalue
response is a simple-pole packet indexed by oriented edges of
\(\mathcal G_u(H_{T-v})\). Maximal old rank makes the nonzero ordered poles
distinct. Residues force equality of relation coefficients along
\[
  \mathcal G_u(H_{T-v})\times K_{q_v}.
  \tag{17}
\]
The categorical product is connected: the first graph is connected and
non-bipartite, so it has walks of both parities between any vertices; match
one parity and length to a walk in \(K_{q_v}\). Therefore every coefficient
is equal, leaving only the trace relation.

For each nonconstant balanced rational coefficient vector, symmetrize its
labelled eigenvalue linear form over all permutations. The resulting
symmetric relation polynomial is not identically zero by the residue
argument. It is a polynomial in the real local Hamiltonian parameters
through the characteristic coefficients. Its zero set is closed, null and
nowhere dense. The discriminant has the same properties. Removing the
discriminant and the countable union of rational-relation zero sets proves
statement 1 on \(T\).

This completes the coupled induction.

### 6. Arbitrary connected graphs

Every connected \(G\) contains a spanning tree \(T\). The real-symmetric
tree-local parameter space is a linear subspace of the \(G\)-local space.
Every discriminant or relation polynomial already nonzero on the tree
subspace remains nonzero on the larger graph space. Hence connected
arbitrary-graph Hamiltonians generically have
\[
  \tau=D-1.
\]

### 7. Disconnected upper bound

Write the component Hamiltonians as \(H_C\). Every total eigenvalue is
\[
  E_x=\sum_C E_C(x_C).
\]
Fix component reference labels \(x_C^0\). Every total relative energy
decomposes as
\[
  E_x-E_{x^0}
  =
  \sum_C\bigl(E_C(x_C)-E_C(x_C^0)\bigr).
\]
Conversely, every component gap is a total gap obtained by changing only
one component coordinate. Therefore the total rational gap module is exactly
the sum of the component gap modules:
\[
  M(H)=\sum_C M(H_C).
  \tag{18}
\]
Consequently
\[
  \tau(H)\le\sum_C(D_C-1).
  \tag{19}
\]

### 8. Disconnected sharpness

Choose a maximally projective real-symmetric local Hamiltonian \(K_C\) on
each connected component. Scale it by a nonzero real \(t_C\).

Choose the scales recursively. If
\[
  W=\sum_{C<k}t_CM(K_C),
\]
then a nontrivial intersection
\[
  t_kM(K_k)\cap W\ne\{0\}
\]
forces
\[
  t_k=w/v
\]
for some \(0\ne v\in M(K_k)\) and \(w\in W\). Both rational modules are
countable, so there are only countably many forbidden real scales. Choose
\(t_k\) outside them. The scaled component modules form a direct sum, and
`(18)` attains `(19)`.

This one witness makes every nonmaximal global relation polynomial
nonzero. The same discriminant and countable zero-set argument proves dense
full-measure \(G_\delta\) sharpness and completes `(2)`.

### 9. Simultaneous subsystem atlas

There are finitely many \(S\subseteq V\). For each \(S\), the inverse image
under coefficient restriction of the good set for \(G[S]\) is dense
\(G_\delta\) and full measure in the full coefficient space: its complement
is a finite-dimensional null algebraic union times unrestricted remaining
coordinates. Their finite intersection is again dense, full measure and
\(G_\delta\). Equations `(5)`--`(8)` follow by evaluating one- and two-vertex
induced graphs.

### 10. Recurrence

On a connected maximally projective spectrum, the \(D-1\) relative
frequencies are rationally independent. Kronecker--Weyl equidistribution
makes the phase orbit Haar-equidistributed on \(\mathbb T^{D-1}\).
Operator-norm distance at most \(\varepsilon\) modulo global phase requires
every relative circle phase to lie in the arc
\[
  |\theta|\le2\arcsin(\varepsilon/2).
\]
The normalized arc length is
\[
  2\arcsin(\varepsilon/2)/\pi.
\]
Product Haar measure gives `(9)`. A positive exact return would put every
relative frequency in one reciprocal-time lattice, contradicting rational
independence.

## Infinite-network completion

Let \(G_\infty\) be any countably infinite locally finite connected graph
with \(q_v\ge2\), and fix a connected finite exhaustion \(V_n\).
Parameterize all real local coefficients by a countable product of
finite-dimensional Euclidean spaces.

For each \(n\), the inverse image of the finite-volume good set is dense
\(G_\delta\). Their countable intersection is residual in the product
topology. Under every product law whose finite-dimensional marginals are
absolutely continuous with respect to Lebesgue measure, each finite-volume
bad cylinder has probability zero; their countable union has probability
zero.

Therefore, residually and almost surely,
\[
  \tau(H_{V_n})=\prod_{v\in V_n}q_v-1
  \longrightarrow\infty.
  \tag{20}
\]
No fixed finite-dimensional compact temporal carrier contains all
finite-volume completed dynamics. This is an exhaustion statement, not an
assertion of an infinite-volume trace, discrete spectrum or global
recurrence time.

## Current formal evidence

Already unconditional in Lean:

1. maximal projective rank makes nonzero ordered gaps injective:
   `maximallyProjectiveEnergy_orientedGap_injective`;
2. selected two-step poles cannot meet the opposite channel:
   `maximallyProjectiveEnergy_twoStep_crossPole_ne`;
3. one unique nonzero partial-fraction residue makes the cleared packet
   nonzero:
   `distinctNodePacketNumerator_ne_zero_of_unique_node`;
4. the two-step response has the exact two-sum form `(15)`:
   `twoStepEndpointPacketResponse_eq`;
5. one two-step channel prevents all cancellation:
   `twoStepEndpointPacketNumerator_ne_zero`;
6. a collision-free real shift with nonzero response exists:
   `exists_natCast_twoStepEndpointPacketResponse_ne_zero`;
7. real characteristic data give real canonical adjugate columns:
   `star_affineEigenbranchAdjugateColumn_eq`;
8. on that slice the bilinear response equals the physical bra--ket:
   `affineEigenbranchSesquilinearMatrixProbe_eq_bilinear_of_left_real`.

Direct checks passed:

```text
lake env lean GaloisForLFunctions/HTGeometry/ReplicaCollisionExtremality.lean
lake env lean GaloisForLFunctions/HTGeometry/LocalSpectralExtensionRelationRigidity.lean
lake env lean GaloisForLFunctions/HTGeometry/AffineEigenbranchSecondOrderLaw.lean
lake env lean GaloisForLFunctions/HTGeometry/AffineEigenbranchDiagonalProbeLaw.lean
lake env lean GaloisForLFunctions/HTGeometry/AllVertexEndpointResponse.lean
```

Still required before stage 3:

1. exact layered eigenbranch derivative-to-packet theorem including nonzero
   adjugate normalization factors;
2. real-line nonzero derivative implies a nonzero physical transition in
   every sufficiently small coefficient ball;
3. finite simultaneous analytic-avoidance theorem;
4. all-vertex-good graph induction;
5. heterogeneous relation-erasure capstone;
6. spanning-tree lift;
7. disconnected module equality and rational-transverse scaling;
8. simultaneous subsystem and infinite product capstones.
