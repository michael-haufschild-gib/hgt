# Nearest-neighbour qudit chains have generically maximal projective spectral rank

- **ID:** `nearest-neighbor-qudit-projective-spectral-maximality`
- **Stage:** 2-fully-proven
- **Type:** PAPER-PROVED CORE / ALL LOCAL DIMENSIONS
- **Parent:** `nearest-neighbor-chain-projective-spectral-maximality.md`
- **Scientific status:** `[PAPER-PROVED] [SPECIALIST AUDIT OPEN]`
  `[PRIORITY PROVISIONALLY CLEARED]`

## Main theorem

Let \(n\geq2\), \(q\geq2\), \(D=q^n\), and let
\(\mathcal L_{P_n,q}\) be the real vector space of traceless Hermitian
Hamiltonians on \((\mathbb C^q)^{\otimes n}\) containing arbitrary one-site
and nearest-neighbour two-site terms on the open path \(P_n\).

For Lebesgue-almost every \(H\in\mathcal L_{P_n,q}\),
\[
 \boxed{
 \rho(H)
 =
 \dim_{\mathbb Q}\operatorname{span}_{\mathbb Q}
 \{E_j-E_1:2\leq j\leq D\}
 =D-1=q^n-1.
 }                                                     \tag{1}
\]
The spectrum is simple, and the maximal-rank set is a dense full-measure
\(G_\delta\).

Thus finite range, degree two and one spatial dimension do not bound temporal
rank by the number of sites or couplings. Every finite on-site dimension
generically attains the full projective Hilbert dimension.

## Endpoint transition graph

For a simple Hamiltonian \(H\) and endpoint \(u\), let
\(\mathcal G_u(H)\) have the energy eigenstates as vertices. Join
\(\alpha\neq\beta\) when
\[
 \langle\psi_\alpha,A_u\psi_\beta\rangle\neq0          \tag{2}
\]
for some Hermitian \(q\times q\) endpoint operator \(A_u\).
Let \(\mathcal U_{n,q,u}\) be the set on which this graph is connected and
non-bipartite.

## Lemma 1 — endpoint-observable qudit chains exist

For every \(n,q\geq2\), \(\mathcal U_{n,q,u}\) is nonempty and open.

### Openness

At simple spectrum, spectral projectors and all finitely many squared matrix
elements against a Hermitian basis of \(M_q(\mathbb C)\) vary continuously.
A fixed connected spanning subgraph and odd cycle therefore survive small
perturbations.

### Base \(n=2\)

Every Hermitian operator on two qudits is an allowed edge Hamiltonian.
Choose a generic orthonormal eigenbasis
\((\psi_\alpha)_{\alpha=1}^{q^2}\). For any fixed pair
\(\alpha\neq\beta\), all endpoint matrix elements vanish exactly when
\[
 \operatorname{Tr}_{\bar u}
 |\psi_\beta\rangle\langle\psi_\alpha|=0.             \tag{3}
\]
This is a proper real-analytic condition on the unitary eigenbasis: it fails,
for example, when the pair is sent to
\(|0,0\rangle,|1,0\rangle\). There are finitely many pairs. A finite union
of proper analytic zero sets cannot cover the unitary group. Hence one
eigenbasis makes `(3)` nonzero for every pair, so
\(\mathcal G_u(H)\) is complete. Assign distinct eigenvalues to obtain a
simple allowed \(H\).

### Endpoint extension for \(q=2\)

Assume \(H_A\) is a simple chain on \(n\) qubits whose transition graph at
the attachment endpoint is connected. Attach one qubit \(v\) and use the
product Hamiltonian
\[
 H_0
 =
 H_A\otimes I+a_0I\otimes|0\rangle\langle0|
              +a_1I\otimes|1\rangle\langle1|,          \tag{4a}
\]
where \(z=a_0-a_1\) makes all \(E_\alpha+a_r\) distinct. Put
\[
 X_v=|0\rangle\langle1|+|1\rangle\langle0|,
 \qquad
 Z_v=|0\rangle\langle0|-|1\rangle\langle1|.
\]
At zero edge coupling, \(X_v\) joins
\((\alpha,0)\) to \((\alpha,1)\) for every \(\alpha\).

Choose a spanning tree of the old endpoint graph. For each tree edge
\(\{\alpha,\beta\}\), choose a Hermitian endpoint operator
\(A_{\alpha\beta}\) with
\(\langle\psi_\alpha,A_{\alpha\beta}\psi_\beta\rangle\neq0\), and perturb the
new edge by a generic small linear combination of
\[
 A_{\alpha\beta}\otimes X_v.                           \tag{4b}
\]
For one coefficient \(x\), first-order eigenvector perturbation gives
\[
 \left.\frac d{dx}
 \langle\psi_{\alpha,1}(x),Z_v\psi_{\beta,0}(x)\rangle
 \right|_{x=0}
 =
 \frac{
  2\langle\psi_\alpha,A_{\alpha\beta}\psi_\beta\rangle
 }{
  E_\alpha-E_\beta-z
 },                                                     \tag{4c}
\]
up to the harmless sign imposed by the eigenvector convention. This is
nonzero because the product spectrum is simple. Thus every selected old tree
edge produces a cross-block endpoint transition.

The same perturbation also gives the same-layer derivative
\[
 \left.\frac d{dx}
 \langle\psi_{\alpha,0}(x),X_v\psi_{\beta,0}(x)\rangle
 \right|_{x=0}
 =
 \langle\psi_\alpha,A_{\alpha\beta}\psi_\beta\rangle
 \left(
  \frac1{E_\alpha-E_\beta+z}
  +\frac1{E_\beta-E_\alpha+z}
 \right)
 =
 \frac{
  2z\langle\psi_\alpha,A_{\alpha\beta}\psi_\beta\rangle
 }{
  z^2-(E_\alpha-E_\beta)^2
 }.                                                      \tag{4d}
\]
Again this is nonzero: simplicity excludes \(z=0\) and
\(z=\pm(E_\alpha-E_\beta)\).

Every required transition amplitude is analytic in the finitely many edge
coefficients and has a nonzero derivative in its selected coefficient.
Their failure loci are therefore proper analytic zero sets. Choose one
sufficiently small coefficient vector outside their finite union. The
vertical \(X_v\)-edges persist and the cross-block tree edges connect all
blocks. For any selected old tree edge, the three persistent/generated edges
\[
 (\alpha,1)-(\alpha,0)-(\beta,0)-(\alpha,1)
 \]
form a triangle. Simplicity also persists. Hence the new endpoint graph is
connected and non-bipartite.

### Endpoint extension for \(q\geq3\)

Assume \(H_A\) is a simple chain on \(n\) qudits whose transition graph at
the attachment endpoint is connected. Attach a \(q\)-level site \(v\) and
start from
\[
 H_0
 =
 H_A\otimes I+\sum_{r=0}^{q-1}a_rI\otimes|r\rangle\langle r|,
                                                               \tag{4}
\]
with the shifts chosen to make all product eigenvalues
\(E_\alpha+a_r\) distinct.

At zero coupling, the local algebra on \(v\) gives a complete \(K_q\) inside
each fixed-\(\alpha\) block. Since \(q\geq3\), every block already contains a
triangle.

Choose a spanning tree of \(\mathcal G_u(H_A)\). For each tree edge
\(\{\alpha,\beta\}\), choose a Hermitian endpoint operator \(A_{\alpha\beta}\)
with nonzero \(\alpha\beta\) matrix element. Fix \(r\neq s\) and perturb the
new edge by a generic small linear combination of
\[
 A_{\alpha\beta}\otimes
 (|r\rangle\langle s|+|s\rangle\langle r|).           \tag{5}
\]
For a local diagonal operator \(C_v\) with \(C_r\neq C_s\), first-order
eigenvector perturbation gives
\[
 \left.\frac{d}{dx}
 \langle\psi_{\alpha,r}(x),C_v\psi_{\beta,s}(x)\rangle
 \right|_{x=0}
 =
 \frac{
   \langle\psi_\alpha,A_{\alpha\beta}\psi_\beta\rangle
   (C_s-C_r)}
 {E_\alpha+a_r-E_\beta-a_s},                          \tag{6}
\]
up to the nonzero convention-dependent real factor from `(5)`.
Thus the required cross-block edge is not identically zero in the
perturbation coefficients. Finitely many proper analytic zero sets cannot
cover a small coefficient ball, so one perturbation makes every spanning-tree
cross edge nonzero simultaneously.

The new endpoint graph is connected, and its old within-block triangle
persists. Simplicity also persists. The two endpoint-extension arguments,
starting from the two-site base, prove nonemptiness inductively for every
\(q\geq2\). ∎

## Lemma 2 — one \(q\)-level endpoint extension destroys every relation

Assume the main theorem on \(P_n\) at local dimension \(q\). Choose
\[
 H_A\in
 \{\text{simple maximal-rank Hamiltonians}\}
 \cap\mathcal U_{n,q,n};
                                                               \tag{7}
\]
the intersection is nonempty because the first set is dense and the second
is nonempty open.

At the product point `(4)`, suppose constants \(c_{\alpha,r}\) give an
analytic eigenbranch identity
\[
 \sum_{\alpha,r}c_{\alpha,r}\lambda_{\alpha,r}\equiv0.
                                                               \tag{8}
\]
Fix \(r<s\), perturb the new edge in the allowed direction
\[
 V_A=A_n\otimes
 (|r\rangle\langle s|+|s\rangle\langle r|),           \tag{9}
\]
and vary \(z=a_r-a_s\). Second-order perturbation theory turns `(8)` into
\[
 \sum_{\alpha,\beta}
 \frac{
   (c_{\alpha,r}-c_{\beta,s})
   |\langle\psi_\alpha,A_n\psi_\beta\rangle|^2}
 {z+E_\alpha-E_\beta}
 =0.                                                  \tag{10}
\]
Maximal projective rank of \(H_A\) makes all nonzero ordered gaps distinct.
Residues at their poles give
\[
 c_{\alpha,r}=c_{\beta,s}                             \tag{11}
\]
for every edge \(\{\alpha,\beta\}\) of
\(\mathcal G_n(H_A)\), every \(r\neq s\), with both orientations supplied by
the two ordered gaps.

The equality graph in `(11)` is the categorical graph product
\[
 \mathcal G_n(H_A)\times K_q.                         \tag{12}
\]
Here is the required connectivity argument. In a connected graph containing
an odd cycle, any two vertices are joined by walks of both parities: take one
connecting walk, detour from it to the odd cycle and back, and traverse the
odd cycle once to flip parity. In the connected graph \(K_q\), any two
vertices have a walk, of some parity, and two-edge backtracks increase its
length without changing parity. Choose that parity for the walk in
\(\mathcal G_n(H_A)\), then add backtracks to the shorter walk until their
lengths agree. Moving along them simultaneously gives a path in the
categorical product. Thus `(12)` is connected for every \(q\geq2\).

All \(c_{\alpha,r}\) are therefore equal. The only branchwise relation is
trace. ∎

## Genericity

The symmetric relation-polynomial argument from the qubit theorem is
dimension-independent. For every nonconstant rational zero-sum coefficient
vector, multiply its eigenvalue linear form over all \(D!\) labelings. The
product is a nonzero symmetric polynomial in the eigenvalues and hence a
nonzero polynomial in local Hamiltonian parameters. Its zero set is null and
nowhere dense.

The discriminant is likewise a nonzero polynomial. Removing it and the
countable union of rational-relation zero sets leaves a dense full-measure
\(G_\delta\) of simple maximal-rank Hamiltonians.

The base \(n=2\) is
`complete-graph-local-projective-spectral-maximality.md`; Lemma 2 supplies
the induction. This proves `(1)`. ∎

## Corollaries

### Every qudit interaction graph containing a spanning path

If an interaction graph \(G\) contains a spanning path, then
\(\mathcal L_{P_n,q}\subseteq\mathcal L_{G,q}\). Every relation polynomial
nonzero on the path space is nonzero on the larger graph space. Hence almost
every \(H\in\mathcal L_{G,q}\) has rank \(q^n-1\).

### Exact recurrence density

For almost every path-local qudit Hamiltonian and
\[
 \Delta_H(t)=\max_{2\leq j\leq q^n}
 |e^{-it(E_j-E_1)}-1|,
\]
\[
 \operatorname{dens}\{\Delta_H<\varepsilon\}
 =
 \left(
 \frac{2\arcsin(\varepsilon/2)}{\pi}
 \right)^{q^n-1},
 \qquad 0<\varepsilon<2.                              \tag{13}
\]

### Exact entropy form of recurrence scarcity

Let
\[
 S_{\max}:=\log\dim\mathcal H=n\log q
 \quad\text{and}\quad
 c_\varepsilon:=
 \log\!\left(
 \frac{\pi}{2\arcsin(\varepsilon/2)}
 \right)>0.
\]
Taking the negative logarithm of `(13)` gives the identity
\[
 \boxed{
 -\log\operatorname{dens}\{\Delta_H<\varepsilon\}
 =
 (e^{S_{\max}}-1)c_\varepsilon .
 }                                                     \tag{14}
\]
Thus fixed-fidelity projective recurrences occupy an
\(\exp[-c_\varepsilon e^{S_{\max}}+c_\varepsilon]\) fraction of asymptotic
time. This is a double-exponential suppression as a function of maximum
entropy. It is an exact density statement, not by itself a theorem about a
first hitting time or a gravitational black hole.

### Every finite-order no-resonance condition

For every \(k\geq1\) and two \(k\)-tuples of energy indices,
\[
 \sum_{\ell=1}^kE_{\alpha_\ell}
 =
 \sum_{\ell=1}^kE_{\beta_\ell}                        \tag{15}
\]
if and only if the two tuples have the same multiplicity vector, equivalently
the same multiset of energy levels. Indeed, subtracting the two sides gives
an integer projective relation; maximal rank makes every coefficient zero.

Thus almost every static nearest-neighbour qudit chain satisfies all
finite-\(k\) no-resonance conditions simultaneously, not only simple
spectrum or nondegenerate pair gaps. Every finite product of balanced energy
phases has a nonzero infinite-time mean only under the corresponding trivial
index balance.

This is an exact-resonance statement. It gives no uniform lower bound on
near-resonance detunings.

### Commuting versus generic local interaction

If \(H_0\) is a sum of \(m=O(n)\) mutually commuting \(k\)-local terms, then
\[
 \rho(H_0)\leq m(q^k-1)=O(n).                         \tag{16}
\]
Every neighbourhood of \(H_0\) in the same path-local space contains a dense
full-measure set with rank \(q^n-1\).

## Hostile boundary

1. Arbitrary connected graphs without a spanning path remain open.
2. Translation-invariant low-parameter subfamilies remain open.
3. Exact rational rank is an infinite-time invariant; finite-horizon
   stability remains essential.
4. The endpoint-existence induction and categorical-product step require
   independent specialist review.
5. No manuscript claim is authorized before formal closure.

## Gates

- [x] every finite local dimension \(q\geq2\)
- [x] bounded-degree path locality
- [x] generic maximal projective rank
- [x] spanning-path graph corollary
- [x] recurrence-density corollary
- [x] simultaneous all-order no-resonance corollary
- [ ] specialist proof audit
- [ ] exact-object priority audit
- [ ] formalization
