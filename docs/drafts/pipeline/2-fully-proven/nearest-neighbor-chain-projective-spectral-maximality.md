# Nearest-neighbour chains have generically maximal projective spectral rank

- **ID:** `nearest-neighbor-chain-projective-spectral-maximality`
- **Stage:** 2-fully-proven
- **Type:** PAPER-PROVED CORE / BOUNDED-DEGREE LOCAL SPECTRAL ARITHMETIC
- **Source:** open core IV of
  `../1-in-progress/temporal-codimension-interaction-law.md`
- **Scientific status:** `[PAPER-PROVED] [PRIORITY OPEN]`
- **Physical class:** arbitrary one-site and nearest-neighbour two-site qubit
  Hamiltonians on a one-dimensional open chain

## Main theorem

Let \(P_n\) be the path graph on \(n\geq2\) qubits and let
\(\mathcal L_{P_n}\) be the real vector space of traceless Hermitian
Hamiltonians
\[
 H=\sum_{i=1}^{n}h_i+\sum_{i=1}^{n-1}h_{i,i+1},       \tag{1}
\]
where every \(h_i\) and \(h_{i,i+1}\) is arbitrary on its stated support.
Put \(D=2^n\).

For Lebesgue-almost every \(H\in\mathcal L_{P_n}\):

1. the spectrum is simple;
2. trace is the only rational affine relation among the eigenvalues;
3. the projective spectral rank is maximal:
   \[
   \boxed{
   \rho(H)
   =
   \dim_{\mathbb Q}\operatorname{span}_{\mathbb Q}
   \{E_j-E_1:2\leq j\leq D\}
   =D-1=2^n-1.
   }                                                     \tag{2}
   \]

The maximal-rank set is a dense full-measure \(G_\delta\) subset of
\(\mathcal L_{P_n}\).

This is a bounded-degree, finite-range, time-independent local Hamiltonian
theorem. No random-matrix ensemble, long-range interaction or thermodynamic
limit is used.

### Corollary — no unavoidable hidden resonances in two-body spectra

The path-local space is a linear subspace of the full two-body qubit
Hamiltonian space. Every rational-relation polynomial shown nonzero on the
path-local subspace is therefore nonzero on the full two-body space.
Consequently almost every unrestricted two-body qubit Hamiltonian also has
projective spectral rank \(2^n-1\).

This answers the projectively correct form of the question “Are there hidden
energy resonances in every two-body Hamiltonian?”: **no**. Trace supplies the
one unavoidable common-energy relation; no other resonance is forced, even
by nearest-neighbour locality.

### Corollary — every interaction graph with a spanning path

Let \(G\) be any interaction graph on \(n\) qubits containing a spanning
path. After relabelling vertices,
\[
 \mathcal L_{P_n}\subseteq\mathcal L_G.
\]
For each nontrivial rational projective relation, its symmetric
relation polynomial is nonzero on \(\mathcal L_{P_n}\), hence nonzero on
\(\mathcal L_G\). The same countable polynomial-zero-set argument gives
\[
 \rho(H)=2^n-1
\]
for Lebesgue-almost every \(H\in\mathcal L_G\).

This includes open chains, rings, complete graphs and every finite qubit
lattice graph for which a spanning path is specified. It does not include
every connected graph; stars and other non-Hamiltonian graphs require a
different witness theorem.

## Endpoint transition graph

Let \(H\) have simple eigenvectors
\(\psi_1,\ldots,\psi_D\), and let \(u\) be one endpoint site. Define the
endpoint transition graph \(\mathcal G_u(H)\) on
\(\{1,\ldots,D\}\) by joining \(\alpha\neq\beta\) when
\[
 \langle\psi_\alpha,A_u\psi_\beta\rangle\neq0          \tag{3}
\]
for at least one Hermitian one-qubit operator \(A_u\).

Let \(\mathcal U_{n,u}\subset\mathcal L_{P_n}\) be the set of
simple-spectrum Hamiltonians for which \(\mathcal G_u(H)\) is connected and
non-bipartite.

## Lemma 1 — endpoint-observable chains form a nonempty open set

For every \(n\geq2\), \(\mathcal U_{n,u}\) is open and nonempty.

### Proof of openness

At a simple-spectrum Hamiltonian, spectral projectors and the quantities
\[
 \sum_{\ell=0}^{3}
 |\langle\psi_\alpha,\sigma_\ell^{(u)}
 \psi_\beta\rangle|^2                                 \tag{4}
\]
are continuous, where
\(\sigma_0=I,\sigma_1=X,\sigma_2=Y,\sigma_3=Z\).
If one finite collection of nonzero edges contains a connected spanning
subgraph and an odd cycle, those same matrix elements remain nonzero in a
neighbourhood. Hence \(\mathcal U_{n,u}\) is open.

### Proof of nonemptiness

Use the number-preserving nearest-neighbour XY chain
\[
 H_{\mathrm F}
 =
 \sum_{i=1}^{n}d_i\,c_i^\dagger c_i
 +\sum_{i=1}^{n-1}t_i
 (c_i^\dagger c_{i+1}+c_{i+1}^\dagger c_i),           \tag{5}
\]
written as the standard nearest-neighbour qubit Hamiltonian under the
Jordan--Wigner transform. Choose distinct onsite values \(d_i\) with unique
subset sums, then choose all \(t_i\neq0\) sufficiently small that the
many-body spectrum remains simple.

The one-particle Jacobi matrix is irreducible. Every normalized
single-particle eigenmode therefore has nonzero amplitude \(v_k\) at endpoint
\(u=1\). In normal modes,
\[
 X_1=c_1+c_1^\dagger
 =\sum_kv_k(\gamma_k+\gamma_k^\dagger).                \tag{6}
\]
It connects every occupation set \(S\) to
\(S\triangle\{k\}\). These edges form the connected \(n\)-dimensional
hypercube.

Moreover,
\[
 Z_1=1-2c_1^\dagger c_1
 =
 1-2\sum_{k,\ell}v_kv_\ell\gamma_k^\dagger\gamma_\ell.
                                                               \tag{7}
\]
For \(k\neq\ell\), it connects the one-particle configurations
\(\{k\}\) and \(\{\ell\}\). Together with the two \(X_1\)-edges through the
vacuum, this gives the triangle
\[
 \varnothing\longleftrightarrow\{k\}
 \longleftrightarrow\{\ell\}
 \longleftrightarrow\varnothing.
\]
Thus the endpoint transition graph is connected and non-bipartite.
This proves nonemptiness. ∎

## Lemma 2 — maximal projective rank gives nondegenerate nonzero gaps

Let \(E_1,\ldots,E_D\) have maximal projective rational rank. If
\[
 E_\alpha-E_\beta=E_\gamma-E_\delta
 \quad\text{with }\alpha\neq\beta,\ \gamma\neq\delta, \tag{8}
\]
then \((\alpha,\beta)=(\gamma,\delta)\).

### Proof

Equation `(8)` is a rational affine relation with coefficient vector
\[
 e_\alpha-e_\beta-e_\gamma+e_\delta.
\]
Its coefficients sum to zero. Maximal projective rank makes this vector zero.
With both gaps nonzero, coefficient comparison forces
\(\alpha=\gamma\) and \(\beta=\delta\). ∎

## Lemma 3 — one endpoint extension destroys every affine relation

Assume the maximal-rank theorem holds on \(P_n\). Then there exists an
analytic chart in \(\mathcal L_{P_{n+1}}\) whose \(2^{n+1}\) eigenbranches
have no constant affine relation except trace.

### Proof

By the induction hypothesis, the maximal-rank subset of
\(\mathcal L_{P_n}\) is dense. Lemma 1 gives a nonempty open set
\(\mathcal U_{n,n}\) at the right endpoint. Choose
\[
 H_A\in
 \{\text{simple maximal-rank Hamiltonians}\}
 \cap\mathcal U_{n,n}.                                \tag{9}
\]
Write its eigenvalues and eigenvectors as
\((E_\alpha,\psi_\alpha)\), \(1\leq\alpha\leq 2^n\).

Attach one new qubit \(v=n+1\). At zero edge perturbation use
\[
 H_0(z)
 =
 H_A\otimes I
 +a_0 I\otimes|0\rangle\langle0|
 +a_1 I\otimes|1\rangle\langle1|,                    \tag{10}
\]
where \(z=a_0-a_1\) avoids the finitely many values
\(-E_\alpha+E_\beta\). After an irrelevant scalar centering, this belongs to
\(\mathcal L_{P_{n+1}}\) and has simple product eigenbranches
\[
 \lambda_{\alpha,r}(z,0)=E_\alpha+a_r,
 \qquad r\in\{0,1\}.                                  \tag{11}
\]

Suppose constants \(c_{\alpha,r}\) give an analytic identity
\[
 \sum_{\alpha,r}c_{\alpha,r}\lambda_{\alpha,r}
 \equiv0                                               \tag{12}
\]
on this chart.

For any Hermitian operator \(A\) on endpoint \(n\), perturb the new edge in
the allowed direction
\[
 V_A=A_n\otimes X_v.                                   \tag{13}
\]
Nondegenerate second-order perturbation theory and `(12)` give the rational
identity
\[
 \sum_{\alpha,\beta}
 \frac{
   (c_{\alpha,0}-c_{\beta,1})
   |\langle\psi_\alpha,A_n\psi_\beta\rangle|^2}
 {z+E_\alpha-E_\beta}
 =0.                                                   \tag{14}
\]

By Lemma 2, every nonzero ordered gap
\(E_\alpha-E_\beta\) is distinct. Taking the residue of `(14)` at
\[
 z=-(E_\alpha-E_\beta),\qquad\alpha\neq\beta,
\]
shows
\[
 c_{\alpha,0}=c_{\beta,1}                              \tag{15}
\]
whenever \(\{\alpha,\beta\}\) is an edge of
\(\mathcal G_n(H_A)\).

The equality graph in `(15)` is the bipartite double cover of
\(\mathcal G_n(H_A)\): its vertices are
\((\alpha,0)\) and \((\alpha,1)\), and every old edge crosses between the two
layers. The bipartite double cover of a connected graph is connected exactly
when the original graph is non-bipartite. By `(9)`, it is connected.
Therefore every \(c_{\alpha,r}\) has one common value. The only identity in
`(12)` is the centred trace relation. ∎

## Lemma 4 — branchwise independence implies generic independence

Let \(D=2^n\). For every nonconstant
\(q=(q_1,\ldots,q_D)\in\mathbb Q^D\) with
\(\sum_jq_j=0\), define
\[
 \mathscr F_q(z_1,\ldots,z_D)
 =
 \prod_{\pi\in S_D}
 \left(\sum_jq_jz_{\pi(j)}\right).                    \tag{16}
\]
This symmetric polynomial is a polynomial in the characteristic
coefficients and hence in the local Hamiltonian parameters.

On the chart supplied by Lemma 3, no factor in `(16)` is identically zero.
Their product is therefore not identically zero. Every ordered spectrum
satisfying the relation \(q\cdot E=0\) lies in the zero set of this nonzero
polynomial. That set is null and nowhere dense.

The discriminant is likewise a nonzero polynomial because the chart contains
a simple-spectrum point.

## Proof of the main theorem

For \(n=2\), the complete graph and path graph coincide.
`complete-graph-local-projective-spectral-maximality.md` supplies the base
case.

Assume the result for \(P_n\). Lemma 3 supplies a branchwise-independent
chart for \(P_{n+1}\); Lemma 4 turns it into a generic theorem. The
discriminant and the countably many rational-relation polynomials have null
nowhere-dense zero sets. Their complement is a dense full-measure
\(G_\delta\) on which the spectrum is simple and the projective rank is
\(2^{n+1}-1\). Induction proves the result for every \(n\geq2\). ∎

## Corollary 1 — exact recurrence rarity in a one-dimensional local system

For almost every \(H\in\mathcal L_{P_n}\), define
\[
 \Delta_H(t)
 =
 \max_{2\leq j\leq2^n}|e^{-it(E_j-E_1)}-1|.
\]
For every \(0<\varepsilon<2\),
\[
 \boxed{
 \operatorname{dens}\{t:\Delta_H(t)<\varepsilon\}
 =
 \left(
 \frac{2\arcsin(\varepsilon/2)}{\pi}
 \right)^{2^n-1}.
 }                                                     \tag{17}
\]
The reciprocal return fraction is doubly exponential in chain length at
fixed resolution.

## Corollary 2 — bounded-degree interaction-rank singularity

Every commuting nearest-neighbour qubit Hamiltonian expressible as
\(m=O(n)\) commuting two-site terms has
\[
 \rho(H)\leq3m=O(n).                                  \tag{18}
\]
Every neighbourhood of it in the same nearest-neighbour Hamiltonian space
contains a dense full-measure set with
\[
 \rho(H)=2^n-1.                                       \tag{19}
\]

Thus a finite-range interaction perturbation can change the completed
projective temporal dimension from linear to exponential without adding
sites or long-range couplings.

The finite-horizon stability theorem prevents an instantaneous
interpretation: a perturbation of norm \(\delta\) remains operationally close
to the unperturbed reporter orbit below the resolution-dependent scale
\(T\delta=O(\varepsilon)\).

## What is new if priority survives

The theorem would close the question left open by existing recurrence bounds:
it proves the arithmetic rank controlling generic global recurrence for a
physical, static, noncommuting, nearest-neighbour Hamiltonian family.

It also answers an explicit question posed in the autonomous two-body
reachability literature: whether hidden energy resonances are unavoidable in
every two-body Hamiltonian. The theorem proves more than a negative answer in
the unrestricted family: bounded-degree one-dimensional locality already
permits and generically realizes maximal projective independence.

It also supplies a rigorous mechanism for the exponential-versus-
double-exponential recurrence distinction:

```text
commuting/free additive spectrum:
  O(n) independent clocks;

generic nearest-neighbour interacting spectrum:
  2^n - 1 independent projective clocks.
```

The conclusion is stronger than generic simplicity or nondegenerate gaps.
It excludes every rational affine relation among all \(2^n\) eigenvalues
apart from trace.

## Hostile boundary

1. “Almost every” refers to Lebesgue measure on the finite-dimensional local
   coupling space; it does not say every noncommuting chain has maximal rank.
2. Integrable and free-fermion chains remain lower-rank exceptional families.
3. Equation `(17)` is an exact long-time density, not a fixed-Hamiltonian
   first-return estimate.
4. The physical crossover upper bound and metric-Diophantine exponent remain
   open.
5. Exact-object priority against generic local no-resonance and spin-chain
   spectral Galois literature remains open.
6. Extension from qubits to arbitrary \(q\), general connected graphs,
   and translation-invariant low-parameter families is not yet proved.
   Periodic boundaries and all other qubit graphs containing a spanning path
   are covered by the subspace corollary.

## Gates

- [x] dependency-closed paper proof
- [x] explicit bounded-degree witness class
- [x] generic simple spectrum
- [x] generic maximal rational projective rank
- [x] exact recurrence-density corollary
- [x] commuting/local rank comparison
- [~] primary-source collision audit
- [ ] specialist audit of endpoint-transition induction
- [x] fixed-Hamiltonian metric first-return exponent on paper
- [ ] finite-resolution upper crossover
- [ ] formalization only after novelty gate
