# Complete-graph local projective spectral maximality

- **ID:** `complete-graph-local-projective-spectral-maximality`
- **Stage:** 2-fully-proven
- **Type:** PAPER-PROVED BRIDGE / GENERIC 2-LOCAL SPECTRAL ARITHMETIC
- **Source:** open core IV of
  `../1-in-progress/temporal-codimension-interaction-law.md`
- **Scientific status:** `[PAPER-PROVED] [PRIORITY OPEN]`
- **Scope boundary:** all-to-all two-local qudit Hamiltonians; not yet
  bounded-degree locality

## Theorem

Let \(n\geq2\), \(q\geq2\), \(D=q^n\), and let
\(\mathcal L_{K_n,q}\) be the real vector space of traceless Hermitian
Hamiltonians on \((\mathbb C^q)^{\otimes n}\) containing arbitrary one-site
and two-site terms on the complete graph.

For Lebesgue-almost every \(H\in\mathcal L_{K_n,q}\):

1. \(H\) has simple spectrum;
2. its ordered eigenvalues \(E_1<\cdots<E_D\) have no rational affine
   relation other than trace:
   \[
   \sum_{j=1}^{D}q_jE_j=0,\quad
   \sum_{j=1}^{D}q_j=0,\quad q_j\in\mathbb Q
   \quad\Longrightarrow\quad
   q_1=\cdots=q_D=0;
   \]
3. its projective spectral rank is maximal:
   \[
   \boxed{
   \dim_{\mathbb Q}\operatorname{span}_{\mathbb Q}
   \{E_j-E_1:2\leq j\leq D\}=D-1=q^n-1.
   }                                                     \tag{1}
   \]

The maximal-rank set is a dense full-measure \(G_\delta\) subset of
\(\mathcal L_{K_n,q}\). Consequently every complete-graph two-local
Hamiltonian, including every commuting one, is arbitrarily closely
approximated by two-local Hamiltonians with maximal projective spectral rank.

## Explicit witness family

Fix a local basis \(\{|r\rangle:0\leq r<q\}\). Let
\[
 P_i^r=|r\rangle\langle r|_i,\qquad
 X_i^{rr'}=|r\rangle\langle r'|_i+
            |r'\rangle\langle r|_i
 \quad(r<r').
\]
It suffices to use the real diagonal-interaction/transverse-transition
subfamily
\[
 \widetilde H(a,b,x)
 =
 \sum_{i,r}a_{i,r}P_i^r
 +\sum_{i<j}\sum_{r,u}b_{ij,r,u}P_i^rP_j^u
 +\sum_i\sum_{r<r'}x_{i,rr'}X_i^{rr'}.                \tag{2}
\]
Center it by
\[
 H=\widetilde H-\frac{\operatorname{Tr}\widetilde H}{D}I.
\]
This does not change any energy gap or zero-sum affine relation and places the
family inside \(\mathcal L_{K_n,q}\).

The diagonal point \(x=0\) has computational eigenvectors indexed by
\(s=(s_1,\ldots,s_n)\in\{0,\ldots,q-1\}^n\), with uncentred eigenvalues
\[
 d_s(a,b)
 =
 \sum_i a_{i,s_i}+\sum_{i<j}b_{ij,s_i,s_j}.           \tag{3}
\]
Outside finitely many affine hyperplanes in \((a,b)\), all \(d_s\) are
distinct. Fix such a point. Standard simple-eigenvalue perturbation theory
gives real-analytic eigenbranches
\[
 \lambda_s(a,b,x),\qquad
 \lambda_s(a,b,0)=d_s(a,b)-D^{-1}\sum_ud_u(a,b),      \tag{4}
\]
on a neighbourhood of that point.

## Lemma 1 — the only branchwise affine relation is trace

Suppose real constants \(c_s\) satisfy
\[
 \sum_s c_s\lambda_s(a,b,x)\equiv0                    \tag{5}
\]
as an analytic identity on one such simple diagonal chart. Then all \(c_s\)
are equal.

If additionally \(\sum_sc_s=0\), then every \(c_s=0\).

### Proof

Fix a site \(i\), two distinct local levels \(r<r'\), and a remote
configuration
\(\sigma=(s_j)_{j\neq i}\in\{0,\ldots,q-1\}^{n-1}\).
Since \(X_i^{rr'}\) connects \(|(r,\sigma)\rangle\) only to
\(|(r',\sigma)\rangle\), the nondegenerate second-derivative formula gives
\[
 \left.
 \frac{\partial^2\lambda_{(r,\sigma)}}
      {\partial x_{i,rr'}^2}
 \right|_{x=0}
 =
 \frac{2}{d_{(r,\sigma)}-d_{(r',\sigma)}},             \tag{6}
\]
with the negative reciprocal for the \(r'\)-branch and zero for every other
local level. Put
\[
 L_\sigma^{rr'}
 =
 d_{(r,\sigma)}-d_{(r',\sigma)}.                       \tag{7}
\]
Differentiate `(5)` twice in \(x_{i,rr'}\), set \(x=0\), and pair the two
levels:
\[
 \sum_{\sigma\in\{0,\ldots,q-1\}^{n-1}}
 \frac{c_{(r,\sigma)}-c_{(r',\sigma)}}{L_\sigma^{rr'}}
 =0.                                                   \tag{9}
\]

The reciprocal affine forms \(1/L_\sigma^{rr'}\) are linearly independent
over \(\mathbb R\). Indeed, every form has coefficient \(+1\) on \(a_{i,r}\)
and \(-1\) on \(a_{i,r'}\), so proportionality would force proportionality
constant one. Distinct remote configurations differ at some site \(j\);
the coefficient vectors on the independent two-site parameter block
\(b_{\{i,j\},\cdot,\cdot}\) then differ, so the forms are distinct. For any
fixed \(\sigma_0\), the hyperplane
\(L_{\sigma_0}^{rr'}=0\) contains a point lying on no other
\(L_\sigma^{rr'}=0\). Multiply a proposed linear relation by
\(L_{\sigma_0}^{rr'}\) and restrict to such a point. Only the
\(\sigma_0\)-coefficient remains, so it is zero.

Equation `(9)` therefore gives
\[
 c_{(r,\sigma)}=c_{(r',\sigma)}
 \qquad\text{for every }\sigma\text{ and }r<r'.       \tag{10}
\]
This holds for every site \(i\). The \(q\)-ary Hamming graph of
configurations is connected by single-site level changes, so `(10)` makes
\(c_s\) constant on all \(q^n\) configurations. The zero-sum conclusion is
immediate. ∎

## Lemma 2 — every prescribed rational relation is algebraically exceptional

Fix a nonzero vector \(q=(q_1,\ldots,q_D)\in\mathbb Q^D\) with
\(\sum_jq_j=0\). For an unordered eigenvalue tuple
\((z_1,\ldots,z_D)\), define
\[
 \mathscr F_q(z_1,\ldots,z_D)
 =
 \prod_{\pi\in S_D}
 \left(\sum_{j=1}^{D}q_jz_{\pi(j)}\right).             \tag{11}
\]

This is symmetric in the \(z_j\). Hence the fundamental theorem of symmetric
polynomials writes it as a polynomial with rational coefficients in the
elementary symmetric functions. Applied to the eigenvalues of a matrix,
\(\mathscr F_q\) is therefore a polynomial in the coefficients of the
characteristic polynomial, and hence a polynomial in the real Hamiltonian
parameters.

It is not the zero polynomial on the witness family `(2)`. On the analytic
chart `(4)`, every factor in `(11)` is a branchwise affine relation with a
permutation of the nonconstant zero-sum vector \(q\). Lemma 1 says no factor
is identically zero. The ring of real-analytic germs on a connected chart is
an integral domain, so their finite product is not identically zero.

If the ordered eigenvalues of any simple \(H\) obey
\[
 \sum_jq_jE_j(H)=0,
\]
then one factor in `(11)` vanishes. Thus all such \(H\) lie in the zero set of
one nonzero real polynomial on \(\mathcal L_{K_n,q}\). That zero set has
Lebesgue measure zero and empty interior. ∎

## Proof of the theorem

The discriminant of the characteristic polynomial is a polynomial in the
Hamiltonian parameters. It is nonzero on every diagonal point `(3)` with
distinct \(d_s\), so the repeated-spectrum set is null and nowhere dense.

There are countably many nonzero rational zero-sum vectors
\(q\in\mathbb Q^D\). Lemma 2 places the exceptional set for each one inside
a null nowhere-dense polynomial zero set. Their countable union is null and
meagre. Outside that union and the discriminant, no rational projective
relation exists, proving `(1)`.

The complement is a countable intersection of open dense sets, hence a dense
\(G_\delta\), and it has full Lebesgue measure. ∎

## Corollary — exact global recurrence density

For every Hamiltonian in the full-measure set, define
\[
 \Delta_H(t)
 =
 \max_{2\leq j\leq D}
 |e^{-it(E_j-E_1)}-1|.
\]
Kronecker--Weyl equidistribution on the full projective torus gives, for
\(0<\varepsilon<2\),
\[
 \boxed{
 \lim_{T\to\infty}\frac1{2T}
 \left|\{t\in[-T,T]:\Delta_H(t)<\varepsilon\}\right|
 =
 \left(
 \frac{2\arcsin(\varepsilon/2)}{\pi}
 \right)^{q^n-1}.
 }                                                     \tag{12}
\]
Thus the inverse time fraction is exponential in \(q^n\), or doubly
exponential in \(n\), at every fixed resolution.

Equation `(12)` is an exact density statement. It is not yet a first-return
time theorem for a fixed local Hamiltonian.

## Corollary — singular asymptotic interaction effect

If \(H_0\in\mathcal L_{K_n,q}\) is a sum of \(m\) commuting terms, each
supported on at most \(k\) sites, then
\[
 \rho(H_0)\leq m(q^k-1).                              \tag{13}
\]
Every neighbourhood of \(H_0\) contains \(H\) with
\(\rho(H)=q^n-1\).

The finite-horizon stability theorem in
`finite-horizon-observer-temporal-profile-stability.md` prevents an
instantaneous physical interpretation: if
\(\|H-H_0\|=\delta\), fixed-resolution reporter histories remain close for
times below order \(1/\delta\). The rank jump is the completed long-time
limit of a finite-time crossover.

## Why the proof needs the complete graph

For a general interaction graph, `(7)` depends only on the neighbour
configuration:
\[
 L_\sigma^{rr'}
 =
 a_{i,r}-a_{i,r'}
 +\sum_{j\in N(i)}
 \bigl(b_{ij,r,\sigma_j}-b_{ij,r',\sigma_j}\bigr).
\]
It no longer distinguishes configurations outside the neighbour set.
Equation `(9)` then forces only sums of coefficients over remote
configurations to vanish. Second-order poles alone do not prove full
independence.

Higher mixed perturbation coefficients along connected walks may propagate
the separation through a bounded-degree graph, but that theorem remains
open. The present proof must not be advertised as nearest-neighbour or
finite-range locality.

## Hostile novelty boundary

1. Generic symmetric matrices are known to have full spectral Galois
   behaviour. The result here concerns a highly constrained, polynomial-size
   two-local subspace and uses an explicit physical witness family for every
   \(q\geq2\).
2. Exact priority remains open. A source proving generic rational
   independence for the same complete-graph diagonal-interaction/transverse-
   transition family would absorb the core.
3. All-to-all coupling weakens direct condensed-matter relevance.
4. Full-measure rational independence is not experimentally certifiable at
   finite precision. The finite-horizon profile is required for physical
   interpretation.
5. The Nature anchor still requires bounded-degree generic maximality and
   an upper crossover law.

## Gates

- [x] dependency-closed paper proof
- [x] simple-spectrum exceptional set isolated
- [x] every rational relation placed in a polynomial null set
- [x] density and Baire genericity proved
- [x] exact recurrence-density corollary
- [ ] exact-object primary-source audit
- [ ] bounded-degree extension
- [ ] metric first-return exponent on local spectral family
- [ ] formalization only after master novelty gate
