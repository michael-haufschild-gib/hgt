# Disconnected local spectra have only factorization-forced generic relations

- **ID:** `disconnected-local-spectral-factorization-genericity`
- **Stage:** 2-fully-proven
- **Type:** DEPENDENCY-CLOSED PAPER PROOF / DISCONNECTED LOCAL HAMILTONIANS /
  PROJECTIVE GAP MODULES
- **Stage:** 3-formalized
- **Formalized companion:** `./disconnected-local-spectral-factorization-genericity-formalized.md`
- **Date:** 2026-07-30
- **Status:** `[PAPER-PROVED] [LEAN-PROVED] [SPECIALIST AUDIT OPEN]`
  `[NOVELTY NOT CLAIMED SEPARATELY]`
- **Parent:** `arbitrary-graph-quantum-temporal-curvature-law.md`

## Theorem

Let a finite tensor-factor quantum system have disconnected interaction
components \(C_1,\ldots,C_c\). Write
\[
 \mathcal H=\bigotimes_{r=1}^{c}\mathcal H_{C_r},
 \qquad D_r=\dim\mathcal H_{C_r},
\]
and assume that on each component \(C_r\), a dense full-Lebesgue-measure
\(G_\delta\) set of allowed component Hamiltonians has simple spectrum and
maximal projective rational rank \(D_r-1\).

Let
\[
 \mathcal L=\bigoplus_{r=1}^{c}\mathcal L_{C_r}
\]
be the disconnected local Hamiltonian parameter space, with the physical
Hamiltonian
\[
 H=\sum_{r=1}^{c}
 I\otimes\cdots\otimes H_r\otimes\cdots\otimes I.
\]
Then a dense full-Lebesgue-measure \(G_\delta\) subset of \(\mathcal L\)
has simple total spectrum and
\[
 \boxed{
 \dim_{\mathbb Q}M(H)=\sum_{r=1}^{c}(D_r-1),
 }                                                       \tag{1}
\]
where \(M(H)\) is the rational vector space spanned by all total energy
gaps.

Equivalently, generically:

1. every component gap module is maximally projective;
2. the component gap modules are mutually rationally transverse;
3. every rational relation among total energies is forced by the additive
   component factorization.

## Proof

### 1. Universal upper bound

Let \(E_{r,j}\), \(1\le j\le D_r\), be the component eigenvalues. Total
eigenvalues are indexed by
\(x=(x_1,\ldots,x_c)\) and equal
\[
 E_x=\sum_{r=1}^{c}E_{r,x_r}.                          \tag{2}
\]
Fix a reference label \(x^0\). Every total gap is
\[
 E_x-E_{x^0}
 =
 \sum_{r=1}^{c}
 \bigl(E_{r,x_r}-E_{r,x_r^0}\bigr).                   \tag{3}
\]
Conversely, every component gap is a total gap obtained by changing only
one coordinate of \(x^0\). Therefore
\[
 M(H)=\sum_{r=1}^{c}M(H_r)                            \tag{4}
\]
as rational subspaces of \(\mathbb R\), and
\[
 \dim_{\mathbb Q}M(H)
 \le\sum_{r=1}^{c}(D_r-1).                            \tag{5}
\]

### 2. One mutually transverse witness

Choose one simple maximally projective allowed Hamiltonian \(K_r\) on each
component. Its finite-dimensional rational gap module \(M(K_r)\subset
\mathbb R\) is countable.

Scale the components recursively. Suppose
\[
 W_{r-1}=\sum_{s<r}t_sM(K_s)
\]
is already a direct sum. A nonzero intersection
\[
 t_rM(K_r)\cap W_{r-1}\ne\{0\}
\]
would give
\[
 t_r=\frac{w}{v}
\]
for some \(0\ne v\in M(K_r)\) and \(w\in W_{r-1}\). There are only
countably many such ratios. Choose a nonzero real \(t_r\) outside them.
Then
\[
 \sum_{r=1}^{c}t_rM(K_r)
\]
is a direct sum and has dimension \(\sum_r(D_r-1)\). The corresponding
total spectrum is simple: equality of two total energies gives a zero sum
of component gaps, transversality makes every component gap zero, and
component simplicity makes every label equal.

This supplies one allowed witness attaining `(5)`.

### 3. Componentwise symmetric relation polynomials

The witness alone is not yet a genericity proof, because disconnected
spectra possess unavoidable rectangular additive relations. We isolate
only relations that would reduce the rank below `(5)`.

For every nonzero rational coefficient family
\[
 q=(q_{r,j})_{\substack{1\le r\le c\\2\le j\le D_r}}
 \in\mathbb Q^{\sum_r(D_r-1)},
\]
make it balanced inside each component by defining
\[
 \widetilde q_{r,1}=-\sum_{j=2}^{D_r}q_{r,j},
 \qquad
 \widetilde q_{r,j}=q_{r,j}\quad(j\ge2).              \tag{6}
\]
Define
\[
 \mathscr P_q((z_{r,j}))
 =
 \prod_{(\pi_1,\ldots,\pi_c)\in\prod_rS_{D_r}}
 \left(
   \sum_{r=1}^{c}\sum_{j=1}^{D_r}
   \widetilde q_{r,j}z_{r,\pi_r(j)}
 \right).                                             \tag{7}
\]

This polynomial is symmetric separately in the eigenvalues of each
component. By the fundamental theorem of symmetric polynomials, it is a
polynomial in the characteristic coefficients of the component matrices,
hence a real polynomial in the disconnected local Hamiltonian parameters.

It is not the zero polynomial. Evaluate `(7)` at the scaled transverse
witness \((t_rK_r)_r\). For every tuple of permutations, the corresponding
factor is a sum of balanced component energy combinations. If it vanished,
mutual transversality would make each component combination vanish.
Maximal projective rank of \(K_r\) would then make every permuted balanced
coefficient vector zero. Since permutations are bijective, this would force
all \(\widetilde q_{r,j}\), and hence \(q\), to be zero, a contradiction.
Thus every factor and their finite product are nonzero at the witness.

If the canonical component gaps obey
\[
 \sum_{r=1}^{c}\sum_{j=2}^{D_r}
 q_{r,j}(E_{r,j}-E_{r,1})=0,                          \tag{8}
\]
then the identity-permutation factor in `(7)` vanishes. The bad set for
this prescribed nonzero \(q\) therefore lies in the zero set of one
nonzero real polynomial. It is null and nowhere dense.

There are countably many nonzero rational \(q\). Removing the union of
their polynomial zero sets leaves a dense full-measure \(G_\delta\) on
which the \(\sum_r(D_r-1)\) canonical component gaps are rationally
independent. Together with `(5)`, this proves `(1)`.

Finally, the total discriminant is not the zero polynomial because it is
nonzero at the transverse witness. Removing its zero set gives generic
total simplicity. \(\square\)

## Exact representation lesson

The correct disconnected genericity object is not “absence of every
rational relation.” Additive component rectangles force many relations.
The correct invariant is:
\[
 \text{component gap modules are maximal internally and transverse
 externally}.                                         \tag{9}
\]
Componentwise, rather than global, symmetrization separates those forced
relations from genuine excess resonance.

## Hostile audit

1. **Does scaling leave the allowed local space?** No. Each component
   parameter space is real linear, so \(t_rK_r\in\mathcal L_{C_r}\).
2. **Can the forbidden scale set be uncountable?** No. Both rational gap
   modules are finite-dimensional over \(\mathbb Q\), hence countable.
3. **Can a permuted factor in `(7)` vanish at the witness despite canonical
   gap independence?** No. A permutation preserves balance within each
   component; transversality separates components and maximal projective
   rank kills each balanced coefficient vector.
4. **Does separate symmetry suffice for polynomiality in matrix entries?**
   Yes. Apply the fundamental theorem of symmetric polynomials independently
   to each finite component eigenvalue block, then use characteristic
   coefficients.
5. **Are the unavoidable rectangular relations incorrectly removed?** No.
   The tested coordinates are one canonical basis of component gaps. Their
   independence is equivalent to maximal direct-sum dimension; no claim says
   all \(D_1\cdots D_c-1\) total gaps are independent.
6. **Does rank maximality imply total simplicity?** Yes, but the proof also
   removes the total discriminant explicitly. The transverse witness shows
   that polynomial is nonzero.

No dependency gap remains in the paper argument. Formalization and external
specialist review remain open.

## Gates

- [x] exact upper bound
- [x] mutually transverse allowed witness
- [x] forced relations separated from excess relations
- [x] nonzero componentwise relation polynomial
- [x] countable null/meagre exceptional set
- [x] exact Lean formalization — `HTGeometry/DisconnectedProjectiveGapModuleLaw.lean`,
      `HypergraphComponentFactorization.lean`, `HypergraphProjectiveSpectralFactorization.lean`,
      `BlockSumSpectralGenericity.lean`
- [ ] independent specialist audit

