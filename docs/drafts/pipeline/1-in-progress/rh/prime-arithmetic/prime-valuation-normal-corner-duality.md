# Prime-valuation normal-corner duality

- **ID:** `prime-valuation-normal-corner-duality`
- **Stage:** 1 — in progress
- **Type:** UNIVERSAL SOURCE-NORMAL LAW / RIEMANN-DIVISOR ARCHITECTURE
- **Scientific status:** `[NEW SYNTHESIS] [EXACT SPECTRAL CORE FORMALIZED] [PAPER AUDIT OPEN]`
- **Parents:**
  - `../2-fully-proven/needs-audit/xi-transverse-gamma-valuation-schur-translation.md`
  - `../2-fully-proven/prime-sieve-wold-gamma-bv-relative-character.md`
  - `../../../3-formalized/new_scientific_knowledge/prime-residue-valuation-interaction-superselection-law.md`
  - `../../../5-failed/source-normal-cone-divisor-conservation-law.md`

## Problem

The current paper resolves the integer source only by largest valuation depth
\[
M(n)=\max_p v_p(n).
\]
The Wold normal-jet theorem resolves only distinct-prime support
\[
\omega(n)=|\{p:p\mid n\}|.
\]
These are transverse filtrations. Treating either as a scalar marginal erases the incidence
geometry needed before divisor specialization.

## Candidate universal object

For a finite packet of distinct primes \(p_1,\ldots,p_k\), put \(q_j=p_j^{-1}\) and
\[
H_e(p_j)=\sqrt{q_j}(1-q_j)q_j^e,\qquad e\ge0.
\]
Rows are valuation depth; columns are prime-normal directions. The resulting depth--normal
incidence matrix is
\[
\mathcal V_{m,k}(p)=(H_e(p_j))_{0\le e<m,\ 1\le j\le k}.
\]

The integer-level bivariate cells are
\[
\mathcal A_{m,k}(s)
=\sum_{\substack{n\ge2\\M(n)=m\\\omega(n)=k}}n^{-s},
\qquad \Re s>1.
\]
Their row marginal is the positive largest-exponent shell; their normal boundary order
\(k-1\) is the exact support-cardinality selector.

## New theorem: exact depth--codimension duality

For every injective \(k\)-prime packet:

1. \(\mathcal V_{k,k}(p)\) is a weighted Vandermonde and is invertible.
2. For every \(m<k\), \(\mathcal V_{m,k}(p)\) is not injective.
3. Hence Wold normal codimension \(k\) is exactly the minimum valuation depth required to
   reconstruct arbitrary amplitudes on that normal packet.
4. The support stratum first appears in normal derivative order \(k-1\), giving the exact
   successor relation
   \[
   \text{normal order}+1=\text{minimal valuation tomography depth}.
   \]

This is stronger than independence of the filtrations: it identifies them as dual ranks.

## Reciprocal-prime spectral law

The vertical Gamma translation on a \(k\)-prime packet is the diagonal operator
\[
T_P=\operatorname{diag}(p^{-1})_{p\in P}.
\]
The valuation tower is its orbit from the depth-zero Gamma-normal vector.  For distinct primes,
\[
\mu_{T_P}(X)=\chi_{T_P}(X)=\prod_{p\in P}(X-p^{-1}),
\qquad \deg\mu_{T_P}=|P|.
\]
Consequently every nonzero polynomial recurrence annihilating the full packet has order at least
\(|P|\), and the displayed prime polynomial attains the bound.  The roots retain the prime
identities, not only packet cardinality.

This converts the rank statement into a dynamical arithmetic law:
\[
\boxed{
\text{Wold normal codimension}
=\text{Gamma-corona conormal rank}
=\text{prime recurrence order}
=\text{minimal valuation depth}.}
\]

## Gamma action

The actual normalized Gamma cross-coordinate is \(H_0\). Its Schur complement satisfies
\[
K(p,r)-H_0(p)H_0(r)=q_pq_rK(p,r),
\]
so Gamma elimination deletes the first depth row and translates the same incidence frame by one
valuation level. Thus Gamma acts vertically on the pre-divisor normal grid rather than on a
scalarized divisor statistic.

## Cofinal consequence

Prime support has unbounded rational character rank. Therefore:

- no fixed finite number of valuation rows reconstructs all prime-normal packets;
- no finite-dimensional phase carrier represents all Euler apertures;
- finite positivity and finite tomography cannot by themselves pass to the all-prime boundary.

The Wold boundary volume tends to zero while its reciprocal normal scale tends to infinity.
The two reflected irregular Gamma branches are jointly polynomially moderate on this exact
cofinal source scale iff \(\Re s=\tfrac12\). This locates the critical line at the completed
source-normal corner before a zero is selected.

## No-go shadows to audit

The theorem must explain, not merely list:

1. finite divisor-head/Euler-head/tail shadows admit a generic off-line orbit;
2. compact-open convergence and every holomorphic jet lose arbitrary \(8\pi\)-quantized charge
   at height infinity;
3. one critical clock and its Gram/Ward budgets are divisor-blind;
4. normalized measured indices erase finite or density-zero off-line charge;
5. Euler diagonal limits push every finite divisor packet to anti-causal infinity;
6. complete differential matroids and continuum isodivisorial gauges do not determine divisor
   orientation;
7. the fixed Möbius--Gamma/Xi source map is expansive, and scalar normal blow-up worsens its gain;
8. the unrenormalized critical Gamma-conormal boundary coordinate is not square-summable.

Provisional synthesis: each route applies scalarization, finite truncation, Hilbert completion, or
compact-open passage before retaining the full source-normal corner. The resulting quotient cannot
increase depth--codimension rank and cannot recover charge that lives at the cofinal boundary.

More sharply, the failed observations destroy one of three pieces:

1. **prime spectrum:** a fixed finite reporter cannot retain the unbounded minimal polynomial
   \(\prod_{p\in P}(X-p^{-1})\);
2. **axis pairing:** a scalar totalization or diagonal identifies distinct depth--codimension
   cells;
3. **cofinal class:** compact-open or ordinary Hilbert completion kills the finite-blind corona
   class or excludes its nonsummable critical coordinate.

Thus the candidate universal principle is not “use two variables.” It is:

> **Prime-normal information is conserved only before finite realization and completion.**
> The complete invariant is the paired pro-recurrence corner: reciprocal-prime spectrum
> horizontally, Gamma translation vertically, and the Wold/Gamma corona class at the cofinal
> boundary.

## Falsifiers

- A faithful fixed finite-depth observer on arbitrary finite prime packets.
- A support-\(k\) packet reconstructed from fewer than \(k\) scalar valuation moments without
  additional source coordinates.
- A cofinal source Hilbert vector retaining a nonzero scalar proportion of the raw critical
  Gamma boundary coordinate.
- A theorem showing that one scalar critical clock or Ward mass reconstructs the missing
  prime-normal vector.

## Current paper gate

Exact rectangular minimal rank, corona rank, reciprocal-prime minimal polynomial, Gamma orbit,
Schur translation, and cofinal critical-line selector are formalized.  Paper promotion now depends
on a hostile literature and significance audit: the theorem must be presented as a source-normal
recurrence law with the existing RH routes as information-losing projections, not as another
critical-line equivalence.
