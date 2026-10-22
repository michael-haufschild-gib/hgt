# Linear-family affine spectral escape

- **ID:** `linear-family-affine-spectral-escape`
- **Stage:** 1-in-progress
- **Type:** theorem / recurrence nondegeneracy bridge
- **Date:** 2026-08-23

## Exact claim

Let \(P_1,\ldots,P_N\) be finite Hermitian matrices and
\(H(\theta)=\sum_a\theta_aP_a\). If this linear family escapes every nonzero balanced homogeneous
real spectral relation, then it escapes every prescribed affine level: for every nonzero
\(c\in\mathbb R^D\) with \(\sum_jc_j=0\), and every \(b\in\mathbb R\), some member has a simple
real spectrum \(E\) for which

\[
  \sum_j c_j E_{\sigma(j)}\ne b
\]

for every permutation \(\sigma\).

## Proof

Homogeneous escape supplies \(H(\theta)\), a simple real root packet \(E\), and nonzero numbers

\[
  A_\sigma=\sum_j c_jE_{\sigma(j)}
\]

for all finitely many permutations. Scale the same Hamiltonian and packet by a real number \(t\).
The forbidden equation is \(tA_\sigma=b\), so permutation \(\sigma\) excludes only
\(t=b/A_\sigma\). Also exclude \(t=0\). A finite subset cannot exhaust \(\mathbb R\), hence choose
\(t\) outside it. The scaled matrix still lies in the same linear family, \(tE\) remains simple,
the scaled values remain characteristic roots, and all affine relations miss \(b\).

## Significance for recurrence paper

The numbered nearest-neighbour Pauli chain already escapes every homogeneous balanced relation.
This bridge upgrades that exact same coefficient family to affine escape, closing the missing
same-object input for the full \(D-1\) stroboscopic first-return exponent. No separate path witness
or identification of existentially packaged chains is needed.

## Gates

- [x] exact dependency-closed paper proof
- [ ] targeted formalization
- [ ] targeted build, lint, and axiom audit

