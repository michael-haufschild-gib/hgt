# Toeplitz recurrent boundary, open defect history, and index law

- **ID:** ULF-TOEPLITZ-1
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** polarized directed-history survivor
- **Statement:** The unilateral shift has recurrent finite boundary observations and constant initial Gram while its defect rank and Toeplitz boundary index grow without bound.
- **Status:** [PAPER-PROVED] [ROUTE-INDEPENDENT] [CLASSICAL TOEPLITZ PARENTS] [FIELD CALIBRATION] [NO LEAN]

## 1. Setup

Let \(H=\ell^2(\mathbb N_0)\) with basis \((e_j)_{j\ge0}\), and let \(S\) be the unilateral
shift

\[
Se_j=e_{j+1}.
\tag{1}
\]

Let \(\mathcal T=C^*(S)\) be the Toeplitz algebra, \(\mathcal K=\mathcal K(H)\), and

\[
0\longrightarrow\mathcal K\longrightarrow\mathcal T
\xrightarrow{\sigma}C(S^1)\longrightarrow0
\tag{2}
\]

the Toeplitz extension, normalized by \(\sigma(S)=z\), the coordinate unitary on \(S^1\).
For \(m\ge2\), put \(\zeta_m=e^{2\pi i/m}\) and define the finite boundary observer

\[
O_m(n)=\operatorname{ev}_{\zeta_m}(\sigma(S^n))=\zeta_m^n.
\tag{3}
\]

## 2. Theorem

For every \(n\ge0\):

1. \(S^{*n}S^n=1\);
2. \(D_n:=1-S^nS^{*n}\) is the orthogonal projection onto
   \(\operatorname{span}\{e_0,\ldots,e_{n-1}\}\), hence
   \(\operatorname{rank}D_n=\operatorname{Tr}D_n=n\);
3. the defect satisfies the exact cocycle law

   \[
   D_{n+r}=D_n+S^nD_rS^{*n},
   \qquad
   D_n\perp S^nD_rS^{*n};
   \tag{4}
   \]

4. \(O_m(n+m)=O_m(n)\), so every finite boundary observer is periodic;
5. along the return sequence \(n=km\),

   \[
   O_m(km)=1,
   \qquad
   \operatorname{Tr}D_{km}=km\longrightarrow\infty;
   \tag{5}
   \]

6. \(S^n\) is Fredholm with

   \[
   \operatorname{ind}(S^n)=-n;
   \tag{6}
   \]

7. with the standard connecting-map convention,

   \[
   \partial[z^n]=-[D_n]\in K_0(\mathcal K)\cong\mathbb Z;
   \tag{7}
   \]

8. if \(n>0\), the boundary unitary \(z^n\) has no unitary lift in \(\mathcal T\).

### Proof

The shift is an isometry, so \(S^*S=1\) and hence \(S^{*n}S^n=1\). Its range is the closed span
of \(e_n,e_{n+1},\ldots\), so \(S^nS^{*n}\) is the projection onto that range. This proves the
description, rank, and trace of \(D_n\).

Using \(S^{n+r}S^{*(n+r)}=S^n(S^rS^{*r})S^{*n}\),

\[
\begin{aligned}
D_{n+r}
&=1-S^nS^{*n}+S^n(1-S^rS^{*r})S^{*n}\\
&=D_n+S^nD_rS^{*n}.
\end{aligned}
\]

The first summand is supported on \(e_0,\ldots,e_{n-1}\), the second on
\(e_n,\ldots,e_{n+r-1}\), so they are orthogonal. Equation (3) gives periodicity and (5).

The kernel of \(S^n\) is zero and its cokernel has dimension \(n\), proving (6). For the partial
isometry lift \(S^n\) of \(z^n\), the standard boundary formula is

\[
\partial[z^n]
=[1-S^{*n}S^n]-[1-S^nS^{*n}]
=-[D_n],
\]

which proves (7). Finally, any other lift \(T\in\mathcal T\) of \(z^n\) differs from \(S^n\) by a
compact operator. It is Fredholm and compact invariance of index gives
\(\operatorname{ind}T=-n\). A unitary has index zero, so no unitary lift exists when \(n>0\).
QED.

## 3. Single-producer coupling

One one-sided isometry produces all of the following without independent slots:

- **positivity:** \(S^{*n}S^n=1\);
- **phase quotient:** \(\sigma(S)=z\) is unitary;
- **recurrent observation:** every root-of-unity boundary observer is periodic;
- **open history:** defect rank grows linearly along exact observer returns;
- **Bockstein/index:** the connecting map sends boundary winding to the negative defect class;
- **nonliftability:** nonzero winding cannot be restored to a reversible law upstairs.

This is the first finite/infinite model in the field tournament where the reversible and irreversible
organs are forced by one relation rather than stored independently.

## 4. Hostile scope

- This is classical Toeplitz/Fredholm index theory, not a novelty claim.
- Root-of-unity evaluation is a declared finite observer; the Toeplitz extension alone does not
  select \(m\).
- The theorem does not yet explain hypertranscendence or identify any HGT source with \(S\).
- Not every corpus no-go can be an index. The field candidate must support higher and nonadditive
  defects without turning into a bag of extensions.
- Arithmetic leverage requires a source-derived semigroup extension and comparison with a live
  source class before target specialization.

## 5. External parents

- Laca--Sehnem, `Toeplitz algebras of semigroups`, arXiv:2101.06822.
- Afsar--Laca--Ramagge--Sehnem, `Equilibrium on Toeplitz extensions of higher dimensional
  noncommutative tori`, arXiv:2108.09614.

## Log

- 2026-08-09 — dependency-closed Toeplitz calibration proved; universal-field status open.
