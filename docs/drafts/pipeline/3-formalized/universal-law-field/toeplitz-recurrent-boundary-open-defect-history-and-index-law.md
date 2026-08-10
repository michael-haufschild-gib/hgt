# Toeplitz recurrent boundary, open defect history, and index law

- **ID:** ULF-TOEPLITZ-1
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** polarized directed-history survivor
- **Statement:** The unilateral shift has recurrent finite boundary observations and constant initial Gram while its defect rank and Toeplitz boundary index grow without bound.
- **Status:** [PAPER-PROVED] [ROUTE-INDEPENDENT] [CLASSICAL TOEPLITZ PARENTS] [FIELD CALIBRATION] [LEAN CERTIFIED]

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

## Lean certification status (2026-08-09) — COMPLETE

Module: `GaloisForLFunctions.HTGeometry.ConstitutiveToeplitzDefectIndex`
(wired into `HTGeometry.UniversalLawField`).

The Hardy space is `ToeplitzSpace = lp (fun _ : ℕ => ℂ) 2`.  The `n`-fold shift is defined once, as
the coordinate reindexing `shiftFun n f k = if k < n then 0 else f (k − n)`, so every identity below
is proved without induction on operator powers.

1. `shiftIsom` is the `n`-fold shift as a linear isometry, `shiftOp` its bounded form, `backOp` the
   `n`-fold backward shift.  `adjoint_shiftOp` proves `S*ⁿ = backOp n` from the `ℓ²` inner product,
   and `backOp_comp_shiftOp` / `adjoint_comp_shiftOp` give clause 1: `S*ⁿSⁿ = 1`.
2. `defectOp n = 1 − Sⁿ S*ⁿ`; `defectOp_apply` proves it is exactly the truncation onto the first
   `n` coordinates, `defectOp_comp_self` and `adjoint_defectOp` make it an orthogonal projection.
   `defectSubmodule n` is its range (`range_defectOp`), `defectCoordEquiv` is an explicit linear
   isomorphism with `ℂⁿ`, and `finrank_defectSubmodule` gives `rank Dₙ = n`.
3. `defectOp_add` is equation (4) and `defectOp_orthogonal` proves the two summands annihilate each
   other in both orders — the orthogonality of the cocycle decomposition.
4. `boundaryObserver m n = exp(2πi n/m)` with `boundaryObserver_add` the `m`-periodicity.
5. `boundaryObserver_mul` gives `O_m(km) = 1` and `finrank_defect_return_tendsto` proves the defect
   rank diverges along the return sequence; `recurrent_boundary_open_defect` bundles (5).
6. `ker_shiftOp` proves `ker Sⁿ = ⊥`; `range_shiftOp` identifies `range Sⁿ` with `ker Dₙ`, so
   `cokerShiftEquiv` is an explicit isomorphism `ToeplitzSpace ⧸ range Sⁿ ≅ defectSubmodule n` and
   `finrank_coker_shiftOp` gives `dim coker Sⁿ = n`.  `shiftIndex_eq` is equation (6):
   `ind Sⁿ = −n`.
7. `coDefect_eq_zero` proves `1 − S*ⁿSⁿ = 0`, and `boundaryClass` is the standard boundary
   expression `[1 − S*ⁿSⁿ] − [1 − SⁿS*ⁿ]` evaluated by rank — the image of `∂[zⁿ]` under the rank
   isomorphism `K₀(𝒦) ≅ ℤ`.  `boundaryClass_eq_neg_defect` is equation (7): `∂[zⁿ] = −[Dₙ]`;
   `boundaryClass_eq` evaluates it to `−n` and `boundaryClass_eq_shiftIndex` identifies it with the
   Fredholm index.
8. `shiftOp_not_surjective` shows `Sⁿ` misses `e₀` for `n > 0`.
   `no_invertible_compact_perturbation` proves that **no invertible operator differs from `Sⁿ` by a
   compact operator**: writing `V Sⁿ = 1 − C` with `C` compact, injectivity of `Sⁿ` rules out the
   eigenvalue `1`, so mathlib's Fredholm alternative puts `1` in the resolvent set of `C`, making
   `1 − C` — hence `Sⁿ` — surjective, a contradiction.  `no_unitary_compact_perturbation` is the
   unitary case, i.e. clause 8.

`toeplitz_recurrent_boundary_open_defect_index` bundles all eight clauses on the single producer.

**Scope note.**  Clause 7 is certified in its computational form: mathlib has no C*-algebra
K-theory, so the module does not construct `K₀(𝒦)`, the Toeplitz extension `0 → 𝒦 → 𝒯 → C(S¹) → 0`,
or the six-term sequence.  What is certified is exactly the number the connecting map produces under
the standard rank identification `K₀(𝒦) ≅ ℤ`, together with the operator identities
`1 − S*ⁿSⁿ = 0` and `1 − SⁿS*ⁿ = Dₙ` that define it.  Clause 8 is certified in the strictly stronger
operator form (no *invertible* compact perturbation), which does not need the Toeplitz algebra at
all.

`#print axioms` on `backOp_comp_shiftOp`, `adjoint_shiftOp`, `defectOp_apply`,
`finrank_defectSubmodule`, `defectOp_add`, `defectOp_orthogonal`, `boundaryObserver_add`,
`finrank_defect_return_tendsto`, `shiftIndex_eq`, `boundaryClass_eq`,
`no_unitary_compact_perturbation`, and `toeplitz_recurrent_boundary_open_defect_index` reports only
`propext`, `Classical.choice`, and `Quot.sound`.
