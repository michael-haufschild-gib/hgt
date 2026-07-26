# Finite-unit Milnor colimit

- **ID:** `deninger-finite-unit-milnor-colimit`
- **Stage:** 2-fully-proven
- **Type:** SOURCE ALGEBRA THEOREM
- **Label:** `DAC_FINITE_UNIT_MILNOR_COLIMIT`
- **Parent:** `deninger-baumslag-milnor-pro-realization`

## Statement

Let \(k\) be a field, let \(V\) be a possibly infinite-dimensional
\(k\)-vector space, and let \(\mathcal I(V)\) be the filtered poset of its
finite-dimensional subspaces.  Put
\[
 P=\Lambda_k(V),\qquad P_U=\Lambda_k(U),\qquad
 K_U=k\oplus U,\quad U^2=0.                                         \tag{1}
\]
Then:

1. \(P\) is a free, hence flat, \(P_U\)-module for every
   \(U\in\mathcal I(V)\);
2. the derived base change is discrete as a DGA:
   \[
   P\mathop{\otimes}^{\mathbb L}_{P_U}K_U
   \simeq
   P\otimes_{P_U}K_U
   \cong
   P/\langle\Lambda^{\ge2}U\rangle;                                 \tag{2}
   \]
3. with transition maps induced by inclusions \(U\subset U'\),
   \[
   \operatorname*{colim}_{U\in\mathcal I(V)}
   \left(P\mathop{\otimes}^{\mathbb L}_{P_U}K_U\right)
   \simeq k\oplus V,\qquad V^2=0.                                   \tag{3}
   \]

If \(Q_U\xrightarrow{\sim}K_U\) is any cofibrant
\(P_U\)-algebra resolution, then `(2)`--`(3)` remain true with \(Q_U\) in
place of \(K_U\).

## Proof

Choose a vector-space complement \(V=U\oplus W\).  Exterior multiplication
gives
\[
 \Lambda(V)\cong\Lambda(U)\otimes_k\Lambda(W),
\]
so \(P\) is free over \(P_U\).  Derived tensor therefore equals ordinary
tensor.  Since \(K_U=P_U/\Lambda^{\ge2}U\), base change gives the quotient in
`(2)`.

The transition \(U\subset U'\) adds relations killing every product whose
factors lie in \(U'\).  In the filtered colimit, every exterior monomial of
degree at least two vanishes: its finitely many factors span some
finite-dimensional \(U\).  No degree-zero or degree-one element is killed,
because every transition ideal is generated in degrees at least two.
Consequently the colimit is exactly the square-zero algebra \(k\oplus V\).

Filtered colimits of vector spaces are exact.  Therefore the same
calculation applies to cofibrant resolutions \(Q_U\to K_U\): flat base
change preserves each quasi-isomorphism, and filtered colimit preserves the
resulting quasi-isomorphisms.

## Application

For \(V=V_{F,\mathbb Q}\), `(3)` proves the algebraic continuous-cochain
target in `DAC_BAUMSLAG_MILNOR_PRO_REALIZATION`.  After tensoring
with \(\mathbb R\), it is
\[
 K_\ast^M(F)\otimes\mathbb R
 \cong\mathbb R\oplus V_{F,\mathbb R}.
\]
The remaining issue is geometric: prove finite-stage cochains satisfy the
relative Eilenberg--Moore comparison and commute with the pro-realization.

## Hostile audit

- Freeness uses a noncanonical complement, but flatness and `(2)` are
  canonical.
- The theorem concerns global algebraic base change.  It makes no
  stalkwise assertion and does not conflict with
  `DAC_KUMMER_SHEAF_STALK_TOR_OBSTRUCTION`.
- It does not prove the twisted topological Eilenberg--Moore map `(4)` of the
  realization card.
- Integral exterior algebras need not be flat under arbitrary subgroup
  inclusions; the theorem is stated over a field.

**Verdict:** `FULLY PROVEN ON PAPER`.
