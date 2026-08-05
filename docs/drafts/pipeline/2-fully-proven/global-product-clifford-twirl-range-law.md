# Global product-Clifford twirl range law

- **Stage:** 2 — fully proven on paper
- **Status:** `[PAPER-PROVED] [BRIDGE] [NOVELTY NOT CLAIMED]`
- **Parent:** `../1-in-progress/static-local-complexity-law.md`, O4.12z25
- **Lean target:** `HTGeometry/TwoReplicaGlobalCliffordTwirlRange.lean`

## Exact statement

Let `V` be any finite qubit register and let `Gamma` be the strict one-qubit
Clifford group already realized in the corpus.  On the two-replica operator
space put

\[
 \mathcal T_V(X)=|\Gamma|^{-|V|}
   \sum_{g\in\Gamma^V}
   (U_g\otimes U_g)X(U_g\otimes U_g)^* .
\]

For each site `v`, let `F_v` exchange its two replica factors and define

\[
 \mathcal S_V=
 \operatorname{span}_{\mathbb C}
 \left\{\prod_{v\in V}F_v^{x_v}:x\in\{0,1\}^V\right\}.
\]

Then

\[
 \boxed{\operatorname{ran}\mathcal T_V=\mathcal S_V,\qquad
        \mathcal T_V^2=\mathcal T_V.}
\]

The swap words are linearly independent, so
`dim_C S_V = 2^|V|`.  The statement includes `V` empty: both sides are the
one-dimensional scalar matrix algebra.

If `U_*` is the canonical greatest maximum-defect subspace for the complete
weight-at-most-`q` two-replica Pauli commutator family, product-Clifford
covariance gives `T_V(U_*) <= U_*`; hence

\[
 \boxed{U_*=(U_*\cap\mathcal S_V)\oplus
              (U_*\cap\ker\mathcal T_V).}
\]

## Dependency-closed proof

The one-site theorem already proved in
`TwoReplicaCliffordTwirlHallSymmetryReduction.lean` says that the doubled
Clifford average `T_v` is an idempotent with range
`span_C{I_v,F_v}`.

Group the global two-replica computational index site by site.  For a pure
local tensor `X=bigotimes_v X_v`, independence of the product group and the
finite distributive law give

\[
\begin{aligned}
 \mathcal T_V(X)
 &=|\Gamma|^{-|V|}
   \sum_{g\in\Gamma^V}
     \bigotimes_v\operatorname{Ad}_{U_{g_v}\otimes U_{g_v}}(X_v)\\
 &=\bigotimes_v\left(
   |\Gamma|^{-1}\sum_{h\in\Gamma}
     \operatorname{Ad}_{U_h\otimes U_h}(X_v)\right)\\
 &=\bigotimes_v T_v(X_v).
\end{aligned}
\]

Pure local tensors span the full global matrix algebra: every global matrix
unit `E_(x,y)` is the tensor product of the local matrix units
`E_(x_v,y_v)`.  Thus

\[
                 \mathcal T_V=\bigotimes_v T_v.
\]

Choose at every site a basis of `ran T_v` and extend it by a basis of
`ker T_v`.  The induced tensor-product basis diagonalizes `T_V`: a tensor
basis vector is fixed exactly when every local factor lies in `ran T_v`, and
is killed otherwise.  Therefore

\[
 \operatorname{ran}\mathcal T_V
 =\bigotimes_v\operatorname{ran}T_v
 =\bigotimes_v\operatorname{span}\{I_v,F_v\}
 =\mathcal S_V,
\]

and `T_V` is idempotent.  Linear independence of the swap words follows from
the explicit coefficient extractor already proved for
`finiteTwoReplicaSwapInvariantEmbed`.

Every product-Clifford conjugation preserves the canonical greatest
maximizer, so their average does too.  For `x in U_*`, write

\[
 x=\mathcal T_Vx+(x-\mathcal T_Vx).
\]

The first term belongs to `U_* cap ran T_V`; idempotence places the second in
`U_* cap ker T_V`.  Their intersection is zero, proving the displayed direct
sum.

## Hostile audit

- This theorem is a finite product-group projection law, not a Haar or
  higher-design statement.
- It classifies the reducing split of the canonical obstruction; it does not
  prove either summand vanishes and therefore does not itself prove Hall.
- It supplies no circuit anti-concentration, cavity decay, complexity growth,
  plateau time, or recurrence time.
- No novelty is claimed for the abstract tensor-product commutant fact.  Its
  role is to remove a precise formal obstruction before the anisotropic
  zero-character detector can be constructed.

## Next exact theorem

On `U_* cap ker T_V`, construct a quotient detector whose nonzero Pauli
characters assemble injectively modulo the already occupied nonsinglet input.
Its kernel must lie in the sitewise swap algebra, where the connected physical
edge Casimir is already injective modulo global identity and global swap.
Instantiating `quadraticHiddenKernelRecovery_of_visibleQuotient` then closes
the full mixed two-replica Hall inequality.
