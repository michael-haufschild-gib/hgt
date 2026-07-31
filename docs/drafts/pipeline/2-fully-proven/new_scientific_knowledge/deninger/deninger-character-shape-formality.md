# Real formality of Deninger--Kucharczyk--Scholze character components

- **ID:** `deninger-character-shape-formality`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Parent:** `deninger-derived-mw-rational-witt-coefficient`
- **Statement:** The real shape-cochain algebra of a cyclotomic rational-Witt character
  component is the exterior algebra on its degree-one unit space; consequently the ordinary
  unit-amalgamated coefficient is the real Milnor symbol algebra.

## Setup

Let \(F\) be any field of characteristic zero containing \(\mu_\infty\), fix
\(\mu_\infty\hookrightarrow S^1\), and put
\[
 V_F=F^\times/\mu_\infty.
\]
The torsion subgroup of \(F^\times\) is exactly \(\mu_\infty\), so \(V_F\) is
torsion-free.  Divisibility and algebraic closedness are not required.

The Kucharczyk--Scholze character component is a torsor under the compact character group
\[
 T_F:=\operatorname{Hom}(V_F,S^1).
\]
Choosing one extension of the fixed character on \(\mu_\infty\) identifies the component
with \(T_F\).  The resulting cochain algebra and all conclusions below are independent of
that choice up to translation, and translation acts trivially on invariant forms.

Let \(\mathcal L_F\) be the filtered poset of finitely generated free subgroups
\(L\subset V_F\).  Restriction of characters gives
\[
 T_F\cong\varprojlim_{L\in\mathcal L_F}T_L,\qquad
 T_L=\operatorname{Hom}(L,S^1),
\]
and each \(T_L\) is a finite-dimensional torus.  Define the real shape-cochain CDGA by
\[
 C^*_{\mathrm{sh}}(T_F;\mathbb R)
 :=
 \varinjlim_{L\in\mathcal L_F}\Omega^*(T_L;\mathbb R),                 \tag{1}
\]
with transition maps given by pullback.  This model computes continuous Čech/sheaf
cohomology because Čech cohomology is continuous on inverse systems of compact Hausdorff
spaces with surjective bonding maps.

## Formality theorem

`[PROVED HERE] [DAC_CHARACTER_SHAPE_FORMALITY]`

There is a natural quasi-isomorphism of commutative DGAs
\[
 \left(\Lambda_{\mathbb R}^*(V_F\otimes_{\mathbb Z}\mathbb R),0\right)
 \xrightarrow{\;\sim\;}
 C^*_{\mathrm{sh}}(T_F;\mathbb R).                                    \tag{2}
\]

### Proof

For every lattice \(L\), let
\(\Omega^*_{\mathrm{inv}}(T_L)\) be the translation-invariant differential forms.  Evaluation
at the identity gives
\[
 \Omega^*_{\mathrm{inv}}(T_L)
 \cong
 \left(\Lambda_{\mathbb R}^*(L\otimes_{\mathbb Z}\mathbb R),0\right).
\]
The inclusion of invariant forms into all smooth forms is a multiplicative
quasi-isomorphism: it is the standard de Rham representative of the cohomology of a torus.
For a homomorphism \(T_{L'}\to T_L\), pullback preserves invariant forms, so these
quasi-isomorphisms form a natural filtered diagram.

Filtered colimits of real vector spaces are exact.  Taking the colimit of the natural
quasi-isomorphisms therefore gives a quasi-isomorphism
\[
 \varinjlim_L
 \Lambda_{\mathbb R}^*(L\otimes\mathbb R)
 \xrightarrow{\sim}
 \varinjlim_L\Omega^*(T_L).
\]
Exterior powers commute with filtered colimits, and
\(\varinjlim_LL=V_F\).  The source is consequently
\(\Lambda_{\mathbb R}^*(V_F\otimes_{\mathbb Z}\mathbb R)\), proving `(2)`.

## Free-unit identification

Let
\[
 \mathcal P_{F,\mathbb R}
 =
 \operatorname{Free}_{E_\infty,H\mathbb R}^{+}
 \bigl(\Sigma_{\mathrm{ar}}H(V_F\otimes_{\mathbb Z}\mathbb R)\bigr).
\]
Rational \(E_\infty\)-algebras are modeled by commutative DGAs.  A free commutative algebra
on generators in odd arithmetic degree one is the exterior algebra.  Hence
\[
 \pi_*\mathcal P_{F,\mathbb R}
 \cong
 \Lambda_{\mathbb R}^*(V_F\otimes_{\mathbb Z}\mathbb R).               \tag{3}
\]
The Kummer map
\[
 \mathcal P_{F,\mathbb R}
 \longrightarrow
 C^*_{\mathrm{sh}}(T_F;\mathbb R)
\]
is the map represented by invariant degree-one forms.  Equations `(2)`--`(3)` show that it
is an equivalence of \(E_\infty\) \(H\mathbb R\)-algebras.

`[PROVED HERE] [DAC_REAL_FREE_UNIT_EQUIVALENCE]`
\[
 \mathcal P_{F,\mathbb R}
 \xrightarrow{\sim}
 C^*_{\mathrm{sh}}(T_F;\mathbb R).                                    \tag{4}
\]

## Milnor-amalgamation corollary

Let
\[
 \mathcal K_{F,\mathbb R}^M
 :=
 H\!\left(K_*^M(F)_{\mathrm{tf}}\otimes_{\mathbb Z}\mathbb R\right)
\]
be the Eilenberg--Mac Lane \(E_\infty\) algebra of the real graded Milnor ring, with zero
differential.  Its symbol map gives
\(\mathcal P_{F,\mathbb R}\to\mathcal K_{F,\mathbb R}^M\).  Then
\[
 \begin{aligned}
 \mathcal C_{F,\mathbb R}^M
 &:=
 C^*_{\mathrm{sh}}(T_F;\mathbb R)
 \mathop{\otimes}^{\mathbb L}_{\mathcal P_{F,\mathbb R}}
 \mathcal K_{F,\mathbb R}^M \\
 &\simeq
 \mathcal K_{F,\mathbb R}^M.                                         \tag{5}
 \end{aligned}
\]

### Proof

Base change along the equivalence `(4)` is an equivalence.  Therefore the left side of `(5)`
is
\[
 \mathcal P_{F,\mathbb R}
 \otimes_{\mathcal P_{F,\mathbb R}}^{\mathbb L}
 \mathcal K_{F,\mathbb R}^M
 \simeq\mathcal K_{F,\mathbb R}^M.
\]

Consequently
\[
 \pi_q\mathcal C_{F,\mathbb R}^M
 \cong K_q^M(F)_{\mathrm{tf}}\otimes_{\mathbb Z}\mathbb R
 \quad(q\geq0).                                                        \tag{6}
\]
This proves the real local form of the Kucharczyk--Scholze Milnor comparison, including all
Steinberg relations and higher syzygies.  It is stronger than killing degree-two Steinberg
classes one at a time.

## Equivariance

Every field automorphism preserving the chosen cyclotomic structure acts linearly on \(V_F\),
dually on \(T_F\), and functorially on invariant forms and Milnor symbols.  Thus `(2)`--`(6)`
are equivariant for the cyclotomic Galois action.  Likewise \(a\mapsto a^n\) acts as scalar
multiplication by \(n\) on \(V_F\), and all displayed maps commute with the corresponding
Frobenius action.

This proves equivariance on the cyclotomic ordinary channel.  Verschiebung across ramified
finite correspondences and MW residue enrichment require the separate coherent Gysin
construction.

## Boundary of the theorem

- The theorem uses shape/Čech cochains `(1)`.  Identifying these with the precise completed
  leafwise complex used after Deninger's suspension remains a global comparison.
- It proves the real ordinary Milnor channel.  Integral torsion, twisted MW residue data,
  and global rank/signature descent remain open.
- It does not construct arithmetic residue gluing, archimedean regulator, Hodge positivity,
  Lefschetz trace, determinant, or RH.

## References

- Robert A. Kucharczyk and Peter Scholze,
  *Topological realisations of absolute Galois groups*, Theorem 1.8 and Question 1.10:
  https://people.mpim-bonn.mpg.de/scholze/GaloisTop.pdf
- Yves Félix and Steve Halperin,
  *Rational homotopy theory via Sullivan models: a survey*:
  https://arxiv.org/abs/1708.05245
- Jacob Lurie, *Higher Algebra*, rational commutative algebra and free algebras:
  https://www.math.ias.edu/~lurie/papers/HA.pdf

## Log

- 2026-07-26 — proved real shape formality and the ordinary unit-amalgamated Milnor
  comparison on every cyclotomic character component; the proof only needs
  \(F^\times/\mu_\infty\) torsion-free, so algebraic closedness was removed.
