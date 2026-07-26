# Deninger Gamma-rank regular representation

- **ID:** `deninger-gamma-rank-regular-representation`
- **Stage:** 2-fully-proven
- **Type:** SOURCE POSITIVE COEFFICIENT CONSTRUCTION
- **Parent:** `deninger-hyperbolic-localization-rank-collapse`
- **Lean status:** algebraic core, dense Hilbert completion, and bar-Hodge descent directly check
  in `DeningerArithmeticGammaRankRegular.lean`

## Goal

Construct the positive odd Hilbert coefficient channel left open by hyperbolic localization.  The
construction must realize every centered power transfer by a source-defined unitary, before any
Xi-divisor comparison.

## Construction

Let
\[
 G=\mathbb Q_{>0}^{\times},\qquad K=\ell^2(G,\mathbb C).
\]
For \(a\in G\), let \(U_a\) be the left regular representation
\[
 U_a e_q=e_{aq}.
\]
Multiplication by \(a\) is a bijection of \(G\), so \(U_a\) is unitary and
\[
 U_aU_b=U_{ab},\qquad U_a^\dagger=U_{a^{-1}}.                     \tag{1}
\]

For \(n\geq1\), define the uncentered pullback and pushforward
\[
 V_n=\sqrt n\,U_n,\qquad F_n=\sqrt n\,U_{n^{-1}}.                 \tag{2}
\]
Then
\[
 F_n=V_n^\dagger,\qquad F_nV_n=n\,\mathrm{id},                   \tag{3}
\]
and
\[
 \langle V_nx,V_ny\rangle=n\langle x,y\rangle.                   \tag{4}
\]
Thus the centered transfer is exactly
\[
 n^{-1/2}V_n=U_n.                                                 \tag{5}
\]

Double the coefficient space:
\[
 \mathcal K_\Gamma=K\oplus K.
\]
Let \(C\) denote coefficientwise complex conjugation and define
\[
 J(f,g)=(-Cg,Cf).                                                 \tag{6}
\]
Then \(J\) is anti-linear, antiunitary, and
\[
 J^2=-1.                                                         \tag{7}
\]
On the dense finite-support subspace define the complex-bilinear alternating form
\[
 \omega((f,g),(f',g'))
   =\sum_{q\in G}\bigl(f(q)g'(q)-g(q)f'(q)\bigr).                 \tag{8}
\]
The series extends continuously to all of \(\mathcal K_\Gamma\) by Cauchy--Schwarz.  Directly,
\[
 \omega(x,Jx)=\|f\|^2+\|g\|^2,                                  \tag{9}
\]
so `(6)` is a positive odd Hodge operator.  Since every \(U_a\) is a real coordinate
permutation,
\[
 JU_a=U_aJ,\qquad
 \omega(U_ax,U_ay)=\omega(x,y).                                  \tag{10}
\]
Equations `(2)` and `(10)` give
\[
 JV_n=V_nJ,\qquad \omega(V_nx,V_ny)=n\,\omega(x,y).               \tag{11}
\]

## Relation to hyperbolic localization

Over a real closed coefficient point,
\[
 GW[h^{-1}]\simeq\mathbb Z[1/2].
\]
The scalar action on \(\mathcal K_\Gamma\) is therefore the canonical rank action.  By
`deninger-hyperbolic-localization-rank-collapse`, the motivic relation
\[
 F_nV_n=n_\epsilon\,\mathrm{id}
\]
maps exactly to `(3)`.  The signature sector is killed algebraically; no indefinite quadratic
form enters the Hilbert metric.

The regular representation is also the Fourier model of the compact Pontryagin dual
\(\widehat G\).  In that picture \(U_a\) is pullback by the corresponding power automorphism.
This is the Hilbert coefficient naturally associated with inverting all Frobenii in Deninger's
\(\mathbb Q_{>0}\)-suspension.

## Consequence for the finite bar complex

Tensor the finite-support MW correspondence packet with the algebraic core
\[
 \mathbb C[G]\oplus\mathbb C[G]\subset\mathcal K_\Gamma.
\]
Let every framed power transfer act through \(V_n\) on the Gamma factor.  Because `(1)` is a
genuine representation, the bar identities remain exact.  Because `(10)` holds coefficientwise,
every bar face commutes with \(J\), and the total bar differential does as well.  After centering,
the \(U_n\) are unitary chain maps.  `deninger-unitary-brst-hodge-descent` then proves that they
commute with the finite Hodge Laplacian and preserve harmonic cohomology.

This closes existence of a positive Gamma-rank coefficient object.  It does not yet prove that
the MW relations form a closed \(J\)-stable subcomplex or that the cofinal harmonic completion
has Deninger's determinant.

## Exact completion and incidence descent

The completed coefficient is taken directly as
\[
  \mathcal K_\Gamma=\ell^2(G\sqcup G,\mathbb C).
\]
The finite-support double embeds linearly, injectively, and densely.  On the two summands the
completed Hodge operator is
\[
  (Jx)(\operatorname{inl}q)=-\overline{x(\operatorname{inr}q)},\qquad
  (Jx)(\operatorname{inr}q)=\overline{x(\operatorname{inl}q)}.
\]
It is antiunitary, squares to \(-1\), and gives the continuous alternating form
\[
  \omega(x,y)=\langle Jx,y\rangle,\qquad
  \omega(x,Jx)=\|x\|^2.
\]
Block-diagonal left translation on \(G\sqcup G\) is unitary, commutes with \(J\), preserves
\(\omega\), and agrees with the algebraic action on the dense core.

Moreover, additivity and \(JT_n=T_nJ\) imply pointwise that \(J\) commutes with all three bar
coboundaries in `(2)` of `deninger-mw-gamma-brst-complex`.  Consequently the good truncation
\(\ker Q^2\) is \(J\)-stable.  This removes Gamma-coefficient/Hodge compatibility with the bar
skeleton from the open core.  It does not prove stability of the separate Milnor--Witt/Steinberg
relation subspace.

## Remaining exact gates

1. Define the tensor action on the finite MW framed-correspondence presentation and prove its
   MW/Steinberg relation subspace is closed and stable under the already constructed \(J\).
2. Prove finite harmonic cohomology is concentrated in degrees \(0,1,2\) with the required
   endpoint Tate classes.
3. Construct cofinal embeddings and prove closability plus strong convergence of harmonic
   projections.
4. Compare the resulting cup/Hodge cohomology with the already constructed prime--Gamma packet
   cohomology.
5. Prove the existing determinant/Lefschetz carrier is the same cohomological flow, without
   evaluating Xi zeros in the construction.

## Hostile audit

- On \(\ell^2(\mathbb N_{>0})\), \(q\mapsto nq\) is only an isometry, not a unitary.  Passing to
  \(G=\mathbb Q_{>0}^{\times}\) is essential and is exactly Deninger's Frobenius colimit.
- The regular representation alone has the wrong, highly non-discrete spectral behavior.  The
  arithmetic spectrum must arise after the MW incidence differential and cofinal harmonic
  reduction; it may not be attributed to the coefficient module itself.
- Formula `(9)` is genuine source positivity, but it proves RH only after the determinant,
  Lefschetz, and comparison gates identify the harmonic generator with arithmetic \(\Theta\).
- Choosing a phase twist indexed by Xi zeros is forbidden.  Only the untwisted rational power
  action appears here.

## Novelty audit

Regular representations and quaternionic doubles are standard.  New content is their exact
assembly with hyperbolic localization and Milnor--Witt push--pull degree to construct the positive
Gamma-rank coefficient demanded by the Deninger source complex.
