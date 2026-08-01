# Deninger Gamma-rank regular representation

- **ID:** `deninger-gamma-rank-regular-representation`
- **Stage:** 3-formalized
- **Type:** SOURCE POSITIVE COEFFICIENT CONSTRUCTION
- **Parent:** `deninger-hyperbolic-localization-rank-collapse`
- **Lean modules:**
  `GaloisForLFunctions.RHTower.DeningerArithmeticGammaRankRegular` (the algebraic core, the
  quaternionic double, the completion, and bar-Hodge descent),
  `GaloisForLFunctions.RHTower.DeningerGammaRankPowerTransfer` (the framed power transfers
  `(1)`--`(5)`, `(11)`, and the group `ℚ_{>0}^×`)

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

Fourier transform identifies the regular representation with
\(L^2(\widehat G)\).  In that picture \(U_a\) is multiplication by the
tautological character \(\chi\mapsto\chi(a)\), not pullback by a power
map.  Indeed multiplication sends \(e_q\) to \(e_{aq}\), whereas
pullback by \(\chi\mapsto\chi^a\) sends \(e_q\) to \(e_{q^a}\).
Thus this module is the regular local-system channel of the
\(\mathbb Q_{>0}\)-deck group.  It is neither Deninger's
unitary-character phase Frobenius nor the Hilbert--Kummer radial flow.

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

## Formalized statement

`GaloisForLFunctions/RHTower/DeningerArithmeticGammaRankRegular.lean` formalizes the coefficient
object itself:

- `DeningerGammaRankCore`, `deningerGammaRankPowerShift` : the finite-support double and the left
  regular translation, with `deningerGammaRankPowerShift_mul`, `_one`, `_inv` giving `(1)` on the
  core and `deningerGammaRank_smul_def` packaging it as a group action;
- `deningerGammaRankHodge`, `deningerGammaRankHodge_sq` : the odd Hodge operator `(6)` and
  `J² = -1`, `(7)`, with conjugate-linearity;
- `deningerGammaRankCup`, `deningerGammaRankCup_hodge`, `deningerGammaRankCup_hodge_pos` : the
  alternating form `(8)` and the positivity `(9)`;
- `deningerGammaRankCup_shift`, `deningerGammaRankShift_hodge` : `(10)`;
- `DeningerGammaRankHilbert`, `deningerGammaRankHilbertHodge`,
  `norm_deningerGammaRankHilbertHodge`, `deningerGammaRankHilbertHodge_sq`,
  `deningerGammaRankHilbertCup`, `deningerGammaRankHilbertCup_isAlt`,
  `deningerGammaRankHilbertHodge_positive` : the completed coefficient `ℓ²(G ⊔ G, ℂ)` with its
  antiunitary `J`, the continuous form `ω(x,y) = ⟨Jx,y⟩`, and `ω(x,Jx) = ‖x‖²`;
- `deningerGammaRankCoreToHilbert_denseRange`, `_hodge`, `_powerShift` : the algebraic core is
  dense and the two structures agree on it;
- `deningerGammaRankBarHodge_D0`, `_D1`, `_D2`, `deningerGammaRankBarHodgeCocycle2` : `J` commutes
  with all three bar coboundaries and the good truncation `ker Q²` is `J`-stable.

`GaloisForLFunctions/RHTower/DeningerGammaRankPowerTransfer.lean` formalizes the framed power
transfers, which are the arithmetic content of `(1)`--`(5)` and `(11)`:

- `deningerGammaRankHilbertPowerShift_mul`, `_one`, `_inv`, `_bijective` : the completed
  translations are a representation of `G` by invertible maps;
- `inner_deningerGammaRankHilbertPowerShift` and
  `inner_deningerGammaRankHilbertPowerShift_left` : each `U_a` is unitary with
  `U_a^† = U_{a^{-1}}`, which is `(1)`;
- `deningerGammaRankTransfer`, `deningerGammaRankCotransfer` : `V_n = √n U_a`, `F_n = √n U_{a^{-1}}`,
  which is `(2)`;
- `deningerGammaRankCotransfer_transfer` : the push--pull degree law `F_n V_n = n·id`, and
  `deningerGammaRankTransfer_adjoint` : `F_n = V_n^†` — together `(3)`;
- `inner_deningerGammaRankTransfer` : `⟨V_n x, V_n y⟩ = n⟨x,y⟩`, which is `(4)`, with
  `norm_deningerGammaRankTransfer` its norm form;
- `deningerGammaRankTransfer_centered` : `n^{-1/2}V_n = U_a`, which is `(5)`;
- `deningerGammaRankHilbertHodge_transfer`, `deningerGammaRankHilbertCup_transfer` : `JV_n = V_nJ`
  and `ω(V_n x, V_n y) = n ω(x,y)`, which is `(11)`;
- `deningerPosRat`, `deningerPosRatNat`, `deningerPosRatNat_mul`, `deningerPosRatNat_one` : the
  Frobenius colimit group `ℚ_{>0}^×` as a subgroup of `ℚˣ`, with the multiplicative embedding of
  the degrees; `deningerGammaRankPosRat_pushPull`,
  `deningerGammaRankPosRat_inner_transfer`, `deningerGammaRankPosRat_centered_norm` instantiate
  `(3)`, `(4)` and unitarity at that group, so the hostile-audit point that positive integers give
  only an isometry is met by an actual group of rational powers.

Everything the card proves — `(1)`--`(11)`, the completion, and the bar-Hodge descent — is
formalized; nothing in the construction is left on paper.  The items under "Remaining exact gates"
are open source theorems that the card states as open, not parts of the construction.

### Verification

- Direct commands: `lake env lean` on both modules — pass with no errors and no warnings.
- Cached module build: `lake build GaloisForLFunctions.RHTower.DeningerGammaRankPowerTransfer`
  completes (`✔ [3106/3106]`).
- Scratch `#print axioms` on all transfer and positive-rational theorems: only `propext`,
  `Classical.choice`, `Quot.sound`.
- Imported by the `GaloisForLFunctions.RHTower` umbrella.

## Gates

- [x] 0 → 1 in-progress: positive Gamma-rank coefficient isolated
- [x] 1 → 2 fully-proven: `(1)`--`(11)`, the completion, and bar-Hodge descent proved
- [x] 2 → 3 formalized: coefficient object, completion, bar-Hodge descent
- [x] 2 → 3 formalized: framed power transfers `(1)`--`(5)`, `(11)`, and `ℚ_{>0}^×`
- [ ] 3 → 4 publication-ready: blocked on the five open source theorems below

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
- Its standard reduced \(\ell^2\) bar completion contributes no
  harmonic group cohomology: \(G=\mathbb Q_{>0}^{\times}\) is infinite
  amenable, so Cheeger--Gromov vanishing applies.  A different
  arithmetic incidence topology would require an independent
  construction and comparison; finite cutoffs do not establish it.
- Formula `(9)` is genuine source positivity, but it proves RH only after the determinant,
  Lefschetz, and comparison gates identify the harmonic generator with arithmetic \(\Theta\).
- Choosing a phase twist indexed by Xi zeros is forbidden.  Only the untwisted rational power
  action appears here.

For the reduced \(\ell^2\)-cohomology statement, use the
Cheeger--Gromov theorem that reduced \(L^2\)-cohomology of an infinite
countable amenable group vanishes in every degree; a modern primary
reference and locally compact extension is Henrik Densing Petersen,
*L2-Betti Numbers of Locally Compact Groups*,
arXiv:1104.3294.

## Novelty audit

Regular representations and quaternionic doubles are standard.  New content is their exact
assembly with hyperbolic localization and Milnor--Witt push--pull
degree as a positive regular local-system coefficient.  Later source
analysis identifies Deninger's arithmetic coefficient instead with
the degreewise invariant Tate--Milnor sheaf and its
Hilbert--Kummer/Poisson pushforward; the regular module is auxiliary,
not a definition of arithmetic cohomology.

## Log

- 2026-08-01 — Formalized the framed power transfers.  The pre-existing module already carried the
  coefficient object, its quaternionic double, the `ℓ²` completion and the bar-Hodge descent, but
  not the scaled transfers that carry the Milnor--Witt degree.  Added
  `DeningerGammaRankPowerTransfer`: the completed representation law and adjoint
  `U_a^† = U_{a^{-1}}`, the transfers `V_n = √n U_a`, `F_n = √n U_{a^{-1}}` with `F_nV_n = n·id`,
  `⟨V_nx,V_ny⟩ = n⟨x,y⟩`, `ω(V_nx,V_ny) = n ω(x,y)`, `JV_n = V_nJ`, the centering
  `n^{-1/2}V_n = U_a`, and the group `ℚ_{>0}^×` with the multiplicative embedding of degrees.
  All formalization gates closed; card moved to `3-formalized`.  The five listed source gates
  remain open research.
