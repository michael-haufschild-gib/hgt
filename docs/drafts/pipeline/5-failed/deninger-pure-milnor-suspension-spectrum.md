# Pure Milnor suspension produces the zeta-zero spectrum

- **ID:** `deninger-pure-milnor-suspension-spectrum`
- **Stage:** 5-failed
- **Type:** FALSIFIED
- **Parent:** `deninger-derived-mw-rational-witt-coefficient`

## Retired claim

After the local unit-amalgamated coefficient collapses to
\[
 \mathbb R\oplus
 ((F^\times/\mu_\infty)\otimes\mathbb R)[-1],
\]
its pure power action and the \(\mathbb Q_{>0}\)-suspension are sufficient
to create the nontrivial spectral \(H^1\) required by Deninger.

## Exact killing theorem

`[PROVED HERE] [DAC_PURE_SUSPENSION_SCALAR_SPECTRUM_NO_GO]`

Let \(V\) be a Hausdorff topological complex vector space and
\[
 U:\mathbb R\longrightarrow\operatorname{Aut}(V)
\]
a strongly continuous one-parameter group.  Fix \(w\in\mathbb C\).
Assume that on the dense rational-power subgroup,
\[
 U(\log q)=q^w\operatorname{id}_V
 \qquad(q\in\mathbb Q_{>0}),                                        \tag{1}
\]
where \(q^w=\exp(w\log q)\).  Then
\[
 U(t)=e^{wt}\operatorname{id}_V
 \qquad(t\in\mathbb R).                                              \tag{2}
\]
On every vector in the infinitesimal-generator domain,
\[
 \Theta=w\operatorname{id}_V.                                       \tag{3}
\]
Thus the point spectrum is contained in \(\{w\}\).

### Proof

Positive rationals are dense in \(\mathbb R_{>0}\), so
\(\log\mathbb Q_{>0}\) is dense in \(\mathbb R\).  For fixed \(v\in V\),
both maps
\[
 t\longmapsto U(t)v,\qquad
 t\longmapsto e^{wt}v
\]
are continuous and agree on this dense subset by `(1)`.  The Hausdorff
equalizer is closed, hence they agree on all of \(\mathbb R\).  This proves
`(2)`.  Differentiating at zero on the generator domain gives `(3)`.

For the real Milnor symbol algebra, the \(q\)-power map acts on weight
\(n\) by \(q^n\).  Deninger's Tate twist \(\mathbb R(n)\) normalizes this
to the trivial action.  Consequently any descent that retains only this
pure scalar action has scalar continuous flow: weight \(n\) before
centering, weight zero after normalization, or weight \(1/2\) after an
externally imposed half-density.  None produces an infinite nonreal
point spectrum.

The contradiction does not depend on a numerical zero calculation.
Hardy's theorem supplies infinitely many nonreal zeros of the completed
zeta function, while `(3)` supplies at most one point eigenvalue.

## Strongest positive survivor

`[CONJECTURE] [DAC_ANALYTIC_NONPURE_LEAFWISE_FACTOR]`

The arithmetic coefficient must retain a source-defined analytic
leafwise factor \(\mathscr O_{\mathrm{an},\mathcal F}\) on which normalized
power maps are not scalar:
\[
 \mathscr A_{\mathrm{source}}
 =
 \mathscr O_{\mathrm{an},\mathcal F}
 \mathop{\otimes}^{\mathbb L}_{\mathscr P_F}
 \underline{\mathcal K}^{M}_{F,\mathbb R}.                           \tag{4}
\]
The Milnor base change in `(4)` imposes Steinberg and residue laws only in
the arithmetic-symbol directions.  It must not collapse the analytic
leafwise/Frobenius dynamics to the pure symbol algebra.  Exact-weight
descent then acts on the tensor product; the non-pure analytic factor is
where a nontrivial infinitesimal spectrum, trace-class localization, and
regularized determinant can live.

Minimal falsifiable requirements on
\(\mathscr O_{\mathrm{an},\mathcal F}\) are:

1. a sheaf or hypersheaf on Deninger's actual suspension cover, not an
   Xi-indexed target space;
2. coherent Frobenius/Verschiebung, Galois, and restriction maps;
3. a non-scalar normalized rational-power action after Milnor
   amalgamation;
4. a closed transverse generator on a nuclear or Hilbert completion;
5. a source trace whose local fixed-orbit terms are the prime powers and
   archimedean contribution.

The final item is what can identify the determinant with completed zeta.
No divisor data may enter the definition of `(4)`.

## New insight

Milnor--Witt theory supplies arithmetic relations, residues, orientations,
and duality.  It cannot by itself supply the analytic zeta spectrum.
Deninger's §12 already points in the correct direction: his tentative
\(\mathcal O_{\mathcal F c}\) should be strengthened by an analyticity
condition along the \(\check X(\mathbb C)\)-coordinate.  That missing
analytic sheaf is a critical coefficient factor, not optional regularity
added after cohomology.

## Status

- Killing theorem: dependency-closed paper proof.
- Lean theorem: pending in
  `DeningerArithmeticPureSuspensionNoGo.lean`.
- Positive survivor: source-pure conjecture; analytic sheaf construction,
  trace formula, and positivity open.

## References

- Christopher Deninger, *Dynamical systems for arithmetic schemes*, end
  of §12: the sheaf \(\mathcal O_{\mathcal F c}\) should acquire an
  analyticity condition along the leaves:
  https://arxiv.org/abs/1807.06400

## Log

- 2026-07-26 — Pure Milnor suspension route killed; analytic non-pure
  leafwise factor isolated as mandatory positive survivor.
