# Route E central Wold patch seam is an exact coboundary

## Status

Paper proof complete. Lean proof complete in
`GaloisForLFunctions/RHTower/MobiusWoldPatchSeamCoboundary.lean`.

This closes the algebraic patch-seam gate only. It does not prove physical Hall expansion,
Möbius cancellation, or RH.

## Statement

Fix \(n,r\geq0\). Let \(Q_r,Q_{r+1}\in\mathbb Q[t]\) have degree at most \(n\) and agree with
squarefree parity on consecutive patches:
\[
Q_r(r+k)=(-1)^{r+k},\qquad
Q_{r+1}(r+1+k)=(-1)^{r+1+k}
\quad(0\leq k\leq n).
\]
Then
\[
n!\bigl(Q_{r+1}(t)-Q_r(t)\bigr)
=(-1)^{r+n+1}2^{n+1}
  \prod_{j=1}^{n}(t-r-j).                              \tag{1}
\]
In particular, transition vanishes on every common integral layer
\(t=r+1,\ldots,r+n\), and its first exterior value is
\[
Q_{r+1}(r+n+1)-Q_r(r+n+1)
=(-1)^{r+n+1}2^{n+1}.                                  \tag{2}
\]
For any finite chain of patch readers,
\[
\sum_{j=0}^{m-1}(Q_{r+j+1}-Q_{r+j})
=Q_{r+m}-Q_r.                                          \tag{3}
\]
Thus adjacent patch differences form an exact additive \(1\)-coboundary. No internal scalar
seam survives a finite chain.

## Proof

Difference \(D=Q_{r+1}-Q_r\) has degree at most \(n\). Both readers equal parity on their \(n\)
common layers, so
\[
D(r+1)=\cdots=D(r+n)=0.
\]
Hence \(D\) is a scalar multiple of monic polynomial
\[
F_{r,n}(t)=\prod_{j=1}^{n}(t-r-j).
\]
First exterior interpolation law for \(Q_r\) is
\[
Q_r(r+n+1)=(-1)^{r+n+1}(1-2^{n+1}),
\]
whereas \(Q_{r+1}(r+n+1)=(-1)^{r+n+1}\). Therefore
\[
D(r+n+1)=(-1)^{r+n+1}2^{n+1}.
\]
Since \(F_{r,n}(r+n+1)=n!\), equation (1) follows. Equation (3) is telescoping.

On an exterior integral layer \(t\ge r+n+1\),
\[
F_{r,n}(t)
=n!\binom{t-r-1}{n},
\]
so sole polynomial extension channel is exactly top subset-incidence coordinate identified in
breadth audit.

## Consequence for Route E

Earlier formulation treated cancellation of adjacent rank-one seams as a new Carleson
hypothesis. That was insufficiently audited. A partition subordinate to overlapping patches
changes readers only where both already equal parity, and (3) cancels all internal polynomial
transitions. Algebraic seam is therefore solved.

This does **not** create arithmetic cancellation. Incidence value
\(\binom{t-r-1}{n}\) counts labels, not distinct physical integers, and no label multiplicity can
increase Hall capacity. Remaining theorem must construct a source-pointed ordinary-integer
relation whose physical neighbor sets satisfy interval Hall expansion and whose paired
breadth--depth data carry friable cutoff flux.

## Lean certificate

Module:
`formal/GaloisForLFunctions/RHTower/MobiusWoldPatchSeamCoboundary.lean`.

Theorems:

- `woldPatchSeamPolynomial_monic`
- `woldPatchSeamPolynomial_natDegree`
- `woldPatchSeamPolynomial_eval_overlap`
- `woldPatchSeamPolynomial_eval_firstExterior`
- `factorial_mul_adjacentParityInterpolants_sub_eq_seamPolynomial`
- `woldAdjacentPatchTransitions_telescope`

All statements are unconditional.

## Novelty audit

Polynomial interpolation, falling factorials, and telescoping coboundaries are classical.
No novelty is claimed for those ingredients. Project-new content is exact correction of Route E
frontier: central Wold patching has no independent scalar seam, and surviving obstruction is
physical source-pointed Hall expansion on paired breadth--depth data.
