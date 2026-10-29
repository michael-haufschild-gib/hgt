# Whole-orbit cutoffs are actual stopping-cell averages

**Status:** formalized. Four individual Lean checks pass; printed capstones use only
`propext`, `Classical.choice` and `Quot.sound`. No full or umbrella build.

## Actual source and projection

Let $\ell_n=\log((n+1)/n)$ and let $f$ be any finite real linear combination
of the original logarithmic cells. Repeated labels are allowed. The interface
includes `wholeCellProfile c X` with its exact original cell coordinates.
The cutoff $P_A$ retains the root and every Haar label $a<A$ at **every**
dyadic level. No translation orbit is truncated.

The stopping intervals are the original cells with $n<A$, together with
$[j\log2+\log a,j\log2+\log(a+1))$ for $j\ge0$ and $A\le a<2A$.
For an original label $n$, integer halving stops at $(j,a)$ with $a<2A$;
if $n\ge A$, then $a\ge A$. The corresponding original-cell block is
$B_{j,a}=\{2^ja,\ldots,2^j(a+1)-1\}$.

The cutoff is exactly averaging on these blocks. Its physical height is
\[
(P_A f)|_{B_{j,a}}=\sum_{m\in B_{j,a}}\frac{\ell_m}{\ell_a}f_m,
\qquad \sum_{m\in B_{j,a}}\frac{\ell_m}{\ell_a}=1.
\]
All cells $n<2A$ are fixed. The image of an original cell $n$ uses only
labels below $2n$. A finite original horizon $X$ therefore has a finite
head with labels below $2X$.

## Literal BV profiles and exact corrections

The constructed head $h=P_Af$ and tail $t=f-h$ are finite real compact BV
functions, with Hilbert representatives equal to the actual projected
source and its orthogonal tail. They satisfy
\[
\int h=\int f,\qquad \int t=0,\qquad \int ht=0,
\qquad \int f^2=\int h^2+\int t^2,
\qquad \int t^2\le\frac{32\Gamma(f)}{1+\log A}.
\]

Write
\[
S_{\rm even}(f)=2\sum_n\frac{\Lambda(n)}n C_{2\log n}(f),\qquad
\bar S_{\rm even}(f)=S_{\rm even}(f)
 -\tfrac12\left(\int f\right)^2-s_0\int f^2.
\]
Here $s_0$ is the square-source regular symbol at zero. The literal
`squarePrimeSource` includes **all even prime powers**, not only squares.
The identities above prove exact equality of the mixed differences of
$S_{\rm even}$ and $\bar S_{\rm even}$ for $f=h+t$.

## Complete even-power head error

For every $\varepsilon>0$ there is $C_\varepsilon\ge0$, chosen before the
cutoff, finite source-index type, coefficients and horizon, such that
\[
|S_{\rm even}(f)-S_{\rm even}(h)|
\le\varepsilon\bigl(\Gamma(h)+\Gamma(t)\bigr)
 +C_\varepsilon\frac{32\Gamma(f)}{1+\log A}.
\]
The analogous mixed difference has the same form of bound.

Proof mechanism: inverse weighted Haar rotations identify the stopping
projection; logarithmic lengths telescope to averaging weights. The exact
physical realization gives mean preservation and orthogonality. The
centered mixed estimate applied to $(g,g)$, with quadratic homogeneity,
gives $|\bar S_{\rm even}(g)|\le\varepsilon\Gamma(g)+C_\varepsilon\int g^2$
for every compact BV source. Apply it to the zero-mean tail and pay its
remaining constant correction by the original-Gamma square-mass bound.

## Lean evidence

- [EveryGeneratorCutoffStopsAtAnActualDyadicCell](../../../../formal/GaloisForLFunctions/SignedArithmeticHodgeTheory/EveryGeneratorCutoffStopsAtAnActualDyadicCell.lean): `logCellGeneratorHead_single_eq_stopping`, terminal-label bounds and self-adjointness.
- [GeneratorCutoffsAreLogarithmicBlockAverages](../../../../formal/GaloisForLFunctions/SignedArithmeticHodgeTheory/GeneratorCutoffsAreLogarithmicBlockAverages.lean): `logCellGeneratorHead_physicalHeight`, `sum_logCellDyadicBlock_weights`, common stopping blocks and factor-two support.
- [ActualGeneratorHeadsPreserveTheSourceMean](../../../../formal/GaloisForLFunctions/SignedArithmeticHodgeTheory/ActualGeneratorHeadsPreserveTheSourceMean.lean): `realSourceLp_actualGeneratorHead`, `integral_actualGeneratorHead`, `integral_actualGeneratorTail`, `integral_actualGeneratorHead_mul_tail`, `actualGenerator_square_mixed_eq_centered`, `integral_actualGeneratorTail_sq_le`, `exists_actualGenerator_square_mixed_bound`.
- [TheSquareSourceHeadErrorHasOnlyAGammaStabilityCost](../../../../formal/GaloisForLFunctions/SignedArithmeticHodgeTheory/TheSquareSourceHeadErrorHasOnlyAGammaStabilityCost.lean): `exists_centeredSquare_diagonal_gamma_mass`, `exists_actualGenerator_square_head_bound`.

## Exact boundary and next analytic target

The result retains $\Gamma(h)+\Gamma(t)$ explicitly. Uniform stability
$\Gamma(h)+\Gamma(t)\le K\Gamma(f)$ is unproved here. It would convert the
even-power estimate into an arbitrarily small original-Gamma error after
choosing the cutoff; the finite-cutoff estimate itself assumes no stability.

Two concrete approaches are available for research:

- Compare averaged Levy kernels on stopping intervals with their far-end
  mean-graph weights. The corpus supplies a lower bound for arbitrary
  disjoint interval families. Adjacent interval kernels and integrated
  exterior rows still need a uniform upper comparison.
- Prove $\Gamma(t)\le K\sum_{j,a}(1+\log a)|d_{j,a}|^2$ for finite root-free
  Haar expansions. The proved weighted original-source estimate would pay
  the right side. Nested Haar cross terms remain unpaid.

Neither approach is a proved input or a claim that a globally open problem
requires a new field. Repeating a one-level constant does not establish
uniformity in depth.

Ordinary integral preservation does not preserve the two exponential Weil
moments. First-prime transfer, full Gamma/polar comparison, retained-orbit
sign and complete-form bounded index remain distinct obligations. The
all-level retained space remains infinite-dimensional and noncompact.

Working findings and verification records: `logs/signed-arithmetic-hodge-research.log`.
