# Adelic place-average residue identity

- **ID:** `deninger-adelic-place-average-residue`
- **Stage:** 2-fully-proven
- **Type:** LITERATURE THEOREM / PAPER COROLLARY
- **Label:** `DAC_ADELIC_PLACE_AVERAGE_RESIDUE`
- **Parent:** `deninger-adelic-l1-l2-rost-schmid-hodge-coefficient`
- **Statement:** Allcock--Vaaler place-component averages are exactly
  normalized Milnor \(K_1\) valuation residues, and normalized field
  norms act contractively in the mixed \(L^1/L^2\) topology.

## Setup

Let \(K/\mathbb Q\) be a number field, \(v\) a place, and
\[
 Y(K,v)=\{y\in Y:y|_K=v\}.
\]
Allcock--Vaaler's measure satisfies
\[
 \lambda(Y(K,v))
 =\frac{[K_v:\mathbb Q_v]}{[K:\mathbb Q]}.                         \tag{1}
\]
For \(\alpha\in K^\times\), the logarithmic Kummer function
\[
 f_\alpha(y)=\log\|\alpha\|_y
\]
is constant on \(Y(K,v)\), with value \(\log|\alpha|_v\).

## Theorem

`[PROVED HERE] [DAC_ADELIC_PLACE_AVERAGE_RESIDUE]`

Write \(d=[K:\mathbb Q]\).  If \(v\mid p\) is finite, with ramification
degree \(e_v\), residue degree \(f_v\), and
\(Nv=p^{f_v}\), then
\[
\begin{aligned}
 \int_{Y(K,v)} f_\alpha\,d\lambda
 &=\frac{e_vf_v}{d}\log|\alpha|_v\\
 &=-\frac{\operatorname{ord}_v(\alpha)}{d}\log Nv.                 \tag{2}
\end{aligned}
\]
Equivalently,
\[
 \operatorname{ord}_v(\alpha)
 =-\frac d{\log Nv}
    \int_{Y(K,v)} f_\alpha\,d\lambda.                              \tag{3}
\]
Thus the finite Rost--Schmid boundary on Milnor \(K_1\) is recovered
from place-component integration.

The product formula becomes
\[
 \sum_{v\in M_K}\int_{Y(K,v)}f_\alpha\,d\lambda=0,                 \tag{4}
\]
where only finitely many terms are nonzero.  Hence the archimedean
component is the negative of the finite residue sum.

For every subfield \(L\), Fili--Miner's projection \(P_L\), obtained by
averaging the Galois action over
\(\operatorname{Gal}(\overline{\mathbb Q}/L)\), is normalized
field norm on Kummer functions and satisfies
\[
 \|P_Lf\|_p\leq\|f\|_p
 \quad(1\leq p\leq\infty).                                        \tag{5}
\]
For \(p=2\), it is the orthogonal projection onto the \(L\)-defined
subspace.  Therefore
\[
 \|P_Lf\|_1+\|P_Lf\|_2
 \leq \|f\|_1+\|f\|_2,                                             \tag{6}
\]
so normalized norms extend to the mixed Kummer completion.

## Proof

For `(2)`, constancy of \(f_\alpha\) on \(Y(K,v)\) and `(1)` give the
first equality.  The absolute value extending the standard
\(p\)-adic one satisfies
\[
 \log|\alpha|_v
 =-\frac{\operatorname{ord}_v(\alpha)}{e_v}\log p.
\]
Substitution and \([K_v:\mathbb Q_p]=e_vf_v\) give the second equality.
Equation `(3)` is a rearrangement.  Summing `(2)` together with the
archimedean components is the usual product formula, proving `(4)`.

Fili--Miner identify \(P_L\) with normalized algebraic norm and prove
that it is a norm-one projection for every \(L^p\); in \(L^2\) it is
orthogonal.  Adding the \(p=1\) and \(p=2\) inequalities proves `(6)`.

## Scope

This theorem constructs the exact local \(K_1\) residue coordinate and
the mixed-topology field-norm maps.  It does not prove:

- sheafification on Deninger's rational-Witt quotient;
- compatibility with higher Milnor--Witt determinant twists;
- closedness of the global Rost--Schmid differential;
- positivity or spectral nontriviality of its cohomology.

## Gates

- [x] Allcock--Vaaler measure normalization
- [x] local residue formula
- [x] product-formula boundary
- [x] normalized-norm mixed contraction
- [ ] Lean formalization of number-field local-degree specialization

## References

- Daniel Allcock and Jeffrey D. Vaaler, *A Banach space determined by
  the Weil height*, equations (1.7)--(1.11):
  https://arxiv.org/abs/0808.1038
- Paul Fili and Zachary Miner, *Orthogonal decomposition of the space
  of algebraic numbers and Lehmer's problem*, Proposition 2.11 and
  Proposition 2.13: https://arxiv.org/abs/0911.1975

## Log

- 2026-07-26 — Extracted the exact valuation-residue formula and mixed
  norm contraction from the primary place-space construction.
