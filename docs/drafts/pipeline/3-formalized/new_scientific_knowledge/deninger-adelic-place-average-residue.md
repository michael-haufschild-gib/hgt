# Adelic place-average residue identity

- **ID:** `deninger-adelic-place-average-residue`
- **Stage:** 3-formalized
- **Type:** LITERATURE THEOREM / PAPER COROLLARY · LEAN 4 THEOREM
- **Label:** `DAC_ADELIC_PLACE_AVERAGE_RESIDUE`
- **Parent:** `deninger-adelic-l1-l2-rost-schmid-hodge-coefficient`
- **Statement:** Allcock--Vaaler place-component averages are exactly
  normalized Milnor \(K_1\) valuation residues, and normalized field
  norms act contractively in the mixed \(L^1/L^2\) topology.
- **Lean module:**
  `GaloisForLFunctions.RHTower.DeningerAdelicPlaceAverageResidue`

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

## Formalized statement

All declarations live in the `RHTower` namespace.  Mathlib's absolute
value at a finite place, `NumberField.HeightOneSpectrum.adicAbv`, is the
\(Nv\)-normalized one; the card's \(|\cdot|_v\) is the \(\mathbb Q_p\)-normalized
one.  Both appear, and the local-degree factor between them is the content of
the specialization gate.

Local residue coordinate:

- `deningerPlaceOrd v α` is \(\operatorname{ord}_v(\alpha)\), defined from the
  \(v\)-adic valuation, with `deningerValuation_eq_exp` :
  `v.valuation K α = exp (-ord_v α)` for `α ≠ 0`.
- `deningerAdicAbv_eq_zpow` : \(|\alpha|_v^{Nv}=Nv^{-\operatorname{ord}_v\alpha}\).
- `deningerLog_adicAbv` : \(\log|\alpha|_v^{Nv}=-\operatorname{ord}_v(\alpha)\log Nv\).

Local-degree specialization (the card's open Lean gate):

- `deningerLogAbsQp p e n` is \(-\frac ne\log p\), the \(\mathbb Q_p\)-normalized
  logarithm.
- `deningerLog_absNorm_eq_localDegree_mul` and
  `deningerLog_adicAbv_eq_localDegree_mul` :
  \(-\operatorname{ord}_v(\alpha)\log Nv=e_vf_v\cdot\log|\alpha|_v\) whenever
  \(Nv=p^{f_v}\) and \(e_v\neq0\).
- `deningerAbsNorm_eq_pow_inertiaDeg` : \(Nv=p^{f_v}\) with mathlib's
  `Ideal.inertiaDeg'`, for a prime lying over `span {(p : ℤ)}`.
- `deningerLog_adicAbv_eq_ramificationIdx_mul` is the combined statement with
  mathlib's own `Ideal.ramificationIdx'` and `Ideal.inertiaDeg'`; nonvanishing of
  the ramification index is discharged, not assumed.

Place average `(2)` and residue recovery `(3)`:

- `deningerPlaceAverage_eq` :
  \(\frac{e_vf_v}{d}\log|\alpha|_v=-\frac{\operatorname{ord}_v\alpha}{d}\log Nv\).
- `deningerPlaceAverage_setIntegral` : the integral of a function constant on a
  measurable set of prescribed measure.
- `deningerPlaceAverage_setIntegral_eq` : the two together, i.e. `(2)` for any
  measure space whose fibre \(Y(K,v)\) carries the Allcock--Vaaler mass
  \(e_vf_v/d\).
- `deningerOrd_eq_of_placeAverage` : `(3)`.

Product formula `(4)`:

- `deningerLog_prod_abs_eq_zero` and `deningerLog_prod_abs_eq_zero'` : the
  additive form of mathlib's `NumberField.prod_abs_eq_one`, over a finite set
  containing the multiplicative support and over all finite places.
- `deningerSum_placeAverage_eq_zero` and `deningerSum_placeAverage_eq_zero'` :
  the same normalized by \(d\), i.e. the place-averages of a nonzero element sum
  to zero.

Mixed contraction `(6)`:

- `deningerMixed_contraction` : an operator contracting two seminorms contracts
  their sum.

### What is hypothesis and what is theorem

The Allcock--Vaaler normalization `(1)` is a property of a construction outside
this file, so it enters `deningerPlaceAverage_setIntegral_eq` as a hypothesis on
the given measure (`μ Y = ENNReal.ofReal (e * f / d)`), together with constancy
of \(f_\alpha\) on the fibre.  Under those two hypotheses the conclusion is
proved outright.  Everything else — the local residue coordinate, the
local-degree specialization, `(2)`, `(3)`, `(4)` — is proved with no arithmetic
hypothesis beyond `α ≠ 0` and primality of `p`.

Inequality `(5)` is the cited Fili--Miner theorem and is *not* proved here; the
card never claimed it.  Only its consequence `(6)` is formalized, as the
two-seminorm statement it actually is.

## Verification

- Direct command:
  `lake env lean GaloisForLFunctions/RHTower/DeningerAdelicPlaceAverageResidue.lean`
- Result: passed with no errors and no warnings.
- Scratch `#print axioms` on all 20 declarations: only the Lean/mathlib standard
  `propext`, `Classical.choice`, and `Quot.sound`.
- No `sorry`, `admit`, `axiom`, `opaque`, or `unsafe` declaration.
- Imported by the `GaloisForLFunctions.RHTower` umbrella.

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
- [x] Lean formalization of number-field local-degree specialization

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
- 2026-08-01 — Formalized `(2)`, `(3)`, `(4)`, `(6)` and the local-degree
  specialization unconditionally in Lean 4.
