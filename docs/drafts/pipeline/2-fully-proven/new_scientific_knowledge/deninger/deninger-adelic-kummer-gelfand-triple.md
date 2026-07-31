# Adelic Kummer rigged Hilbert triple

- **ID:** `deninger-adelic-kummer-gelfand-triple`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Label:** `DAC_ADELIC_KUMMER_GELFAND_TRIPLE`
- **Parent:** `deninger-adelic-l1-l2-rost-schmid-hodge-coefficient`
- **Statement:** mixed \(L^1/L^2\) completion of logarithmic Kummer
  functions is a canonical dense test space in the adelic \(L^2\)
  Hilbert space, with continuous product-formula topology and
  distribution dual.

## Setup

Let \((Y,\lambda)\) be the Allcock--Vaaler place space and
\(\mathcal F\) the rational vector space of logarithmic Kummer
functions.  Give \(\mathcal F\) the norm
\[
 \|f\|_E=\|f\|_1+\|f\|_2                                           \tag{1}
\]
and let \(E\) be its completion.  Let
\[
 H=L^2(Y,\lambda).
\]

## Theorem

`[PROVED HERE] [DAC_ADELIC_KUMMER_GELFAND_TRIPLE]`

There are canonical continuous dense injections
\[
 E\xhookrightarrow{i}H\xhookrightarrow{j}E',                      \tag{2}
\]
where
\[
 (jh)(e)=\langle i(e),h\rangle_{L^2}.                              \tag{3}
\]
The map \(j\) is injective.  Thus `(2)` is a real rigged Hilbert
triple.

Let
\[
 I(f)=\int_Yf\,d\lambda
\]
on \(L^1\cap L^2\).  Then
\[
 |I(f)|\leq\|f\|_1\leq\|f\|_E,                                    \tag{4}
\]
and the image of \(E\) lies in the closed product-formula kernel
\(\ker I\).  The arithmetic constraint is therefore retained on the
test space even though its image is dense in \(H\).

Normalized field-norm projections preserve `(2)` and are contractions
on \(E\) and \(H\).  The \(s\)-twisted power map acts on the Kummer
core by \(n^{1-s}\); at \(s=\tfrac12\) it scales the \(H\)-pairing by
\(n\) and preserves \(E\).

## Proof

The norm `(1)` dominates the \(L^2\)-norm, so the inclusion of
\(\mathcal F\) into \(H\) extends continuously to \(i:E\to H\).
If an \(E\)-Cauchy sequence converges to zero in \(L^2\), it also
converges in \(L^1\); uniqueness in measure identifies both limits,
so \(i\) is injective.

Allcock--Vaaler prove that \(\mathcal F\) is dense in \(L^2\).
Since \(\mathcal F\subset i(E)\), the image of \(i\) is dense.

Cauchy--Schwarz and \(\|e\|_2\leq\|e\|_E\) give
\[
 |(jh)(e)|
 \leq\|h\|_2\|e\|_2
 \leq\|h\|_2\|e\|_E,
\]
so `(3)` defines a continuous injection \(j:H\to E'\).  If
\(jh=0\), then \(h\) is orthogonal to the dense subspace \(i(E)\), so
\(h=0\).

Inequality `(4)` proves continuity of the product-formula functional on
the ambient mixed space.  It vanishes on every \(f_\alpha\); continuity
therefore makes it vanish on their \(E\)-closure.  The norm and power
claims follow from `DAC_ADELIC_PLACE_AVERAGE_RESIDUE` and
`DAC_NAIVE_ADELIC_L2_KUMMER_COMPLETION_NO_GO`.

## Arithmetic interpretation

- \(E\): source test/cochain topology retaining principal-divisor
  reciprocity and residue summability;
- \(H\): positive local Kummer energy space;
- \(E'\): distributional coefficient space in which trace and
  fixed-point functionals may live.

This separates Deninger's distributional Lefschetz topology from his
Hodge Hilbert topology.  It does not identify \(H\) with global
arithmetic \(H^1\): the centered Kummer power action is still scalar,
and nontrivial spectrum must come from the non-scalar part of
Deninger's true-to-approximate derived coefficient.  Frobenius
coherence and coarse/stack defects are candidate summands only.

## Limits

- \(E=L^1\cap L^2\) is not automatically nuclear.
- The theorem gives no global sheafification, closed Rost--Schmid
  differential, Kähler leaf, or Hodge star.
- Extension of the rigged triple from Kummer functions to the full
  Steinberg-corrected Milnor coefficient, plus its separate real
  Milnor--Witt orientation, is conjectural.

## Gates

- [x] complete paper proof
- [ ] Lean formalization of the abstract rigged-Hilbert construction
- [ ] source specialization to the formalized Allcock--Vaaler measure

## References

- Daniel Allcock and Jeffrey D. Vaaler, *A Banach space determined by
  the Weil height*: https://arxiv.org/abs/0808.1038
- Paul Fili and Zachary Miner, *Orthogonal decomposition of the space
  of algebraic numbers and Lehmer's problem*:
  https://arxiv.org/abs/0911.1975

## Log

- 2026-07-26 — Proved the mixed coefficient is the canonical
  test/Hilbert/distribution triple forced by \(L^1\) product formula and
  \(L^2\) positivity.
