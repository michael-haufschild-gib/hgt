# Full A1 localization of the rational-Witt coordinate

- **ID:** `deninger-a1-localized-rational-witt-coefficient`
- **Stage:** 5-failed
- **Type:** FALSIFIED
- **Parent:** `deninger-derived-mw-rational-witt-coefficient`
- **Failed statement:** Applying the Suslin/\(\mathbb A^1\)-localization functor to the
  reduced correspondence object represented by
  \(\mathbb A^1/\{0\}\) produces Deninger's missing derived coefficient.

## Exact contraction

Let
\[
 \widetilde W^0(X)=
 \widetilde{\operatorname{Corr}}(X,\mathbb A^1)/
 \widetilde{\operatorname{Corr}}(X,\{0\}).
\]
The target-scaling map
\[
 H:\mathbb A^1_t\times\mathbb A^1_s\longrightarrow\mathbb A^1_t,
 \qquad H(t,s)=st
\]
is an algebraic homotopy from the identity at \(s=1\) to the zero section at \(s=0\).
For every finite correspondence \(Z\subset X\times\mathbb A^1_t\), the graph family
\[
 \{(x,s,u): (x,t)\in Z,\ u=st\}
 \subset X\times\mathbb A^1_s\times\mathbb A^1_u
\]
remains finite over \(X\times\mathbb A^1_s\).  Hence it defines a valid Suslin homotopy.
At \(s=0\) its target lies in the zero section, which is zero in \(\widetilde W^0\).
Therefore the identity of the reduced correspondence object is Suslin-chain-homotopic to
zero:
\[
 L_{\mathbb A^1}\widetilde W^0\simeq0.                                \tag{1}
\]
The same contraction applies after adding MW orientation coefficients: scaling changes the
target map, not finiteness of the source family, and the endpoint still factors through the
quotiented zero section.

Consequently
\[
 \operatorname{Tot}C_{\mathrm{RS}}
 \bigl(a_f C_*^{\mathrm{Sus}}\widetilde W^0\bigr)
\]
cannot recover \(W_{\mathrm{rat}}\) in degree zero; it is already contractible before any
rank correction.

## Strongest positive survivor

`[CONJECTURE] [DAC_SELECTIVE_STEINBERG_RESIDUE_ENVELOPE]`

Do not impose full \(\mathbb A^1\)-invariance on Deninger's coordinate.  Start from derived
finite-topology sheafification of MW correspondences and construct a
**multiplicative arithmetic bar--residue envelope**
\[
 M_{\mathrm{res}}
 =
 \mathfrak R_{\mathrm{MW}}^{\mathrm{mult}}
 \bigl(Ra_f\widetilde W^0\bigr),                                      \tag{2}
\]
whose differential is generated only by:

1. finite-topology descent;
2. normalized multiplicative bar faces;
3. MW codimension residues and Gysin maps.

The functor \(\mathfrak R_{\mathrm{MW}}^{\mathrm{mult}}\) is forbidden to invert the scaling
homotopy \(t\mapsto st\).  The Steinberg defects occur as a family of positive-degree
cocycles
\[
 \sigma_{U,a}:\mathbbm1[-2]\longrightarrow M_{\mathrm{res}},
 \qquad a,1-a\in\mathcal O(U)^\times .
\]
Let \(S_{\mathrm{St}}\) be their coproduct and set
\[
 M_{\mathrm{St}}
 :=
 M_{\mathrm{res}}
 \mathop{\otimes}^{\mathbb L}_{
   \operatorname{Free}_{E_\infty}^{+}(S_{\mathrm{St}})}
 \mathbbm1.                                                           \tag{3}
\]
This selectively supplies coherent null-homotopies for the Steinberg cocycles.  Because
\(S_{\mathrm{St}}\) is positive-degree, the connective bar spectral sequence predicts
\[
 H^0(M_{\mathrm{St}})\cong H^0(M_{\mathrm{res}}),
\]
so Deninger's rational-Witt coordinate survives.  The separate derived rank quotient then
removes degree-zero Witt coefficients without touching the ordinary channel.

## Survivor obligations

1. Construct \(\mathfrak R_{\mathrm{MW}}^{\mathrm{mult}}\) before
   \(\mathbb A^1\)-localization and prove its \(H^0\) is the MW finite-correspondence sheaf.
2. Construct the cocycles \(\sigma_{U,a}\), including functorial and Čech coherence.
3. Prove `(3)` is compatible with MW residues, products, and power-map Gysin operations.
4. Prove positive-degree cell attachment preserves \(H^0\).
5. Apply the multiplicative derived rank quotient and prove the ordinary
   rational-Witt \(H^0\) comparison.
6. Prove the resulting higher complex satisfies arithmetic duality; positivity still comes
   from the real boundary.

## Status

Full Suslin/\(\mathbb A^1\)-localization is retired.  The contraction `(1)` is unconditional
and occurs before any analytic or Hodge issue.  Selective positive-degree Steinberg cell
attachment `(2)`--`(3)` is the active survivor.

## References

- Christopher Deninger, *Rational Witt vectors and associated sheaves*,
  Theorem 5.1:
  https://arxiv.org/abs/2508.05329
- Jacob Lurie, *Higher Algebra*:
  https://www.math.ias.edu/~lurie/papers/HA.pdf

## Log

- 2026-07-26 — target scaling \(t\mapsto st\) shown to contract the reduced represented
  coordinate after Suslin localization; selective Steinberg bar--residue envelope extracted.
