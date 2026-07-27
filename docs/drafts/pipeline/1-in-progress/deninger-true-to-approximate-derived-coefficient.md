# True-to-approximate derived arithmetic coefficient

- **ID:** `deninger-true-to-approximate-derived-coefficient`
- **Stage:** 1-in-progress
- **Type:** SOURCE CONSTRUCTION CONJECTURE
- **Label:** `DAC_TRUE_TO_APPROXIMATE_DERIVED_COEFFICIENT`
- **Parent:** `deninger-arithmetic-cohomology-construction`
- **Statement:** Deninger's arithmetic cohomology is compactly
  supported hypercohomology of a derived Steinberg coefficient on the
  rational-Witt suspension, not raw cohomology of the approximate
  space.

## Source-locked definition

For the arithmetic curve \(X_0=\operatorname{Spec}\mathbb Z\), let
\(\check X_0(\mathbb C)\) be Deninger's rational-Witt approximation,
let
\[
 X_{\mathrm{Den}}
 =\check X_0(\mathbb C)
   \times_{\mathbb Q_{>0}}\mathbb R_{>0},
\]
and let \(\phi^t\) be translation in the suspension coordinate.

Deninger distinguishes this approximation from a hypothetical true
space \(X_0[\mathbb C]\).  If
\[
 \alpha:X_0[\mathbb C]\longrightarrow\check X_0(\mathbb C)
\]
existed, he says that the missing cohomology would be computed on the
approximation with coefficient \(R\alpha_*\mathcal G\).  This fixes
the type of the source object even without constructing
\(X_0[\mathbb C]\).

Define the sought coefficient directly:
\[
 \mathscr E_{\mathrm{Den}}
 \in
 \operatorname{CAlg}\!\left(
   D_{\mathrm{clc},\mathbb Q}(X_{\mathrm{Den}})
 \right),\qquad
 R\Gamma_{\mathrm{Den},c}
 :=
 R\Gamma_c(X_{\mathrm{Den}},\mathscr E_{\mathrm{Den}}).             \tag{1}
\]
Here `clc` records complete locally convex/nuclear analytic
coefficients.  Equation `(1)`, after maximal Hausdorff reduction, is
the arithmetic cohomology complex.  The flow is induced from
\(\phi^t\); no zeta zero or Gamma factor enters the definition.

## Forced sheaf-level local model

The generic source is not a truncation of global cochains.  On each
cyclotomic component \(\widetilde X_F\) of the suspension cover, set
\[
 \mathscr T_{\widetilde X_F}
 =
 \Omega^\bullet_{\mathrm{cyl},F}
 \widehat\otimes\bigoplus_{n\ge0}\mathbb R(n),
\qquad
 \mathscr P_F
 =
 \operatorname{Free}^{+}_{E_\infty,\mathscr T}
   (H\mathscr V_F(1)[-1]),                                        \tag{2}
\]
using Deninger's equivariant Kummer regulator.  Define
\[
 \widetilde{\mathscr E}_{\mathrm{Den},F}
 :=
 \mathscr T_{\widetilde X_F}
 \mathop{\otimes}^{\mathbb L}_{\mathscr P_F}
 \underline{\mathcal K}^{M}_{F,\mathbb R}.                         \tag{3}
\]
`DAC_LEAFWISE_KUMMER_SHEAF_AMALGAMATION_EXISTENCE` proves that `(2)`--`(3)`
exist functorially as genuine equivariant Tate-graded derived sheaves
with restriction, Galois, power, and weight maps.

The conjectural comparison
`DAC_SHEAFIFIED_UNIT_AMALGAMATION_COMPARISON` identifies chartwise
derived sections of `(3)` with the unit-amalgamated character algebra.
`DAC_CHARACTER_SHAPE_FORMALITY` and
`DAC_ALGEBRAIC_CYCLOTOMIC_MILNOR_AMPLITUDE` then compute that chart
algebra as
\[
 \mathbb R\oplus
 \bigl((F^\times/\mu_\infty)\otimes\mathbb R\bigr)[-1].             \tag{4}
\]
This is a derived-section statement, not a stalk-amplitude statement.
`DAC_KUMMER_SHEAF_STALK_TOR_OBSTRUCTION` proves that the stalks of `(3)`
can have additional higher Tor.

Milnor \(K\), not a global Postnikov truncation, imposes the
Kucharczyk--Scholze Steinberg relations.  A Milnor--Witt/signature
extension is adjoined only at the real orientation boundary.

## Conjecture

`[CONJECTURE] [DAC_TRUE_TO_APPROXIMATE_DERIVED_COEFFICIENT]`

There is a unique contractible-choice class of
\(\mathbb Q_{>0}\)-equivariant derived coefficients
\(\mathscr E_{\mathrm{Den}}\) satisfying:

1. **Raw-to-true map.**  The raw invariant leafwise coefficient maps
   multiplicatively to \(\mathscr E_{\mathrm{Den}}\), and on the
   suspension cover this map is the sheaf-level Kummer
   unit-amalgamation `(2)`--`(3)`.
2. **Finite localization.**  For every finite prime \(p\), the
   Milnor residue extends to a closed morphism into the \(p\)-packet
   coefficient.  Globally these form a two-column localization
   triangle over the regular arithmetic curve.
3. **Real orientation.**  The archimedean boundary is the
   real-linearized Arakelov divisor endpoint, with its
   Milnor--Witt/signature refinement.  It is an added boundary
   orientation, not a replacement for `(2)`.
4. **Frobenius coherence.**  Rational-Witt power push/pull and local
   Frobenius homotopies act coherently on the localization triangle.
5. **Analytic topology.**  The Kummer restriction carries the mixed
   \(L^1/L^2\) and nuclear test scale.  Residues/product formula are
   continuous in the \(L^1\) channel; positive energy is supplied by
   the \(L^2\) channel.
6. **Arithmetic amplitude.**  Compactly supported derived sections,
   including finite and real boundaries, have reduced cohomology only
   in degrees \(0,1,2\).
7. **Leafwise comparison.**  A smooth leafwise resolution of
   \(\mathscr E_{\mathrm{Den}}\) is a quasi-isomorphism, after maximal
   Hausdorff reduction, to the arithmetic Kähler complex.
8. **Endpoints.**
   \[
    H^0_{\mathrm{Den}}\cong\mathbb R,\qquad
    H^2_{\mathrm{Den}}\cong\mathbb R(-1),
   \]
   compatibly with flow, cup product, and trace.
9. **Middle defect.**  \(H^1_{\mathrm{Den}}\) contains the completed
   Steinberg/coarse-descent defect beyond the scalar Kummer regulator;
   the trace formula, not a preloaded zero set, determines its
   spectrum.

## Construction sequence

1. Start from the already constructed equivariant sheaf `(3)` and
   prove `DAC_SHEAFIFIED_UNIT_AMALGAMATION_COMPARISON`; do not
   reconstruct it from global cochains.
2. Use standard finite correspondences only to transport the raw
   rational-Witt coefficient and power maps.
3. Use the Milnor homotopy module and its Rost--Schmid residues for
   the Steinberg-corrected localization differential.
4. Prove finite-flat/qfh descent only in the domains covered by
   Deninger's theorems; prove the integral arithmetic-base case
   separately.
5. Complete Kummer degree one in the mixed \(L^1/L^2\) topology.
6. Adjoin the real Arakelov/signature boundary and totalize.
7. Construct the smooth nuclear leafwise resolution and prove closed
   range/reduced comparison.
8. Only then construct cup--trace duality, Kähler Hodge star,
   Lefschetz trace, and determinant.

## Falsifiers

- Raw \(H^\bullet(X_F,\mathbb Q)\) is not the coefficient: it violates
  Steinberg in degree two.
- The rational-Witt represented presheaf is degree-zero geometry, not
  by itself \(R\alpha_*\mathcal G\).
- The coarse/quotient-stack comparison defect is at most one
  contributor to clause 9; it is not the source definition.
- Base dimension one proves the length of the residue column, not the
  internal amplitude of arbitrary analytic sheaves.
- A Milnor--Witt replacement at every place changes Deninger's
  explicitly requested Milnor correction and therefore requires a
  separate comparison theorem.
- Any coefficient defined using \(\xi\)-zeros, Weil positivity, or a
  Gamma kernel is circular.

## Current status

- Raw rational-Witt space, invariant leafwise sheaf, \(H^0\), prime
  packets, and regulator: Deninger-proved.
- Exact Steinberg defect and raw rational cohomology:
  Kucharczyk--Scholze-proved.
- Equivariant Tate-graded sheaf existence: paper-proved in
  `DAC_LEAFWISE_KUMMER_SHEAF_AMALGAMATION_EXISTENCE`.
- Unit-amalgamated chart algebra and its algebraic cyclotomic
  \([0,1]\)-amplitude: paper-proved in
  `DAC_CHARACTER_SHAPE_FORMALITY` and
  `DAC_ALGEBRAIC_CYCLOTOMIC_MILNOR_AMPLITUDE`.
- Transfer of this computation to coarse-suspension derived sections:
  open in `DAC_SHEAFIFIED_UNIT_AMALGAMATION_COMPARISON`; no stalkwise
  amplitude is claimed.
- Global arithmetic sheafification, localization, real gluing,
  reduced analytic comparison, and non-scalar middle cohomology:
  open.

**Verdict:** `ACTIVE SOURCE OBJECT; COVER SHEAF CONSTRUCTED,
SHEAFIFIED SECTION COMPARISON AND ARITHMETIC GLUING OPEN`.

## References

- Christopher Deninger, *Dynamical systems for arithmetic schemes*:
  https://arxiv.org/abs/1807.06400
- Robert A. Kucharczyk and Peter Scholze, *Topological realisations of
  absolute Galois groups*: https://arxiv.org/abs/1609.04717
- Martin Gallauer, *tt-geometry of Tate motives over algebraically
  closed fields*: https://arxiv.org/abs/1708.00834

## Log

- 2026-07-26 — Promoted Deninger's explicit
  \(R\alpha_*\mathcal G\) correction to the source definition and made
  the exact Steinberg defect its generic local model.
- 2026-07-27 — Removed the global-Postnikov type error.  The source is
  now the already constructed equivariant leafwise unit-amalgamated
  sheaf; chartwise two-term Milnor cohomology is only its conjectural
  derived-section comparison.
