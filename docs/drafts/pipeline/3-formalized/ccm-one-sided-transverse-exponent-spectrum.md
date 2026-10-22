# Exact one-sided transverse exponent spectrum of the CCM rectangular observable

- **ID:** `ccm-one-sided-transverse-exponent-spectrum`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Scientific register:** `[PROVED]`; `[NOVELTY-PENDING]`
- **Route:** Connes--Consani--Moscovici fixed-window Weil observable

## Main theorem

Fix a window width (L>0), and let

\[
q_L(n)=\operatorname{Re}\mathcal W_\Xi
  \left(F_{L,\frac12\log n},F_{L,\frac12\log n}\right).
\]

For (alpha\ge0), call (alpha) admissible when there are (C\ge0) and an admissible cutoff
(N) such that

\[
q_L(n)\ge -C n^\alpha\qquad(n\ge N).
\]

Let

\[
\delta_*=
\sup_{\Xi(\rho)=0,\ \Re\rho>1/2}
  \left(\Re\rho-\frac12\right),
\]

with the empty supremum normalized to (0).  Then the admissible exponent spectrum is exactly

\[
\boxed{\ [\delta_*,\infty)\ }.
\]

Equivalently, for every (alpha\ge0),

\[
\exists C,N\ \forall n\ge N,
\quad q_L(n)\ge-Cn^\alpha
\quad\Longleftrightarrow\quad
\forall\rho,\ \Xi(\rho)=0\Longrightarrow
\Re\rho\le\frac12+\alpha.
\]

The same statement has the open zero-free form

\[
\exists C,N\ \forall n\ge N,
\quad q_L(n)\ge-Cn^\alpha
\quad\Longleftrightarrow\quad
\Xi(\rho)\ne0
\quad\text{whenever}\quad
\Re\rho>\frac12+\alpha.
\]

This is a positive carrier law: the polynomial lower-loss spectrum of one actual fixed-window
observable is the horizontal support function of the right Xi divisor.

## Formal theorem surface

The unconditional formalization is

- `formal/GaloisForLFunctions/RHTower/CCM/CCMRectangularOneSidedTransverseExponent.lean`.

Principal declarations:

- `xiRectangularWeilTailPowerLower_iff_transverseSup_le`;
- `xiRectangularWeilTailPowerLower_iff_all_rightZeros_le`;
- `xiRectangularWeilTailPowerLower_iff_all_xiZeros_re_le`;
- `xiRectangularWeilTailPowerLower_iff_xi_zeroFree_right_halfPlane`;
- `xiRectangularWeilTailPowerLower_iff_transverseSup_le_global`;
- `xiRectangularOneSidedExponentSet_eq_Ici_transverseSup`.

The exact module build passes.  Each theorem depends only on `propext`, `Classical.choice`, and
`Quot.sound`.  The formal lint gate and generated-index check pass; there is no project axiom,
`sorry`, `admit`, `opaque`, `unsafe` declaration, or abstract proposition replacing analytic
content.

## Proof architecture

The forward implication is the quantitative Landau direction.  An eventual observable lower
budget is transported across the bounded rectangular remainder to the positive-transverse
Dirichlet carrier.  A right zero with displacement greater than (alpha) would then force a
contradictory dominant coefficient.

For the reverse implication, the sharp transverse growth estimate bounds the norm of the actual
fixed-window Weil value by (K n^{\delta_*}).  If (delta_*\le\alpha), monotonicity of real powers
gives a lower budget (q_L(n)\ge-Kn^\alpha).  When the right divisor is empty, RH follows and Weil
positivity supplies the zero budget.  Taking both cases yields the exact closed-ray spectrum.

## Exact limitation

The theorem classifies the information contained in the fixed-window observable.  It does not
prove that exponent (0) is admissible; that endpoint assertion is equivalent to RH.  A successful
CCM construction must therefore prove, from its prime--Gamma/Sonin source rather than from the Xi
divisor, that its selected cofinal observable section has exponent (0).

## Novelty and significance gate

- The one-sided dominant-coefficient mechanism has classical Landau parentage.
- The exact closed-ray spectrum for the actual fixed-window Xi--Weil observable, including the
  converse upper budget and the unconditional empty-divisor case, was not located as a named
  theorem in the audited literature.
- Current internal score: **86/100**.  It materially strengthens the fixed-window tomography
  theorem but does not by itself clear the 90/100 new-science threshold because the endpoint
  remains the Xi divisor displacement and the proof mechanisms have classical parents.
