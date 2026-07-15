# Formal hypertranscendence of the inverse-Gamma clock observation germ

- **ID:** `gamma-inverse-pole-clock-observability`
- **Stage:** 3-formalized
- **Type:** BRIDGE THEOREM
- **Scientific status:** `[PROVED IN LEAN] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Lean:** `GaloisForLFunctions.HTGeometry.GammaInversePoleClockObservability`

## Statement

At the pole `-n`, write the normalized inverse branch as

\[
 B_n(T)=T+\sum_{j\ge 0}b_{n,j}T^{j+2}.
\]

After removing the fixed origin and unit tangent, its nonlinear clock observation is

\[
 \mathcal C_n(T)=\frac{B_n(T)-T}{T^2}
   =\sum_{j\ge0}b_{n,j}T^j.
\]

View every coefficient `n ↦ b_{n,j}` in the eventual pole-index germ ring.  For every finite
differential order and every nonzero polynomial differential observable `P`,

\[
 P\bigl(T,\mathcal C,\partial_T\mathcal C,\ldots,
   \partial_T^r\mathcal C\bigr)\ne0
\]

as a formal power series over that germ ring.

## Proof

`GammaInversePoleBranchCoefficientFreeness.lean` proves that the complete coefficient family
`(b_j)_{j≥0}` is algebraically independent over `C`.  The general theorem
`aeval_formalJetsOver_ne_zero_of_coeff_algebraicIndependent` says that a power series with a free
coefficient family satisfies no finite algebraic differential relation.  Applying it to
`PowerSeries.mk gammaInversePoleBranchCoefficientGerm` proves the statement.

## Meaning

This is an observability statement, not an evolution statement.  Derivative order is the
resolution of the clock observation algebra.  Every finite resolution exposes another free
coordinate; there is no finite saturation.

The theorem is a mechanically exact consumer of the stronger coefficient-freeness theorem.  It
does not add independent scientific content and is therefore classified as a formal bridge.

## Lean surface

- `gammaInversePoleClockObservableFormalGerm`
- `gammaInversePoleClockObservableFormalGerm_formallyHypertranscendental`

The exact target build and direct file elaboration pass.  No full build or numerical computation
was run.

## Limits

1. This theorem concerns the normalized inverse-branch clock fiber, not yet the actual moving-base
   Gamma jet groupoid.
2. It does not prove that the clock algebra is disjoint from the differential field of the lower
   Gamma iterates.
3. The actual positive Gamma-iterate values and first derivatives are already jointly algebraically
   independent by `algebraicIndependent_gammaIterateInfiniteFirstJetFamily`; this bridge does not
   extend that theorem to second and higher joint jets.
4. It has no direct RH localization or positivity consequence.
