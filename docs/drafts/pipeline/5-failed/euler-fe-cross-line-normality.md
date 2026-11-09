# Ordinary high translates cannot cross the critical line

- **ID:** euler-fe-cross-line-normality.
- **Stage:** 5-failed.
- **Type:** NO-GO WITH POSITIVE SURVIVOR.
- **Failed route:** propagate ordinary ζ-returns through a connected boundedness
  domain crossing the critical line and reaching the Euler half-plane.

## Obstruction

For every real sequence `τ_j→+∞`, every connected open domain `U⊆{Im s>0}`
meeting `Re s>1` on which `ζ(s+iτ_j)` is locally bounded satisfies
`U⊆{Re s>½}`. Phase alignment is unnecessary. The whole-upper-quadrant premise
in `ArithmeticAuxiliaryDynamics/ReturnsAreReturnsOfThePrimes.lean` is therefore
impossible for escaping shifts, independently of zero location.

At a reflected disc crossing the line, boundedness and Gamma decay force a zero
limit on its right half. Vitali and analytic uniqueness propagate zero through
`U`, contradicting the uniform Euler lower bound at any fixed real part above one.

## Positive survivor

Conductor normalization gives an actual reflected-height law. With
`R(s)=1−conj(s)` and `N_t(s)=exp((s−½)log(t/(2π)))/χ(½+it)`,

    sup_{0<Re s<1, |s−½|≤D}
      |N_t(s)ζ(s+it)−conj(ζ(R(s)+it))| ≤ C_D t^(−1/4) → 0.

This holds for every radius `D≥0`, without a boundedness or recurrence premise.
The exact functional equation factors the error into a normalized Gamma error
`O_D(t⁻¹)` and an actual reflected ζ-profile `O(t^(3/4))`.

Both the obstruction and positive survivor have complete paper proofs and Lean
formalizations in `EulerFETransportTheory/TheWholeQuadrantCannotSupportReturns.lean`
and `EulerFETransportTheory/TheNormalizedHeightReflection.lean`, with only the
three standard axioms. Exact declarations and proof:
`../3-formalized/euler-fe-height-reflection-normalization.md`.

The survivor retains the same height. Recurrence on smaller domains strictly
right of the line, same-depth replication, `LinAt C`, and AAL remain unresolved.
