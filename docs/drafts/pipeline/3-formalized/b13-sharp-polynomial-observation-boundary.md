# Sharp polynomial observation boundary

- **Obstacle:** B13.
- **Stage:** 3-formalized
- **Type:** THEOREM

## Statements

Put `x=Re ρ−σ`, `φ(t)=−π/2+1/t`, and
`C(x)=sqrt(2π)/2 · (1/2)^((x−1)/2) · exp(−1/2)>0`.
For every eventually positive radius schedule `y(t)`,

`|Kφ(y(t),ρ−σ−it)| / [y(t)^(−x/2)t^((x−1)/2)] → C(x)`.

The constant is independent of the ordinate and radius schedule. With
`y=t^(−A)` and degree-`d` spacing `h=t^(−κ)`, the contracted mode satisfies

`|h^d Kφ| / t^E → C(x)`, where `E=((A+1)x−1)/2−dκ`.

Its modulus tends to infinity exactly when `E>0`; it tends to zero for
`E<0` and to `C(x)` for `E=0`.

For an actual finite exceptional profile, every `A` above its proved
recovery threshold gives the literal prime-filter limit

`|A_h^rot(t)| / t^E → L=|−mρ(ρ−1)Π_{ρq≠ρ}(ρ−ρq)| C(x)>0`.

Thus the complete prime filter has the same trichotomy. Choosing
`κ=((A+1)x−1)/(2d)` for sufficiently large `A` gives the same positive
limiting modulus `L` for every such `A`. An unconditional AAL-or-critical-
levels theorem obtains the actual finite profile and top zeros.

## Proof

Set `τ=(t−Im ρ)/2`. Exact vertical Stirling gives
`|Γ(x/2+iτ)|/[τ^((x−1)/2)exp(−πτ/2)]→sqrt(2π)`.
Conjugation gives the negative-height Gamma value. The rotation contributes
`exp(πτ/2−τ/t)`, canceling the exponential Gamma decay exactly. Radius
cancels from the normalized modulus, and `τ/t→1/2` gives `C(x)`.
Combining real powers gives `E`; positivity of `C(x)` gives all three cases
and necessity of the growth condition.

The existing complete divisor-reading limit is nonzero for every positive
spacing tending to zero. Multiply its modulus by the exact normalized-mode
limit to obtain `L`. The critical spacing has positive exponent once
`A≥2/x`; it makes `E=0`. Failure of AAL supplies a finite isolated top,
so these steps yield the unconditional dichotomy without a missing
analytic hypothesis.

## Short-scale obstruction and positive survivor

For `0<x<1/2`, every eventually bounded spacing `0≤h(t)≤1` and radius
`y(t)≥1/t` give `h(t)^d Kφ(y(t),ρ−σ−it)→0`.
Indeed `y^(−x/2)≤t^(x/2)` and the comparison mode is `O(t^(x−1/2))`.
This includes all `A≤1` at polynomial radius, where the Gaussian damping
scale `t^((A+1)/2)` is at most height.

The obstruction concerns raw selected-mode growth only. It neither proves
short-scale prime-filter decay nor excludes estimates relative to a
decaying mode. Polynomial damping and long-sum cancellation remain open.
The positive survivor is the exact modulus law, its necessary-and-sufficient
growth threshold, and the fixed positive critical modulus of the literal
prime filter.

## Lean declarations

Module: `ExceptionalLayerTheory/TheSharpPolynomialObservationBoundary.lean`.

- `tendsto_boundary_mode_normalized_modulus`
- `tendsto_polynomial_mode_modulus`
- `polynomial_mode_growth_iff`
- `tendsto_polynomial_mode_critical`
- `boundary_mode_zero_of_short_damping_scale`
- `exists_sharp_polynomial_prime_modulus_threshold`
- `exists_polynomial_prime_modulus_trichotomy`
- `asymptoticAbscissaLaw_or_critical_polynomial_prime_levels`

Inputs: exact `SelbergClass.DegreeOne.tendsto_Gamma_div_stirlingShape` and
complete divisor recovery in `PolynomialDampingReadsTheDivisor.lean`.
No stronger independent arithmetic upper bound follows. B13 remains open.

## Verification

Direct `lake --old env lean` source audit passes without warnings.
All eight printed transitive axiom lists contain only `propext`,
`Classical.choice`, and `Quot.sound`. Imported by `ExceptionalLayerTheory.lean`.
