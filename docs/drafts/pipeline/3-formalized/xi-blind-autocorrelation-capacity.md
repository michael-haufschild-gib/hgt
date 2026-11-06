# Xi blind tests retain a double-exponential correlation tail

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Wall:** Γ56
- **Statement:** A Γ56 strip-factor candidate has no autocorrelation bound
  `|K(x)| ≤ C exp(−a exp(b|x|))` with `a > 0`, `b > 3/2`.

## Mechanism

The entire transform of such a correlation is nonnegative on the real axis.
Each real Xi zero therefore has multiplicity at least two. The unconditional
simple-critical density and reflection force at least
`(4/(3π) + o(1)) R log R` divisor mass in large discs. The proposed tail permits
at most `(2/(πb) + o(1)) R log R`, contradicting `b > 3/2`.

## Positive survivor

Every nonzero even entire transform, nonnegative on the real axis and vanishing
at the simple critical Xi zeros, has disc divisor mass at least
`4 N₀,s(T)` once the disc contains `[-T,T]`. This density constraint uses
positivity, not holomorphy of the factorization quotient. The known single-copy
threshold is `b > 3`; full-divisor transfer cannot be assumed for the exact test.

## Paper proof [PROVED HERE]

Let Φ satisfy `StripDecay Φ d ε C`, `d>1/2`, `ε>0`,
`Φ(−r)=conj Φ(r)` on ℝ, and `Φ(z)=Ξ(z)g(z)` on `|Im z|≤1/2`,
with `g(0)≠0`. Write `K(x)=∫ F(t)F(t−x)dt`, where `F=stripTest Φ`, and
`Ψ(z)=Φ(z)Φ(−z)`. The strip bound for Φ gives the same strip for Ψ,
with decay rate `2ε` and constant `C²`. Fourier inversion and the established
correlation identity give `K=stripTest Ψ` and `H(r)=Ψ(r)=|Φ(r)|²` for
`H(z)=∫ exp(−izx)K(x)dx`. The assumed double-exponential tail makes H entire;
K and H are even. Also `H(0)=|Ξ(0)g(0)|²>0`.

Every positive simple critical Xi ordinate γ is a zero of Φ by pointwise
factorization. Thus H vanishes at ±γ. An entire nonnegative real-axis function
has even order at each real zero. Consequently the divisor of H on
`closedBall(c,T+|c|)` has mass at least `4N₀,s(T)`.

The corpus two-thirds theorem and Riemann–von Mangoldt give, for every positive
η, eventually `N₀,s(T)≥(2/3−η)N(T)` and
`N(T)≥(1/(2π)−η)T log T`. Hence the divisor lower coefficient approaches
`4/(3π)`. The double-exponential Legendre bound and angular Jensen formula give
upper coefficient `2/(πb)`. For `b>3/2` these contradict each other.

The quotient g is used only pointwise, including at zero. No analytic quotient,
RH, or transfer of Xi multiplicities is assumed. Blindness is unnecessary for
this obstruction, so it applies to every candidate in Γ56.

## Novelty and scope

Existing `ThetaTailSimpleCriticalThreshold` counts each critical zero once and
excludes `b>3`. `ThetaTailDivisorCapacity` assumes full multiplicity transfer.
The new bound counts spectral-square zeros twice without that premise.
The positive survivor is the exact `4N₀,s(T)` divisor lower bound.
The [arc square-root construction](w3-single-exact-blind-test.md) supplies a single
exact blind test. The obstruction here retains its weaker, pointwise quotient hypothesis.

## Lean certificate

Module: `GaloisForLFunctions/BiScaleUncertainty/PositiveSpectralXiDivisorCapacity.lean`.
Namespace: `GaloisForLFunctions.BiScaleUncertainty`.

- `four_mul_simpleCriticalCount_le_divisor_of_nonnegative`: positive divisor survivor.
- `ae_eq_zero_of_nonnegativeTransform_fastDoubleExp`: capacity contradiction.
- `stripTest_reflectionProduct`: literal autocorrelation bridge.
- `not_fastDoubleExp_crossCorr_of_stripXiFactor`: Γ56 obstruction.

Direct `lake --old env lean` audit passed. All three main declarations' transitive
axioms are exactly `propext`, `Classical.choice`, `Quot.sound`. Umbrella wired.
No conclusion at `b=3/2`; no claim that this boundary is sharp.
