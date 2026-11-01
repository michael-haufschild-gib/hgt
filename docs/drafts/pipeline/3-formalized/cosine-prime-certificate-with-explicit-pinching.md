# The actual cosine prime certificate through bandwidth two

- **Stage:** 3-formalized
- **Type:** THEOREM / ACTUAL PRIME-GRAM TRANSPORT
- **Route:** Argon §4.1.
- **Parents:** [Actual pinching](../3-formalized/trans-threshold-cosine-pinching-credit.md), [cosine coefficient](../3-formalized/cosine-shape-one-improves-trans-threshold-calibration.md).

## Theorem

For every fixed `0<λ≤2` and ε>0, eventually

`(Hcos(λ)+δλ−ε) N(T,2T) − Sλ(T) ≤ N0simple(T,2T)`,

where the literal shape-one cosine prime surplus is
`Sλ(T)=frobSurplus(Q.toSetting T,Q.localFun T)/(Q.a T*Q.L T)²`,
`Q=zetaCosineParams λ T`, and
`δλ=1/[200(10+720π²λ²)²]`.

The explicit specializations have coefficients
`3/4+79/1250+δ(4/3)` and `5/6+43/3750+δ(2)` before ε.
No upper bound on S is assumed or proved. Thus neither a 75% theorem nor
a five-sixths theorem follows yet.

## Proof

The generic admissible window supplies wide local hypotheses and complex
strip decay `|φ̂(r−iy)|≤exp(L/4)cDT/|r−iy|²` for `|y|≤1/2`.
Prime partial summation retains the literal lag moment:
`sumA2g=(L³/2)J+O(L²)`. The actual Gram diagonal is
`D≤TL(b ell1²+L²J)/(2π)+O(T l²)`.

Let `N=N(T,2T)`, `F=||hat Gprime||²`, `S=Sλ(T)`, and `δ=δλ`.
Normalize by `(aL)²`, use moment convergence and Riemann–von Mangoldt:
`F≤(2−Hcos(λ)+η)N+S`; the actual prime trace is `N+o(N)`.
The normalized tail is bounded for λ≤2, even though its unnormalized
bound need not tend to zero at λ=2. Perturbing the actual zero-side
pinching certificate gives

`4 tr(hat Gprime)−F−2N+δN−3NII−B(4+2sqrt(F)+B)≤N0simple`

with B fixed. If `(Hcos+δ−ε)N−S≤0`, use `N0simple≥0`.
Otherwise the same retained surplus forces `F≤(3+δ)N` for small η.
The tail loss is then `O(sqrt(N)+1)=o(N)`; the actual local zero count
gives `NII=o(N)`. Absorb these errors. This also proves the endpoint λ=2.

## Lean

- `IncommensurableGaborPinching/CosineWindowAnalyticBridge.lean`: five
  theorems for wide local hypotheses, the literal frozen window, and strip decay.
- `TransThresholdPairCorrelation/CosinePrimeGramCertificate.lean`:
  `sumA2g_cosine_close`, `zetaCosine_diagonal_part_le`,
  `zetaCosine_bounded_tail`, `zetaCosine_prime_rankTrace`.
- `TransThresholdPairCorrelation/CosinePrimeSurplusCriterion.lean`:
  `zetaCosine_frobSq_le`, `zetaCosine_trace_close`,
  `zetaCosine_surplus_certificate`,
  `zetaCosine_fourThirds_surplus_certificate`,
  `zetaCosine_two_surplus_certificate`.

All fourteen public theorem audits use only `propext`, `Classical.choice`,
and `Quot.sound`. All three exact production leaves pass `lake --old env lean`. Umbrella imports are present.

## Remaining

An actual signed upper bound for this same Sλ. At λ=4/3, the sufficient
asymptotic budget is `(79/1250+δ(4/3))N`; at λ=2 it is
`(1/12+43/3750+δ(2))N`. Unsigned factor-two envelopes do not supply either bound.
